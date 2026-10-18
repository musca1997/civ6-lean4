#!/usr/bin/env python3
"""Executable MVP v2 model for the civ6-lean4 rule contract.

This file is an **untrusted candidate generator / semantic executable**, not a
Civ6 fact claim and not a proof.  It implements exactly the step relation in
``mvp/RULE-CONTRACT.md`` and reads its scenario/axis data from
``fixtures/mvp-rule-candidates.json``.  The Lean development is the authority;
this module only freezes a replayable candidate and the observed search data.

Owned by this module:
  * ``search/mvp.py``
  * ``fixtures/mvp-baseline.json``   (written by ``--write-fixture``)
  * ``mvp/EXECUTABLE.md``

Python standard library only.  All state arithmetic is integer 1/100 units; no
Float/Fraction is used.

Important implementation decisions (also documented in ``mvp/EXECUTABLE.md``):

* The *action box* is the literal powerset product
  ``tiles-subsets x extra-option x build`` (capacity-filtered).  A separate
  structural legality filter removes impossible tuples, and ``step`` returns
  ``None`` for the remaining starvation/pre-turn-population failures.  The
  contract's O2 wording ("legal iff in allActions") is therefore implemented as
  ``legal(s,a) := step(s,a).isSome`` over the finite box; both counts are
  reported so a Lean porter can choose either encoding.
* ``prod(extra)`` is totalised to ``0`` for ``extra = none``.  The contract's
  "extra exists by legality" is false; legality permits ``extra = none``.
* ``newCitizen`` is used only by ``growth_first`` (the normative pseudocode
  has no new-citizen term in ``production_first``).
* IDLE credits no settler progress and cannot complete a settler.
* SETTLER legality is judged against the pre-turn population.
* A negative post-modifier surplus makes the action illegal (``step -> none``).

Usage:
    python3 search/mvp.py                  # baseline + cost-110 report
    python3 search/mvp.py --self-test      # test suite (no full 128 search)
    python3 search/mvp.py --guards         # H=27 guard enumeration
    python3 search/mvp.py --all            # all 128 theta (bounded, ~minutes)
    python3 search/mvp.py --write-fixture  # freeze fixtures/mvp-baseline.json
    python3 search/mvp.py --check-fixture  # replay/validate the frozen fixture
"""

from __future__ import annotations

import argparse
import json
import sys
import time
import unittest
from dataclasses import dataclass, field
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Any, Dict, Iterator, List, NamedTuple, Optional, Sequence, Tuple

# ---------------------------------------------------------------------------
# Paths and constants
# ---------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parents[1]
RULE_FIXTURE_PATH = ROOT / "fixtures" / "mvp-rule-candidates.json"
BASELINE_FIXTURE_PATH = ROOT / "fixtures" / "mvp-baseline.json"

TASK_HORIZON_MAX = 27
CONTRACT_HORIZON_MAX = 34
BUILDS: Tuple[str, str] = ("SETTLER", "IDLE")
SCENARIO_ID = "sigma-capital-4tiles-v1"


class ModelError(ValueError):
    """The data or model lies outside the finite MVP contract box."""


class ExactnessError(ModelError):
    """A multiplier did not divide exactly in 1/100 units."""


# ---------------------------------------------------------------------------
# Typed values
# ---------------------------------------------------------------------------


class State(NamedTuple):
    pop: int
    food: int
    prog: int
    trained: int


class Action(NamedTuple):
    #: bit i set <=> tile i is worked
    work: int
    #: tile the new citizen would work, or None.  Never contributes food.
    extra: Optional[int]
    build: str


class Theta(NamedTuple):
    settler_cost: int  # 8000 or 11000 in 1/100 food/production units
    turn_order: str
    new_citizen: str
    amenity_stock: int
    basket_on_growth: str
    production_rounding: str
    threshold_rounding: str


class StepInfo(NamedTuple):
    state: State
    food_yield: int  # F
    prod_base: int  # P before an optional new-citizen tile
    prod_used: int  # P used for q
    surplus: int  # d checked >= 0
    growth: int  # e
    grew: bool
    extra_prod: int
    q_raw: int  # P_used * prodMult (before /100)
    q: int  # after /100 and optional trunc10
    credited: int
    completed: bool
    surplus_pop: int  # population at which d is evaluated


# ---------------------------------------------------------------------------
# Scenario / theta loading and validation
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Scenario:
    tile_ids: Tuple[str, ...]
    tile_food: Tuple[int, ...]
    tile_prod: Tuple[int, ...]
    center_food: int
    palace_prod: int
    base_prod: int
    thresholds: Tuple[int, ...]  # index 1..4 used; index 0 = 0
    t3_floor: int
    t3_exact: int
    cost_by_axis: Dict[int, int]
    horizon: int
    amenity_values: Tuple[int, ...]
    axes: Tuple[str, ...]
    axis_values: Dict[str, Tuple[Any, ...]]
    default_theta: Theta
    raw: Dict[str, Any]


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise ModelError(msg)


def _is_int(x: Any) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


def _theta_from_axis_values(values: Sequence[Any]) -> Theta:
    _require(len(values) == 7, "theta needs 7 axis values")
    cost_axis, order, new_cit, stock, basket, prod_round, thr_round = values
    return Theta(
        settler_cost=int(cost_axis) * 100,
        turn_order=str(order),
        new_citizen=str(new_cit),
        amenity_stock=int(stock),
        basket_on_growth=str(basket),
        production_rounding=str(prod_round),
        threshold_rounding=str(thr_round),
    )


def _theta_to_axis_values(theta: Theta) -> Tuple[Any, ...]:
    return (
        theta.settler_cost // 100,
        theta.turn_order,
        theta.new_citizen,
        theta.amenity_stock,
        theta.basket_on_growth,
        theta.production_rounding,
        theta.threshold_rounding,
    )


def _theta_dict(theta: Theta) -> Dict[str, Any]:
    return dict(zip(("settlerCost", "turnOrder", "newCitizen", "amenityStock",
                     "basketOnGrowth", "productionRounding", "thresholdRounding"),
                    _theta_to_axis_values(theta)))


def load_scenario(path: Path = RULE_FIXTURE_PATH) -> Scenario:
    """Read the actual JSON shape, validate the finite contract box, return data."""
    try:
        data = json.loads(Path(path).read_text(encoding="utf-8"))
    except OSError as exc:  # pragma: no cover - environmental failure
        raise ModelError(f"cannot read rule fixture {path}: {exc}") from exc

    _require(str(data.get("version")) in ("2", "2.1"),
             "rule fixture version must be 2 or 2.1")
    _require(data.get("synthetic") is False, "rule fixture must not be synthetic")
    _require(data.get("civ6Model") is True, "rule fixture must describe the MVP model")
    _require(data.get("gameFactClaim") is False, "rule fixture must not claim a game fact")

    scenario = data.get("scenario")
    _require(isinstance(scenario, dict), "missing scenario")
    _require(scenario.get("id") == SCENARIO_ID, f"scenario id must be {SCENARIO_ID}")

    tiles = scenario.get("tiles")
    _require(isinstance(tiles, list) and len(tiles) == 4, "expected exactly 4 tiles")
    tile_ids: List[str] = []
    tile_food: List[int] = []
    tile_prod: List[int] = []
    for tile in tiles:
        _require(isinstance(tile, dict), "tile must be an object")
        tid = tile.get("id")
        food = tile.get("food")
        prod = tile.get("production")
        _require(isinstance(tid, str) and tid, "tile id must be a nonempty string")
        _require(_is_int(food) and food >= 0, f"tile {tid} food must be a nonnegative int")
        _require(_is_int(prod) and prod >= 0, f"tile {tid} production must be a nonnegative int")
        _require(food % 100 == 0 and prod % 100 == 0,
                 f"tile {tid} yields must be multiples of 100 in 1/100 scale")
        tile_ids.append(tid)
        tile_food.append(food)
        tile_prod.append(prod)
    _require(len(set(tile_ids)) == 4, "tile ids must be unique")
    _require(scenario.get("tileCapacityPerCitizen") == 1, "tile capacity must be 1")

    center = scenario.get("cityCenter")
    palace = scenario.get("palace")
    _require(isinstance(center, dict) and isinstance(palace, dict), "missing centre/palace")
    center_food = center.get("food")
    center_prod = center.get("production")
    palace_prod = palace.get("production")
    _require(_is_int(center_food) and center_food == 200, "city centre food must be 200")
    _require(_is_int(center_prod) and center_prod == 100, "city centre production must be 100")
    _require(_is_int(palace_prod) and palace_prod == 200, "palace production must be 200 (A1)")

    initial = scenario.get("initialState")
    _require(isinstance(initial, dict), "missing initial state")
    _require(initial.get("t") == 0 and initial.get("pop") == 1 and initial.get("food") == 0
             and initial.get("prog") == 0 and initial.get("trained") == 0,
             "initial state must be t=0,pop=1,food=0,prog=0,trained=0")

    scale = data.get("numericScale")
    _require(isinstance(scale, dict), "missing numericScale")
    food_scale = scale.get("food")
    prod_scale = scale.get("production")
    _require(isinstance(food_scale, dict) and isinstance(prod_scale, dict), "missing numeric scales")
    _require(food_scale.get("thresholdPop1") == 1500, "T(1) must be 1500")
    _require(food_scale.get("thresholdPop2") == 2400, "T(2) must be 2400")
    t3 = food_scale.get("thresholdPop3")
    _require(isinstance(t3, dict), "missing T(3) candidates")
    t3_floor = t3.get("floor")
    t3_exact = t3.get("exactComparisonBound")
    _require(_is_int(t3_floor) and t3_floor == 3300, "T(3) floor must be 3300")
    _require(_is_int(t3_exact) and t3_exact == 3383, "T(3) exact bound must be 3383")
    _require(food_scale.get("thresholdPop4") == 4420, "T(4) must be 4420")
    _require(_is_int(prod_scale.get("settlerCost80")) and prod_scale["settlerCost80"] == 8000,
             "cost 80 must be 8000")
    _require(_is_int(prod_scale.get("settlerCost110")) and prod_scale["settlerCost110"] == 11000,
             "cost 110 must be 11000")
    cost_by_axis = {80: 8000, 110: 11000}

    time_model = data.get("timeModel")
    _require(isinstance(time_model, dict), "missing timeModel")
    horizon = time_model.get("horizon")
    _require(_is_int(horizon) and 1 <= horizon <= CONTRACT_HORIZON_MAX,
             f"rule-fixture horizon must be an int in 1..{CONTRACT_HORIZON_MAX}")

    amenity = scenario.get("amenityStock")
    _require(isinstance(amenity, dict), "missing amenityStock")
    amenity_values = tuple(amenity.get("candidateValues") or ())
    _require(amenity_values in ((2, 1), (1, 2)), "amenity candidate values must be {2,1}")

    box = data.get("candidateBox")
    _require(isinstance(box, dict), "missing candidateBox")
    axes = tuple(box.get("axesOrder") or ())
    _require(axes == ("settlerCost", "turnOrder", "newCitizen", "amenityStock",
                      "basketOnGrowth", "productionRounding", "thresholdRounding"),
             "unexpected candidate axis order")
    _require(box.get("size") == 128, "candidateBox.size must be 128")
    candidates = data.get("candidates")
    _require(isinstance(candidates, list) and len(candidates) == 7, "need 7 candidate axes")
    axis_values: Dict[str, Tuple[Any, ...]] = {}
    defaults: Dict[str, Any] = {}
    for cand in candidates:
        axis = cand.get("axis")
        values = cand.get("values")
        _require(axis in axes, f"unknown candidate axis {axis!r}")
        _require(isinstance(values, list) and len(values) >= 2, f"axis {axis} needs values")
        axis_values[axis] = tuple(values)
        defaults[axis] = cand.get("defaultWitness")
    _require(set(axis_values) == set(axes), "candidate axes do not match axesOrder")

    expected_axis_values = {
        "settlerCost": (80, 110),
        "turnOrder": ("growth_first", "production_first"),
        "newCitizen": ("best", "none"),
        "amenityStock": (2, 1),
        "basketOnGrowth": ("zero", "subtract"),
        "productionRounding": ("exact", "trunc10"),
        "thresholdRounding": ("exact", "floor"),
    }
    _require(axis_values == expected_axis_values, "axis values differ from the v2 contract box")

    combos = box.get("combos")
    _require(isinstance(combos, list) and len(combos) == 128, "candidateBox must list 128 combos")
    seen: set[Tuple[Any, ...]] = set()
    for combo in combos:
        _require(isinstance(combo, dict), "combo must be an object")
        vals = tuple(combo.get(a) for a in axes)
        _require(all(vals[i] in axis_values[axes[i]] for i in range(7)),
                 f"combo outside candidate axes: {vals}")
        _require("predictedN" in combo, "combo lacks predictedN (analyst prediction)")
        _require(vals not in seen, f"duplicate combo {vals}")
        seen.add(vals)
    _require(seen == set(product(*(axis_values[a] for a in axes))),
             "candidateBox.combos is not the full product of the axes")

    observed_defaults = tuple(defaults[a] for a in axes)
    baseline = _theta_from_axis_values(observed_defaults)
    pred = data.get("predictions")
    _require(isinstance(pred, dict), "missing predictions (comparison only)")
    reported_baseline = pred.get("baselineTheta")
    if isinstance(reported_baseline, dict):
        for axis in axes:
            expected = _theta_dict(baseline)[axis]
            _require(reported_baseline.get(axis) == expected,
                     f"baselineTheta.{axis} disagrees with defaultWitness")

    thresholds = (0, 1500, 2400, t3_exact, 4420)
    return Scenario(
        tile_ids=tuple(tile_ids),
        tile_food=tuple(tile_food),
        tile_prod=tuple(tile_prod),
        center_food=center_food,
        palace_prod=palace_prod,
        base_prod=center_prod + palace_prod,
        thresholds=thresholds,
        t3_floor=t3_floor,
        t3_exact=t3_exact,
        cost_by_axis=cost_by_axis,
        horizon=horizon,
        amenity_values=amenity_values,
        axes=axes,
        axis_values=axis_values,
        default_theta=baseline,
        raw=data,
    )


SCENARIO = load_scenario()
# The task execution bound is 27; the v2.1 contract moved its horizon bound to
# 34.  This executable obeys the task cap and reports the difference explicitly.
EXECUTION_HORIZON = min(SCENARIO.horizon, TASK_HORIZON_MAX)
N_TILES = len(SCENARIO.tile_ids)


def _build_work_meta(scenario: Scenario) -> Tuple[Tuple[int, int, int], ...]:
    meta: List[Tuple[int, int, int]] = []
    for mask in range(1 << N_TILES):
        idx = [i for i in range(N_TILES) if (mask >> i) & 1]
        meta.append((
            len(idx),
            sum(scenario.tile_food[i] for i in idx),
            sum(scenario.tile_prod[i] for i in idx),
        ))
    return tuple(meta)


WORK_META = _build_work_meta(SCENARIO)
TILE_PROD = SCENARIO.tile_prod
TILE_IDS = SCENARIO.tile_ids
START = State(1, 0, 0, 0)


def validate_theta(theta: Theta) -> None:
    _require(isinstance(theta, Theta), "theta must be a Theta")
    _require(_is_int(theta.settler_cost) and theta.settler_cost in SCENARIO.cost_by_axis.values(),
             f"settler_cost {theta.settler_cost!r} is outside {{8000,11000}}")
    for axis, value in zip(SCENARIO.axes, _theta_to_axis_values(theta)):
        _require(value in SCENARIO.axis_values[axis],
                 f"theta.{axis}={value!r} is outside {SCENARIO.axis_values[axis]!r}")
    # Cross-check the axis cost against the scaled cost.
    _require(theta.settler_cost == SCENARIO.cost_by_axis[int(_theta_to_axis_values(theta)[0])],
             "settler_cost does not match settlerCost axis")


def validate_state(state: State, prepared: Optional["Prepared"] = None) -> None:
    _require(isinstance(state, State), "state must be a State")
    for name, value in zip(State._fields, state):
        _require(_is_int(value), f"state.{name} must be an int")
    _require(1 <= state.pop <= 4, f"state.pop={state.pop} outside MVP threshold table (1..4)")
    _require(state.food >= 0, f"state.food={state.food} is negative")
    _require(state.prog >= 0, f"state.prog={state.prog} is negative")
    _require(state.trained >= 0, f"state.trained={state.trained} is negative")
    if prepared is not None:
        _require(state.prog < prepared.cost,
                 f"non-completing state has prog={state.prog} >= cost={prepared.cost}")


# ---------------------------------------------------------------------------
# Tier and prepared theta
# ---------------------------------------------------------------------------

_GROWTH_MULT = {"happy": 110, "content": 100, "displeased": 85}
_PROD_MULT = {"happy": 105, "content": 100, "displeased": 95}


def tier(theta: Theta, pop: int) -> str:
    """Amenity tier from stock - req(pop); Ecstatic/below-Displeased are outside Θ."""
    _require(pop >= 1, f"population must be >= 1, got {pop}")
    req = max(0, (pop - 1) // 2)
    diff = theta.amenity_stock - req
    if diff >= 3:
        raise ModelError(
            f"Ecstatic tier (stock-req={diff}) is not in the MVP multiplier table; "
            "this state is outside the finite contract box"
        )
    if diff >= 1:
        return "happy"
    if diff == 0:
        return "content"
    if diff >= -2:
        return "displeased"
    raise ModelError(f"tier below Displeased (stock-req={diff}) is outside the MVP table")


def thresholds_for(theta: Theta) -> Tuple[int, ...]:
    t3 = SCENARIO.t3_floor if theta.threshold_rounding == "floor" else SCENARIO.t3_exact
    return (0, 1500, 2400, t3, 4420)


@dataclass(frozen=True)
class Prepared:
    theta: Theta
    cost: int
    order: str
    new_citizen: str
    stock: int
    basket: str
    rounding: str
    T: Tuple[int, ...]
    gm: Tuple[int, ...]  # growth multiplier by pop
    pm: Tuple[int, ...]  # production multiplier by pop


@lru_cache(maxsize=512)
def prepare(theta: Theta) -> Prepared:
    validate_theta(theta)
    T = thresholds_for(theta)
    # Index by population (0 is a dummy) so step can use gm[pop]/pm[pop].
    gm = (0,) + tuple(_GROWTH_MULT[tier(theta, pop)] for pop in range(1, 5))
    pm = (0,) + tuple(_PROD_MULT[tier(theta, pop)] for pop in range(1, 5))
    return Prepared(
        theta=theta,
        cost=theta.settler_cost,
        order=theta.turn_order,
        new_citizen=theta.new_citizen,
        stock=theta.amenity_stock,
        basket=theta.basket_on_growth,
        rounding=theta.production_rounding,
        T=T,
        gm=gm,
        pm=pm,
    )


def _div100(num: int, what: str) -> int:
    if num % 100 != 0:
        raise ExactnessError(
            f"{what}: numerator {num} is not divisible by 100 in 1/100 units"
        )
    return num // 100


# ---------------------------------------------------------------------------
# Finite action box, capacity, structural legality
# ---------------------------------------------------------------------------


def _popcount(mask: int) -> int:
    return mask.bit_count()


def action_box(pop: int) -> Tuple[Action, ...]:
    """Literal finite powerset product (capacity-filtered), including illegal tuples."""
    _require(pop >= 1, "population must be >= 1")
    out: List[Action] = []
    for mask in range(1 << N_TILES):
        if _popcount(mask) > pop:
            continue
        for extra in (None,) + tuple(range(N_TILES)):
            for build in BUILDS:
                out.append(Action(mask, extra, build))
    return tuple(out)


def structurally_legal(pop: int, action: Action) -> bool:
    """Static part of §3: capacity, no shared tile, IDLE/no-extra, pre-turn pop."""
    if action.work < 0 or action.work >= (1 << N_TILES):
        return False
    size = WORK_META[action.work][0]
    if size > pop:
        return False
    if action.extra is not None:
        if not (0 <= action.extra < N_TILES):
            return False
        if (action.work >> action.extra) & 1:
            return False
    if action.build not in BUILDS:
        return False
    if action.build == "IDLE" and action.extra is not None:
        return False
    if action.build == "SETTLER" and pop < 2:
        return False
    return True


@lru_cache(maxsize=16)
def structural_actions(pop: int) -> Tuple[Action, ...]:
    return tuple(a for a in action_box(pop) if structurally_legal(pop, a))


@lru_cache(maxsize=16)
def idle_free_actions(pop: int) -> Tuple[Action, ...]:
    # O5's "idle-free" means no citizen without a tile (|work| = pop), not build != IDLE.
    return tuple(a for a in structural_actions(pop) if WORK_META[a.work][0] == pop)


# ---------------------------------------------------------------------------
# The normative step
# ---------------------------------------------------------------------------


def _step_prepared(
    p: Prepared,
    state: State,
    action: Action,
    trace: bool = False,
    *,
    credit_idle: bool = False,
    allow_starving: bool = False,
) -> Optional[State] | Tuple[State, StepInfo]:
    """One exact settlement step.  ``None`` means the action is illegal.

    ``credit_idle`` and ``allow_starving`` exist only for negative tests; the
    public model never sets them.
    """
    pop, food, prog, trained = state
    work = action.work
    size, food_sum, prod_sum = WORK_META[work]

    # --- structural legality -------------------------------------------------
    if size > pop:
        return None
    if action.extra is not None:
        if not (0 <= action.extra < N_TILES):
            return None
        if (work >> action.extra) & 1:
            return None
    if action.build not in BUILDS:
        return None
    if action.build == "IDLE" and action.extra is not None:
        return None
    if action.build == "SETTLER" and pop < 2:
        return None

    F = SCENARIO.center_food + food_sum
    P_base = SCENARIO.base_prod + prod_sum
    T = p.T
    cost = p.cost

    if p.order == "growth_first":
        d = F - 200 * pop
        if d < 0 and not allow_starving:
            return None
        e = _div100(d * p.gm[pop], "growth e (growth_first)")
        food1 = food + e
        pop1 = pop
        grew = False
        if food1 >= T[pop1]:
            grew = True
            food1 = 0 if p.basket == "zero" else food1 - T[pop1]
            pop1 = pop + 1
            if pop1 > 4:
                raise ModelError(f"population {pop1} exceeds threshold table (G1)")
        P_used = P_base
        extra_prod = 0
        if grew and p.new_citizen == "best" and action.extra is not None:
            extra_prod = TILE_PROD[action.extra]
            P_used += extra_prod
        q_raw = P_used * p.pm[pop1]
        q = _div100(q_raw, "production q (growth_first)")
        if p.rounding == "trunc10":
            q = (q // 10) * 10
        credited = q if (action.build == "SETTLER" or credit_idle) else 0
        prog1 = prog + credited
        completed = action.build == "SETTLER" and prog1 >= cost
        if completed:
            post = State(pop1 - 1, food1, prog1 - cost, trained + 1)
        else:
            post = State(pop1, food1, prog1, trained)
        if trace:
            return post, StepInfo(post, F, P_base, P_used, d, e, grew, extra_prod,
                                  q_raw, q, credited, completed, pop)
        return post

    if p.order == "production_first":
        q_raw = P_base * p.pm[pop]
        q = _div100(q_raw, "production q (production_first)")
        if p.rounding == "trunc10":
            q = (q // 10) * 10
        credited = q if (action.build == "SETTLER" or credit_idle) else 0
        prog1 = prog + credited
        completed = action.build == "SETTLER" and prog1 >= cost
        pop1 = pop - 1 if completed else pop
        prog1 = prog1 - cost if completed else prog1
        if pop1 < 1:
            raise ModelError("completion reduced population below 1")
        d = F - 200 * pop1
        if d < 0 and not allow_starving:
            return None
        e = _div100(d * p.gm[pop1], "growth e (production_first)")
        food1 = food + e
        pop2 = pop1
        grew = False
        if food1 >= T[pop1]:
            grew = True
            food1 = 0 if p.basket == "zero" else food1 - T[pop1]
            pop2 = pop1 + 1
            if pop2 > 4:
                raise ModelError(f"population {pop2} exceeds threshold table (G1)")
        post = State(pop2, food1, prog1, trained + (1 if completed else 0))
        if trace:
            return post, StepInfo(post, F, P_base, P_base, d, e, grew, 0,
                                  q_raw, q, credited, completed, pop1)
        return post

    raise ModelError(f"unknown turn_order {p.order!r}")


def step(theta: Theta, state: State, action: Action) -> Optional[State]:
    """Public exact step: ``None`` iff the action is illegal."""
    return _step_prepared(prepare(theta), state, action)  # type: ignore[return-value]


def explain_step(theta: Theta, state: State, action: Action) -> Optional[StepInfo]:
    """Diagnostic wrapper used for witnesses; agrees with :func:`step`."""
    out = _step_prepared(prepare(theta), state, action, trace=True)
    if out is None:
        return None
    return out[1]  # type: ignore[index]


def legal(theta: Theta, state: State, action: Action) -> bool:
    return step(theta, state, action) is not None


def successors(theta: Theta, state: State) -> Tuple[State, ...]:
    out: List[State] = []
    for action in structural_actions(state.pop):
        nxt = step(theta, state, action)
        if nxt is not None:
            out.append(nxt)
    return tuple(out)


def goal(state: State) -> bool:
    return state.trained >= 1


# ---------------------------------------------------------------------------
# Exact-step frontier search
# ---------------------------------------------------------------------------


@dataclass
class SearchStats:
    max_pop: int = 1
    max_food_by_pop: List[int] = field(default_factory=lambda: [0, 0, 0, 0, 0])
    max_prog: int = 0
    max_trained: int = 0
    max_layer_size: int = 1
    states_visited: int = 1
    pop4_seen: bool = False
    t3_food_seen: int = 0  # max food seen at pop 3 (for "T(3) never crossed")

    def observe(self, s: State) -> None:
        if s.pop > self.max_pop:
            self.max_pop = s.pop
        if s.pop <= 4 and s.food > self.max_food_by_pop[s.pop]:
            self.max_food_by_pop[s.pop] = s.food
        if s.prog > self.max_prog:
            self.max_prog = s.prog
        if s.trained > self.max_trained:
            self.max_trained = s.trained
        if s.pop == 4:
            self.pop4_seen = True
        if s.pop == 3 and s.food > self.t3_food_seen:
            self.t3_food_seen = s.food

    def as_dict(self, prepared: Optional[Prepared] = None) -> Dict[str, Any]:
        d: Dict[str, Any] = {
            "maxPop": self.max_pop,
            "maxFoodPop1": self.max_food_by_pop[1],
            "maxFoodPop2": self.max_food_by_pop[2],
            "maxFoodPop3": self.max_food_by_pop[3],
            "maxFoodPop4": self.max_food_by_pop[4],
            "maxProg": self.max_prog,
            "maxTrained": self.max_trained,
            "maxLayerSize": self.max_layer_size,
            "statesVisited": self.states_visited,
            "pop4Seen": self.pop4_seen,
        }
        if prepared is not None:
            d["T3"] = prepared.T[3]
            d["t3Crossed"] = self.t3_food_seen >= prepared.T[3]
            d["housingLeftAtMaxPop"] = 6 - self.max_pop
        return d


@dataclass
class SearchResult:
    theta: Theta
    n: Optional[int]
    goal_state: Optional[State]
    layer_sizes: List[int]
    stats: SearchStats
    layers: Optional[List[set[State]]] = None
    parents: Optional[List[Dict[State, Tuple[State, Action]]]] = None

    def as_dict(self) -> Dict[str, Any]:
        return {
            "theta": _theta_dict(self.theta),
            "n": self.n,
            "goalState": list(self.goal_state) if self.goal_state is not None else None,
            "layerSizes": self.layer_sizes,
            "stats": self.stats.as_dict(prepare(self.theta)),
        }


def frontier_search(
    theta: Theta,
    horizon: Optional[int] = None,
    *,
    stop_on_goal: bool = True,
    exclude_goal: bool = False,
    idle_free: bool = False,
    keep_frontiers: bool = False,
    validate: bool = False,
) -> SearchResult:
    """Exact-step layers ``reach 0 = {s0}``, dedup inside a layer only.

    ``stop_on_goal`` reproduces the minimality search.  ``exclude_goal`` is used
    for the no-goal guard scan: goal successors are not even added.  With
    ``stop_on_goal=False`` the scan continues to the horizon (goal states are
    expanded unless excluded).
    """
    p = prepare(theta)
    h = EXECUTION_HORIZON if horizon is None else int(horizon)
    _require(1 <= h <= TASK_HORIZON_MAX,
             f"execution horizon must be in 1..{TASK_HORIZON_MAX}, got {h}")

    layer: set[State] = {START}
    layers: Optional[List[set[State]]] = [set(layer)] if keep_frontiers else None
    parents: Optional[List[Dict[State, Tuple[State, Action]]]] = None
    if keep_frontiers:
        parents = [{START: None}]  # type: ignore[list-item]
    sizes: List[int] = [1]
    stats = SearchStats()
    stats.observe(START)
    n: Optional[int] = None
    goal_state: Optional[State] = None
    actions_for_pop = idle_free_actions if idle_free else structural_actions

    for t in range(h):
        nxt: set[State] = set()
        par: Dict[State, Tuple[State, Action]] = {}
        iterable = sorted(layer) if keep_frontiers else layer
        for s in iterable:
            for action in actions_for_pop(s.pop):
                nxt_state = _step_prepared(p, s, action)
                if nxt_state is None:
                    continue
                if exclude_goal and goal(nxt_state):
                    continue
                if validate:
                    validate_state(nxt_state, p)
                nxt.add(nxt_state)
                stats.observe(nxt_state)
                if keep_frontiers and nxt_state not in par:
                    par[nxt_state] = (s, action)
        sizes.append(len(nxt))
        if len(nxt) > stats.max_layer_size:
            stats.max_layer_size = len(nxt)
        stats.states_visited += len(nxt)
        if keep_frontiers:
            assert layers is not None and parents is not None
            layers.append(nxt)
            parents.append(par)
        goals = sorted(s for s in nxt if goal(s))
        if goals and not exclude_goal:
            if n is None:
                n = t + 1
                goal_state = goals[0]
            if stop_on_goal:
                layer = nxt
                break
        layer = nxt
        if not layer:
            break

    return SearchResult(theta, n, goal_state, sizes, stats,
                        layers if keep_frontiers else None,
                        parents if keep_frontiers else None)


def reconstruct_path(result: SearchResult, target: Optional[State] = None) -> List[Tuple[int, State, Action, State]]:
    """Return rows (t, pre, action, post) of a canonical witness."""
    if result.n is None:
        raise ModelError("cannot reconstruct: no goal within horizon")
    if result.parents is None:
        raise ModelError("cannot reconstruct without keep_frontiers=True")
    cur = target if target is not None else result.goal_state
    if cur is None:
        raise ModelError("cannot reconstruct: no goal state")
    rows: List[Tuple[int, State, Action, State]] = []
    for t in range(result.n, 0, -1):
        prev, action = result.parents[t][cur]
        rows.append((t, prev, action, cur))
        cur = prev
    if cur != START:
        raise ModelError(f"parent chain does not end at start (ended at {cur})")
    rows.reverse()
    return rows


# ---------------------------------------------------------------------------
# Witness construction/verification
# ---------------------------------------------------------------------------


def _action_ids(action: Action) -> Dict[str, Any]:
    return {
        "work": [TILE_IDS[i] for i in range(N_TILES) if (action.work >> i) & 1],
        "workMask": action.work,
        "extra": TILE_IDS[action.extra] if action.extra is not None else None,
        "build": action.build,
    }


def witness_rows(theta: Theta, path: Sequence[Tuple[int, State, Action, State]]) -> List[Dict[str, Any]]:
    p = prepare(theta)
    rows: List[Dict[str, Any]] = []
    for t, pre, action, post in path:
        info = explain_step(theta, pre, action)
        if info is None:  # pragma: no cover - caller checks
            raise ModelError(f"witness action at t={t} is not legal")
        if info.state != post:  # pragma: no cover - consistency check
            raise ModelError(f"explain_step disagrees with step at t={t}")
        row = {
            "t": t,
            "pre": list(pre),
            "action": _action_ids(action),
            "F": info.food_yield,
            "P": info.prod_used,
            "d": info.surplus,
            "e": info.growth,
            "grew": info.grew,
            "q": info.q,
            "credited": info.credited,
            "completed": info.completed,
            "extraProd": info.extra_prod,
            "post": list(post),
        }
        rows.append(row)
    return rows


def verify_witness(theta: Theta, rows: Sequence[Dict[str, Any]], n: int) -> Dict[str, Any]:
    """Replay a witness and check O5-style properties.  Returns a check report."""
    if len(rows) != n:
        raise ModelError(f"witness length {len(rows)} != N={n}")
    cur = START
    prog_zero_before_pop2 = True
    idle_free = True
    nonnegative = True
    no_goal_before = True
    setter_preturn = True
    for i, row in enumerate(rows):
        action = Action(row["action"]["workMask"], _tile_index(row["action"]["extra"]), row["action"]["build"])
        if tuple(row["pre"]) != cur:
            raise ModelError(f"row {i+1}: pre-state {row['pre']} != replay state {list(cur)}")
        if cur.pop < 2 and cur.prog != 0:
            prog_zero_before_pop2 = False
        if WORK_META[action.work][0] != cur.pop:
            idle_free = False
        if action.build == "SETTLER" and cur.pop < 2:
            setter_preturn = False
        nxt = step(theta, cur, action)
        if nxt is None:
            raise ModelError(f"row {i+1}: witness action is illegal")
        if tuple(row["post"]) != nxt:
            raise ModelError(f"row {i+1}: post-state {row['post']} != step {list(nxt)}")
        if row["d"] < 0:
            nonnegative = False
        if i < n - 1 and nxt.trained >= 1:
            no_goal_before = False
        cur = nxt
    if not goal(cur):
        raise ModelError("witness final state is not a goal")
    return {
        "length": n,
        "finalState": list(cur),
        "goal": goal(cur),
        "idleFree": idle_free,
        "progZeroBeforePop2": prog_zero_before_pop2,
        "nonnegativeSurplus": nonnegative,
        "noGoalBeforeN": no_goal_before,
        "settlerPreturnLegal": setter_preturn,
    }


def _tile_index(tid: Optional[str]) -> Optional[int]:
    if tid is None:
        return None
    try:
        return TILE_IDS.index(tid)
    except ValueError as exc:
        raise ModelError(f"unknown tile id {tid!r}") from exc


def find_witness(theta: Theta, n: int) -> Tuple[List[Tuple[int, State, Action, State]], Dict[str, Any]]:
    """Find an idle-free witness of length exactly n; fall back to full search."""
    restricted = frontier_search(theta, horizon=n, stop_on_goal=True, idle_free=True,
                                 keep_frontiers=True, validate=True)
    if restricted.n == n:
        path = reconstruct_path(restricted)
    elif restricted.n is not None and restricted.n < n:
        raise ModelError(f"idle-free search found goal at {restricted.n} < full N={n}")
    else:
        full = frontier_search(theta, horizon=n, stop_on_goal=True, idle_free=False,
                               keep_frontiers=True, validate=True)
        if full.n != n:
            raise ModelError(f"full search did not reproduce N={n} (got {full.n})")
        path = reconstruct_path(full)
    rows = witness_rows(theta, path)
    checks = verify_witness(theta, rows, n)
    if not checks["idleFree"]:
        raise ModelError("canonical witness is not idle-free")
    return path, checks


def contract_style_path(theta: Theta, limit: int = EXECUTION_HORIZON) -> List[Tuple[int, State, Action, State]]:
    """Replay the §10-style witness GH x7 (IDLE), then GH+PH (SETTLER) until goal."""
    cur = START
    rows: List[Tuple[int, State, Action, State]] = []
    for t in range(1, limit + 1):
        if cur.pop == 1:
            action = Action(1 << TILE_IDS.index("GH"), None, "IDLE")
        else:
            action = Action((1 << TILE_IDS.index("GH")) | (1 << TILE_IDS.index("PH")), None, "SETTLER")
        nxt = step(theta, cur, action)
        if nxt is None:
            raise ModelError(f"contract-style witness illegal at t={t} state={cur}")
        rows.append((t, cur, action, nxt))
        cur = nxt
        if goal(cur):
            return rows
    raise ModelError("contract-style witness did not reach goal within limit")


# ---------------------------------------------------------------------------
# Reports and all-theta enumeration
# ---------------------------------------------------------------------------


def baseline_theta() -> Theta:
    return SCENARIO.default_theta


def cost110_theta() -> Theta:
    return baseline_theta()._replace(settler_cost=11000)


def guard_report(theta: Theta, horizon: Optional[int] = None) -> Dict[str, Any]:
    h = EXECUTION_HORIZON if horizon is None else horizon
    all_reach = frontier_search(theta, horizon=h, stop_on_goal=False,
                                exclude_goal=False, keep_frontiers=False, validate=True)
    no_goal = frontier_search(theta, horizon=h, stop_on_goal=False,
                              exclude_goal=True, keep_frontiers=False, validate=True)
    return {
        "theta": _theta_dict(theta),
        "horizon": h,
        "allReachable": {
            "layerSizes": all_reach.layer_sizes,
            "firstGoal": all_reach.n,
            "stats": all_reach.stats.as_dict(prepare(theta)),
        },
        "noGoal": {
            "layerSizes": no_goal.layer_sizes,
            "stats": no_goal.stats.as_dict(prepare(theta)),
        },
    }


def enumerate_thetas() -> Iterator[Theta]:
    for vals in product(*(SCENARIO.axis_values[a] for a in SCENARIO.axes)):
        yield _theta_from_axis_values(vals)


def all_theta_search(horizon: Optional[int] = None, verbose: bool = False) -> Dict[str, Any]:
    h = EXECUTION_HORIZON if horizon is None else horizon
    axes = SCENARIO.axes
    results: List[Dict[str, Any]] = []
    t0 = time.time()
    max_pop = 1
    max_f2 = 0
    max_f3 = 0
    max_layer = 1
    max_trained = 0
    unreached: List[Dict[str, Any]] = []
    for i, theta in enumerate(enumerate_thetas(), start=1):
        res = frontier_search(theta, horizon=h, stop_on_goal=True,
                              exclude_goal=False, keep_frontiers=False, validate=False)
        st = res.stats
        max_pop = max(max_pop, st.max_pop)
        max_f2 = max(max_f2, st.max_food_by_pop[2])
        max_f3 = max(max_f3, st.max_food_by_pop[3])
        max_layer = max(max_layer, st.max_layer_size)
        max_trained = max(max_trained, st.max_trained)
        row = {
            "theta": _theta_to_axis_values(theta),
            "n": res.n,
            "goalState": list(res.goal_state) if res.goal_state else None,
            "layerSizes": res.layer_sizes,
            "maxPop": st.max_pop,
            "maxFoodPop2": st.max_food_by_pop[2],
            "maxFoodPop3": st.max_food_by_pop[3],
            "maxLayerSize": st.max_layer_size,
            "statesVisited": st.states_visited,
        }
        results.append(row)
        if res.n is None:
            unreached.append(row)
        if verbose and (i % 16 == 0 or i == 128):
            print(f"  all-theta: {i}/128  elapsed {time.time()-t0:.1f}s", file=sys.stderr)
    elapsed = time.time() - t0

    # Marginals, strict inertness and envelope.
    per_axis: Dict[str, Dict[str, List[int]]] = {}
    for idx, axis in enumerate(axes):
        m: Dict[str, set[int]] = {}
        for row in results:
            if row["n"] is None:
                continue
            m.setdefault(str(row["theta"][idx]), set()).add(int(row["n"]))
        per_axis[axis] = {k: sorted(v) for k, v in m.items()}

    inert: List[str] = []
    for idx, axis in enumerate(axes):
        groups: Dict[Tuple[Any, ...], set[Optional[int]]] = {}
        for row in results:
            key = tuple(v for j, v in enumerate(row["theta"]) if j != idx)
            groups.setdefault(key, set()).add(row["n"])
        if all(len(v) == 1 for v in groups.values()):
            inert.append(axis)

    ns = [int(row["n"]) for row in results if row["n"] is not None]
    envelope = [min(ns), max(ns)] if ns else None
    distinct = sorted(set(ns))
    argmin = [row["theta"] for row in results if row["n"] == envelope[0]] if envelope else []
    argmax = [row["theta"] for row in results if row["n"] == envelope[1]] if envelope else []

    # Compare to the analyst predictions without using them as results.
    source = SCENARIO.raw
    combos = source["candidateBox"]["combos"]
    pred_map = {tuple(c[a] for a in axes): c["predictedN"] for c in combos}
    mismatches = []
    for row in results:
        key = tuple(row["theta"])
        actual = row["n"]
        predicted = pred_map.get(key)
        if actual != predicted:
            mismatches.append({"theta": list(key), "actualN": actual, "predictedN": predicted})
    preds = source.get("predictions", {})
    pred_env = preds.get("interval", preds.get("envelope", {}))
    pred_marg = source.get("predictions", {}).get("perAxisMarginal", {})
    pred_inert = source.get("predictions", {}).get("predictedInertAxes", [])
    marginal_mismatch = []
    for axis in axes:
        expected = {str(k): sorted(v) for k, v in (pred_marg.get(axis) or {}).items()}
        if per_axis[axis] != expected:
            marginal_mismatch.append({"axis": axis, "actual": per_axis[axis], "predicted": expected})
    prediction_comparison = {
        "checkedCombos": len(results),
        "mismatches": mismatches,
        "envelopeMatch": (envelope == [pred_env.get("min"), pred_env.get("max")]),
        "perAxisMarginalMismatches": marginal_mismatch,
        "inertAxesMatch": inert == list(pred_inert),
        "actualInertAxes": inert,
        "predictedInertAxes": list(pred_inert),
        "note": "analyst predictedN is used only for comparison; results above come from this executable.",
    }

    return {
        "horizon": h,
        "count": len(results),
        "elapsedSeconds": round(elapsed, 3),
        "thetaOrder": list(axes),
        "results": [
            {
                "theta": list(row["theta"]),
                "n": row["n"],
                "goalState": row["goalState"],
                "maxPop": row["maxPop"],
                "maxFoodPop2": row["maxFoodPop2"],
                "maxFoodPop3": row["maxFoodPop3"],
                "maxLayerSize": row["maxLayerSize"],
            }
            for row in results
        ],
        "envelope": {
            "min": envelope[0] if envelope else None,
            "max": envelope[1] if envelope else None,
            "distinctValues": distinct,
            "label": "untrusted search estimate, not certified",
        },
        "perAxisMarginal": per_axis,
        "inertAxes": inert,
        "argminThetas": [list(x) for x in argmin],
        "argmaxThetas": [list(x) for x in argmax],
        "unreached": [row["theta"] for row in unreached],
        "prefixExtrema": {
            "maxPop": max_pop,
            "maxFoodPop2": max_f2,
            "maxFoodPop3": max_f3,
            "maxLayerSize": max_layer,
            "maxTrained": max_trained,
            "note": "extrema over states up to the first goal layer for each theta",
        },
        "predictionComparison": prediction_comparison,
    }


def _observed_action_counts() -> Dict[str, Any]:
    counts = {}
    for pop in (1, 2, 3):
        box = action_box(pop)
        struct = structural_actions(pop)
        idlefree = idle_free_actions(pop)
        counts[str(pop)] = {
            "fullProduct": (1 << N_TILES) * (1 + N_TILES) * len(BUILDS),
            "box": len(box),
            "structuralLegal": len(struct),
            "idleFreeStructural": len(idlefree),
        }
    return counts


def _q_at_pop1_gh(theta: Theta) -> int:
    action = Action(1 << TILE_IDS.index("GH"), None, "IDLE")
    info = explain_step(theta, START, action)
    assert info is not None
    return info.q


def _max_rss_kb() -> Optional[int]:
    try:
        import resource
        return int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    except Exception:  # pragma: no cover - non-POSIX fallback
        return None


def build_fixture_report(run_all: bool = True, verbose: bool = True) -> Dict[str, Any]:
    report_t0 = time.time()
    b = baseline_theta()
    c110 = cost110_theta()

    t0 = time.time()
    base_res = frontier_search(b, horizon=EXECUTION_HORIZON, stop_on_goal=True,
                               keep_frontiers=True, validate=True)
    if base_res.n is None:
        raise ModelError("baseline did not reach the goal within the horizon")
    base_path, base_checks = find_witness(b, base_res.n)
    _require(base_checks["idleFree"], "baseline witness is not idle-free")
    base_rows = witness_rows(b, base_path)
    base_goal = base_path[-1][3]
    base_time = time.time() - t0

    t0 = time.time()
    c110_res = frontier_search(c110, horizon=EXECUTION_HORIZON, stop_on_goal=True,
                               keep_frontiers=True, validate=True)
    if c110_res.n is None:
        raise ModelError("cost-110 counterpart did not reach the goal within the horizon")
    c110_path, c110_checks = find_witness(c110, c110_res.n)
    _require(c110_checks["idleFree"], "cost-110 witness is not idle-free")
    c110_rows = witness_rows(c110, c110_path)
    c110_goal = c110_path[-1][3]
    c110_time = time.time() - t0

    t0 = time.time()
    guards_b = guard_report(b)
    guards_c = guard_report(c110)
    guard_variants: Dict[str, Any] = {}
    for cost_axis in (80, 110):
        for basket in ("zero", "subtract"):
            th = b._replace(settler_cost=cost_axis * 100, basket_on_growth=basket)
            guard_variants[f"cost{cost_axis}_{basket}"] = guard_report(th)["allReachable"]
    guard_time = time.time() - t0

    # Replay the contract-style witness for comparison.
    contract_path = contract_style_path(b)
    contract_rows = witness_rows(b, contract_path)
    contract_checks = verify_witness(b, contract_rows, len(contract_rows))
    contract_n = len(contract_rows)

    all_result = None
    if run_all:
        if verbose:
            print("running all 128 theta (bounded exact-step search)...", file=sys.stderr)
        t0 = time.time()
        all_result = all_theta_search(verbose=verbose)

    # Observed-vs-analyst notes.  The executable's own results are never
    # adjusted to match the fixture.
    discrepancies: List[Dict[str, Any]] = []
    q_gh = _q_at_pop1_gh(b)
    selfcheck = (SCENARIO.raw.get("predictions", {}).get("selfCheckTrace") or [{}])[0]
    fixture_q = selfcheck.get("q", selfcheck.get("qComputed"))
    if fixture_q is not None and fixture_q != q_gh:
        discrepancies.append({
            "id": "D-Q",
            "where": "predictions.selfCheckTrace[0].q / RULE-CONTRACT.md §10",
            "fixtureValue": fixture_q,
            "executableValue": q_gh,
            "explanation": (
                "At pop 1 with work=GH, F=400, P=300+100=400 and the happy production "
                "multiplier 105, q = 400*105/100 = 420.  The value is discarded under "
                "IDLE, so N is unchanged."
            ),
            "effectOnN": "none (IDLE credits 0)",
        })

    # Guard variants named by the analyst scale block (cost x basket).
    guard_variant_stats = {
        key: gv["stats"] for key, gv in guard_variants.items()
    }
    scale = SCENARIO.raw.get("predictions", {}).get("scale", {})
    gb_all = guards_b["allReachable"]
    observed_scale = {
        "maxLayerObserved": gb_all["stats"]["maxLayerSize"],
        "maxPop": gb_all["stats"]["maxPop"],
    }
    if isinstance(scale, dict):
        for key, observed in observed_scale.items():
            if key in scale and isinstance(scale[key], int) and scale[key] != observed:
                discrepancies.append({
                    "id": f"D-SCALE-{key}",
                    "where": f"predictions.scale.{key}",
                    "fixtureValue": scale[key],
                    "executableValue": observed,
                    "explanation": (
                        "Executable observation on baseline theta with the task-capped "
                        "H=27 and all goal states expanded.  The fixture value is an "
                        "analyst 128-combo/H=34 measurement (not certified), so the two "
                        "numbers are not the same experiment; no semantic adjustment is made."
                        + (f" All-128 goal-prefix max layer observed here: "
                           f"{all_result['prefixExtrema']['maxLayerSize']}."
                           if all_result is not None else "")
                    ),
                    "effectOnN": "none (guard statistic)",
                })
        mf3 = scale.get("maxFoodPop3")
        if isinstance(mf3, dict) and isinstance(mf3.get("analystMeasured"), dict):
            analyst = mf3["analystMeasured"]
            ours = {
                "cost80": {
                    "zero": guard_variant_stats["cost80_zero"]["maxFoodPop3"],
                    "subtract": guard_variant_stats["cost80_subtract"]["maxFoodPop3"],
                },
                "cost110": {
                    "zero": guard_variant_stats["cost110_zero"]["maxFoodPop3"],
                    "subtract": guard_variant_stats["cost110_subtract"]["maxFoodPop3"],
                },
            }
            if analyst != ours:
                discrepancies.append({
                    "id": "D-SCALE-maxFoodPop3",
                    "where": "predictions.scale.maxFoodPop3.analystMeasured",
                    "fixtureValue": analyst,
                    "executableValue": ours,
                    "explanation": (
                        "Independent H=27 all-reachable enumeration for the four cost x "
                        "basket combinations.  The analyst block is explicitly labelled "
                        "'per-combo measurements are O8-owned' and not certified; the values "
                        "differ, so O8 must own the re-derived maxima.  No semantics changed."
                    ),
                    "effectOnN": "none (guard statistic)",
                })

    # Fixture table vs the contract formula for req(pop).  Pop 4 is unreachable
    # under the guards, so this is a parameter-consistency note with no N effect.
    rules = {r.get("id"): r for r in SCENARIO.raw.get("rules", []) if isinstance(r, dict)}
    amen = rules.get("R-AMEN-3", {}).get("value", {})
    if isinstance(amen, dict):
        formula_p4 = max(0, (4 - 1) // 2)
        if amen.get("p4") != formula_p4:
            discrepancies.append({
                "id": "D-AMEN-P4",
                "where": "rules.R-AMEN-3.value.p4 vs contract §4 req(p)=max(0,floor((p-1)/2))",
                "fixtureValue": amen.get("p4"),
                "executableValue": formula_p4,
                "explanation": (
                    "The executable follows the normative §4 formula.  Pop 4 is never "
                    "reached (G1), so the p4 table entry cannot change any N or guard "
                    "used here; recorded explicitly rather than silently repaired."
                ),
                "effectOnN": "none (pop 4 unreachable)",
            })

    limitations: List[Dict[str, Any]] = [
        {
            "id": "L-HORIZON",
            "where": "timeModel.horizon / contract §0",
            "contractValue": SCENARIO.horizon,
            "executionValue": EXECUTION_HORIZON,
            "explanation": (
                "The task caps this executable's horizon at <=27 (h<=27).  The current v2.1 "
                "contract/fixture uses H=34 and an O6b horizonOk obligation.  Baseline/cost-110 "
                "N=20/25 and every one of the 128 theta minima are below 27, so minimality "
                "searches are unaffected; the H=34 guard/sensitivity envelope is NOT checked here."
            ),
        },
        {
            "id": "L-ALLACTIONS",
            "where": "contract §3/O2 vs O2b",
            "explanation": (
                "The contract writes both 'legal s a <-> a in allActions s' (O2) and "
                "'legal := step.isSome' (O2b).  This executable exposes the literal powerset "
                "box (pop1/2/3: 50/110/150), the structural filter (5/50/62), and the "
                "step-viable set.  A Lean porter can take allActions := structural box and "
                "legal := step.isSome; starving tuples in that box then have step=none."
            ),
        },
        {
            "id": "L-EXTRA",
            "where": "contract §4 extraGain",
            "explanation": (
                "prod(extra) is totalised to 0 when extra=none (v2.1 extraGain).  Legality "
                "allows extra=none, so the old 'extra exists by legality' justification is "
                "not used."
            ),
        },
    ]

    all_summary = None
    if all_result is not None:
        all_summary = {
            "count": all_result["count"],
            "horizon": all_result["horizon"],
            "elapsedSeconds": all_result["elapsedSeconds"],
            "envelope": all_result["envelope"],
            "perAxisMarginal": all_result["perAxisMarginal"],
            "inertAxes": all_result["inertAxes"],
            "argminThetas": all_result["argminThetas"],
            "argmaxThetas": all_result["argmaxThetas"],
            "unreached": all_result["unreached"],
            "prefixExtrema": all_result["prefixExtrema"],
            "predictionComparison": all_result["predictionComparison"],
            "results": all_result["results"],
        }

    report: Dict[str, Any] = {
        "fixtureId": "mvp-baseline-v1",
        "version": 1,
        "kind": "mvp-executable-baseline",
        "untrusted": True,
        "gameFactClaim": False,
        "contractPath": "mvp/RULE-CONTRACT.md",
        "ruleFixturePath": "fixtures/mvp-rule-candidates.json",
        "ruleFixtureVersion": SCENARIO.raw.get("version"),
        "semantics": {
            "name": "M_MVP v2.1 corrected executable",
            "exactStepLayers": True,
            "settlerProgress": "credited only when build=SETTLER; IDLE accrues nothing",
            "settlerLegality": "pre-turn population >= 2",
            "starvation": "post-modifier surplus < 0 is not an action",
            "extra": "production only on a growth event under growth_first/newCitizen=best; never food",
            "newCitizenUnderProductionFirst": "unused (normative pseudocode has no term)",
            "arithmetic": "integer 1/100 units; no floats",
        },
        "scenario": {
            "id": SCENARIO_ID,
            "tileIds": list(TILE_IDS),
            "tileFood": list(SCENARIO.tile_food),
            "tileProduction": list(SCENARIO.tile_prod),
            "centerFood": SCENARIO.center_food,
            "baseProduction": SCENARIO.base_prod,
            "thresholds": {"1": 1500, "2": 2400, "3Floor": SCENARIO.t3_floor,
                           "3Exact": SCENARIO.t3_exact, "4": 4420},
            "housing": 6,
            "initialState": list(START),
            "goal": "trained >= 1",
        },
        "thetaAxes": list(SCENARIO.axes),
        "actionCounts": _observed_action_counts(),
        "baseline": {
            "theta": _theta_dict(b),
            "n": base_res.n,
            "goalState": list(base_goal),
            "layerSizes": base_res.layer_sizes,
            "stats": base_res.stats.as_dict(prepare(b)),
            "witness": base_rows,
            "witnessChecks": base_checks,
            "elapsedSeconds": round(base_time, 3),
        },
        "cost110": {
            "theta": _theta_dict(c110),
            "n": c110_res.n,
            "goalState": list(c110_goal),
            "layerSizes": c110_res.layer_sizes,
            "stats": c110_res.stats.as_dict(prepare(c110)),
            "witness": c110_rows,
            "witnessChecks": c110_checks,
            "elapsedSeconds": round(c110_time, 3),
        },
        "guards": {
            "baseline": guards_b,
            "cost110": guards_c,
            "variants": guard_variant_stats,
            "elapsedSeconds": round(guard_time, 3),
            "note": "All-reachable expands goal states to the task-capped H=27; no-goal excludes trained>=1 states.",
        },
        "horizon": EXECUTION_HORIZON,
        "contractHorizon": SCENARIO.horizon,
        "contractStyleWitness": {
            "n": contract_n,
            "finalState": list(contract_path[-1][3]),
            "checks": contract_checks,
            "pop1QComputed": q_gh,
            "note": "GH x7 IDLE then GH+PH SETTLER; same N as the canonical witness, different food path.",
        },
        "execution": {
            "totalSeconds": round(time.time() - report_t0, 3),
            "maxRssKb": _max_rss_kb(),
            "python": sys.version.split()[0],
            "all128Seconds": all_result["elapsedSeconds"] if all_result is not None else None,
        },
        "all128": all_summary,
        "discrepancies": discrepancies,
        "limitations": limitations,
    }
    return report


def fixture_summary(report: Dict[str, Any]) -> str:
    b = report["baseline"]
    c = report["cost110"]
    lines = []
    lines.append("MVP v2.1 executable (untrusted search)")
    lines.append(f"  baseline theta: {b['theta']}")
    lines.append(f"  baseline N = {b['n']}  goal={b['goalState']}  layerSizes={b['layerSizes']}")
    lines.append(f"  cost110  theta: {c['theta']}")
    lines.append(f"  cost110  N = {c['n']}  goal={c['goalState']}")
    lines.append(f"  action counts: {report['actionCounts']}")
    lines.append(f"  guards baseline all-reachable: {report['guards']['baseline']['allReachable']['stats']}")
    lines.append(f"  guards cost110 all-reachable:  {report['guards']['cost110']['allReachable']['stats']}")
    if report.get("all128"):
        a = report["all128"]
        lines.append(f"  all128: n={a['count']} envelope={a['envelope']} inert={a['inertAxes']} "
                     f"time={a['elapsedSeconds']}s")
        pc = a["predictionComparison"]
        lines.append(f"  all128 prediction mismatches={len(pc['mismatches'])} "
                     f"envelopeMatch={pc['envelopeMatch']} inertMatch={pc['inertAxesMatch']}")
    if report["discrepancies"]:
        lines.append("  discrepancies:")
        for d in report["discrepancies"]:
            lines.append(f"    {d['id']}: fixture={d['fixtureValue']} observed={d['executableValue']}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def write_fixture(report: Dict[str, Any], path: Path = BASELINE_FIXTURE_PATH) -> None:
    text = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    path.write_text(text, encoding="utf-8")


def check_fixture(path: Path = BASELINE_FIXTURE_PATH) -> Dict[str, Any]:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    _require(data.get("fixtureId") == "mvp-baseline-v1", "unexpected fixture id")
    _require(data.get("untrusted") is True, "fixture must be labelled untrusted")
    _require(data.get("gameFactClaim") is False, "fixture must not claim a game fact")
    # Recompute baseline/counterpart from the rule fixture and compare N + replay.
    b = baseline_theta()
    c110 = cost110_theta()
    res_b = frontier_search(b, horizon=EXECUTION_HORIZON, stop_on_goal=True,
                            keep_frontiers=True, validate=True)
    res_c = frontier_search(c110, horizon=EXECUTION_HORIZON, stop_on_goal=True,
                            keep_frontiers=True, validate=True)
    _require(res_b.n == data["baseline"]["n"], "baseline N mismatch")
    _require(res_c.n == data["cost110"]["n"], "cost110 N mismatch")
    _require(data["baseline"]["witness"], "baseline witness missing")
    _require(data["cost110"]["witness"], "cost110 witness missing")
    verify_witness(b, data["baseline"]["witness"], data["baseline"]["n"])
    verify_witness(c110, data["cost110"]["witness"], data["cost110"]["n"])
    return {"ok": True, "baselineN": res_b.n, "cost110N": res_c.n,
            "baselineWitnessRows": len(data["baseline"]["witness"]),
            "cost110WitnessRows": len(data["cost110"]["witness"])}


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


class MVPModelTests(unittest.TestCase):
    def setUp(self) -> None:
        self.b = baseline_theta()
        self.c = cost110_theta()

    # -- parameters and state -------------------------------------------------
    def test_fixture_parameters(self) -> None:
        self.assertIn(str(SCENARIO.raw["version"]), ("2", "2.1"))
        self.assertEqual(SCENARIO.tile_ids, ("G", "GH", "PH", "P"))
        self.assertEqual(SCENARIO.tile_food, (200, 200, 100, 100))
        self.assertEqual(SCENARIO.tile_prod, (0, 100, 200, 100))
        self.assertEqual(SCENARIO.base_prod, 300)
        self.assertEqual(EXECUTION_HORIZON, 27)
        self.assertEqual(SCENARIO.horizon, 34)
        self.assertEqual(thresholds_for(self.b), (0, 1500, 2400, 3383, 4420))
        self.assertEqual(thresholds_for(self.c._replace(threshold_rounding="floor")),
                         (0, 1500, 2400, 3300, 4420))

    def test_theta_validation(self) -> None:
        validate_theta(self.b)
        with self.assertRaises(ModelError):
            validate_theta(self.b._replace(settler_cost=9000))
        with self.assertRaises(ModelError):
            validate_theta(self.b._replace(turn_order="simultaneous"))
        with self.assertRaises(ModelError):
            validate_theta(self.b._replace(amenity_stock=3))

    def test_tier_multiplier_indexing(self) -> None:
        # Regression: prepared gm/pm are indexed by population, not shifted by one.
        p2 = prepare(self.b)
        p1 = prepare(self.b._replace(amenity_stock=1))
        self.assertEqual((p2.gm[1], p2.gm[2], p2.gm[3], p2.gm[4]), (110, 110, 110, 110))
        self.assertEqual((p2.pm[1], p2.pm[2], p2.pm[3], p2.pm[4]), (105, 105, 105, 105))
        self.assertEqual((p1.gm[1], p1.gm[2], p1.gm[3], p1.gm[4]), (110, 110, 100, 100))
        self.assertEqual((p1.pm[1], p1.pm[2], p1.pm[3], p1.pm[4]), (105, 105, 100, 100))
        # At pop 1 stock 1 is still Happy, so q(GH)=420.
        info = explain_step(self.b._replace(amenity_stock=1), START,
                            Action(1 << TILE_IDS.index("GH"), None, "IDLE"))
        assert info is not None
        self.assertEqual(info.q, 420)

    def test_state_validation(self) -> None:
        validate_state(START)
        validate_state(State(3, 990, 0, 0), prepare(self.b))
        with self.assertRaises(ModelError):
            validate_state(State(0, 0, 0, 0))
        with self.assertRaises(ModelError):
            validate_state(State(1, -1, 0, 0))
        with self.assertRaises(ModelError):
            validate_state(State(1, 0, -1, 0))
        with self.assertRaises(ModelError):
            validate_state(State(1, 0, 8000, 0), prepare(self.b))
        with self.assertRaises(ModelError):
            validate_state(State(5, 0, 0, 0))

    # -- finite actions / occupancy ------------------------------------------
    def test_action_box_and_structural_counts(self) -> None:
        self.assertEqual(len(action_box(1)), 50)
        self.assertEqual(len(action_box(2)), 110)
        self.assertEqual(len(action_box(3)), 150)
        self.assertEqual(len(structural_actions(1)), 5)
        self.assertEqual(len(structural_actions(2)), 50)
        self.assertEqual(len(structural_actions(3)), 62)  # contract's <=62
        self.assertEqual(len(idle_free_actions(1)), 4)
        self.assertEqual(len(idle_free_actions(2)), 24)
        self.assertEqual(len(idle_free_actions(3)), 12)

    def test_action_generation_is_powerset_product(self) -> None:
        for pop in (1, 2, 3):
            box = set(action_box(pop))
            expected = set()
            for mask in range(1 << N_TILES):
                if mask.bit_count() > pop:
                    continue
                for extra in (None,) + tuple(range(N_TILES)):
                    for build in BUILDS:
                        expected.add(Action(mask, extra, build))
            self.assertEqual(box, expected)

    def test_worker_occupancy_and_tile_capacity(self) -> None:
        for pop in (1, 2, 3):
            for action in structural_actions(pop):
                self.assertLessEqual(WORK_META[action.work][0], pop)
                if action.extra is not None:
                    self.assertFalse((action.work >> action.extra) & 1)
        # No duplicate tile is representable: each tile is one bit.
        self.assertEqual(WORK_META[(1 << 0) | (1 << 1)][0], 2)

    def test_extra_must_be_unworked_and_idle_has_no_extra(self) -> None:
        state = State(2, 0, 0, 0)
        in_work = Action(0b0011, 1, "SETTLER")
        self.assertIsNone(step(self.b, state, in_work))
        idle_extra = Action(0b0001, 2, "IDLE")
        self.assertIsNone(step(self.b, state, idle_extra))
        ok = Action(0b0001, 2, "SETTLER")
        self.assertIsNotNone(step(self.b, state, ok))

    # -- selection timing / settler prereq -----------------------------------
    def test_settler_preturn_legality(self) -> None:
        self.assertIsNone(step(self.b, State(1, 0, 0, 0), Action(0b0001, None, "SETTLER")))
        self.assertIsNotNone(step(self.b, State(2, 0, 0, 0), Action(0b0001, None, "SETTLER")))

    def test_selection_timing_growth_cannot_legalise_settler(self) -> None:
        # Food is high enough to grow this step, but SETTLER legality reads pre-turn pop=1.
        state = State(1, 1490, 0, 0)
        action = Action(0b0001, None, "SETTLER")  # GH
        self.assertIsNone(step(self.b, state, action))
        # The same action as IDLE grows to pop 2 and still credits no progress.
        nxt = step(self.b, state, Action(0b0001, None, "IDLE"))
        self.assertIsNotNone(nxt)
        assert nxt is not None
        self.assertEqual(nxt.pop, 2)
        self.assertEqual(nxt.prog, 0)

    # -- banking bug ----------------------------------------------------------
    def test_idle_accrues_nothing(self) -> None:
        res = frontier_search(self.b, horizon=self.b_settler_n(), stop_on_goal=False,
                              exclude_goal=False, keep_frontiers=True, validate=True)
        seen = 0
        for layer in res.layers or []:
            for s in layer:
                for action in structural_actions(s.pop):
                    if action.build != "IDLE":
                        continue
                    nxt = step(self.b, s, action)
                    if nxt is None:
                        continue
                    seen += 1
                    self.assertEqual(nxt.prog, s.prog)
                    self.assertEqual(nxt.trained, s.trained)
        self.assertGreater(seen, 0)

    def b_settler_n(self) -> int:
        r = frontier_search(self.b, horizon=EXECUTION_HORIZON, stop_on_goal=True, validate=True)
        assert r.n is not None
        return r.n

    def test_banking_bug_would_be_faster(self) -> None:
        good = frontier_search(self.b, horizon=EXECUTION_HORIZON, stop_on_goal=True, validate=True)
        assert good.n is not None
        p = prepare(self.b)
        # Negative control: a legacy bug credits q on IDLE too.  It must not be
        # the model, and it must be detectably faster (banking across the prereq).
        layer = {START}
        bad_n = None
        for t in range(SCENARIO.horizon):
            nxt = set()
            for s in layer:
                for action in structural_actions(s.pop):
                    nxt_state = _step_prepared(p, s, action, credit_idle=True)
                    if nxt_state is None:
                        continue
                    nxt.add(nxt_state)
                    if nxt_state.trained >= 1:
                        bad_n = t + 1
                        break
                if bad_n is not None:
                    break
            if bad_n is not None:
                break
            layer = nxt
        self.assertIsNotNone(bad_n)
        self.assertLess(bad_n, good.n)  # bug is a relaxation, not the contract

    # -- ghost extra ----------------------------------------------------------
    def test_ghost_extra_no_growth_is_inert(self) -> None:
        state = State(2, 0, 0, 0)
        a_none = Action(0b0011, None, "SETTLER")  # G+GH, d=200 -> grows actually
        # Use PH+P (zero surplus) so no growth: d=0.
        work = (1 << TILE_IDS.index("PH")) | (1 << TILE_IDS.index("P"))
        a1 = Action(work, TILE_IDS.index("G"), "SETTLER")
        a2 = Action(work, None, "SETTLER")
        r1 = step(self.b, state, a1)
        r2 = step(self.b, state, a2)
        self.assertEqual(r1, r2)
        i1 = explain_step(self.b, state, a1)
        i2 = explain_step(self.b, state, a2)
        assert i1 is not None and i2 is not None
        self.assertFalse(i1.grew)
        self.assertEqual(i1.q, i2.q)
        self.assertEqual(i1.extra_prod, 0)

    def test_ghost_extra_only_on_growth_best(self) -> None:
        # pop 2 at 2350 food, GH+PH gives d=100, e=110 -> growth to pop 3.
        state = State(2, 2350, 0, 0)
        work = (1 << TILE_IDS.index("GH")) | (1 << TILE_IDS.index("PH"))
        extra = TILE_IDS.index("P")
        a_none = Action(work, None, "SETTLER")
        a_extra = Action(work, extra, "SETTLER")
        i_none = explain_step(self.b, state, a_none)
        i_extra = explain_step(self.b, state, a_extra)
        assert i_none is not None and i_extra is not None
        self.assertTrue(i_none.grew)
        self.assertTrue(i_extra.grew)
        self.assertEqual(i_extra.extra_prod, TILE_PROD[extra])
        self.assertEqual(i_extra.q - i_none.q, TILE_PROD[extra] * 105 // 100)
        # newCitizen=none must make extra inert.
        theta_none = self.b._replace(new_citizen="none")
        j_none = explain_step(theta_none, state, a_none)
        j_extra = explain_step(theta_none, state, a_extra)
        assert j_none is not None and j_extra is not None
        self.assertEqual(j_none.q, j_extra.q)
        # production_first has no new-citizen term in the normative pseudocode.
        theta_pf = self.b._replace(turn_order="production_first")
        k_none = explain_step(theta_pf, state, a_none)
        k_extra = explain_step(theta_pf, state, a_extra)
        assert k_none is not None and k_extra is not None
        self.assertEqual(k_none.q, k_extra.q)

    def test_extra_food_never_contributes(self) -> None:
        state = State(2, 0, 0, 0)
        work = (1 << TILE_IDS.index("PH")) | (1 << TILE_IDS.index("P"))
        extra = TILE_IDS.index("G")  # 2F tile
        info = explain_step(self.b, state, Action(work, extra, "SETTLER"))
        assert info is not None
        self.assertEqual(info.food_yield, 200 + 100 + 100)  # extra G ignored
        self.assertFalse(info.grew)

    # -- nonnegative food legality -------------------------------------------
    def test_nonnegative_surplus_legality(self) -> None:
        state = State(3, 0, 0, 0)
        low_work = 1 << TILE_IDS.index("P")
        self.assertIsNone(step(self.b, state, Action(low_work, None, "IDLE")))
        high_work = ((1 << TILE_IDS.index("G")) | (1 << TILE_IDS.index("GH"))
                     | (1 << TILE_IDS.index("PH")))
        self.assertIsNotNone(step(self.b, state, Action(high_work, None, "SETTLER")))

    def test_starvation_restriction_is_inert_on_baseline(self) -> None:
        for theta in (self.b, self.c):
            p = prepare(theta)
            good = frontier_search(theta, horizon=EXECUTION_HORIZON, stop_on_goal=True, validate=True)
            # Negative control: allow d < 0 (restriction removed).
            layer = {START}
            bad_n = None
            for t in range(EXECUTION_HORIZON):
                nxt = set()
                for s in layer:
                    for action in structural_actions(s.pop):
                        nxt_state = _step_prepared(p, s, action, allow_starving=True)
                        if nxt_state is None:
                            continue
                        nxt.add(nxt_state)
                        if nxt_state.trained >= 1:
                            bad_n = t + 1
                            break
                    if bad_n is not None:
                        break
                if bad_n is not None:
                    break
                layer = nxt
            self.assertEqual(good.n, bad_n)

    # -- goal terminality / frontiers ----------------------------------------
    def test_goal_terminality_and_no_earlier_goal(self) -> None:
        res = frontier_search(self.b, horizon=EXECUTION_HORIZON, stop_on_goal=True,
                              keep_frontiers=True, validate=True)
        assert res.n is not None and res.layers is not None
        self.assertEqual(len(res.layers), res.n + 1)
        for t in range(res.n):
            for s in res.layers[t]:
                self.assertEqual(s.trained, 0, f"goal at layer {t} before N={res.n}")
        # Goal states are present in the final layer and are not expanded.
        self.assertTrue(any(goal(s) for s in res.layers[res.n]))
        # trained is monotone on the canonical path.
        path = reconstruct_path(res)
        for _, pre, action, post in path:
            self.assertGreaterEqual(post.trained, pre.trained)
            self.assertIsNotNone(step(self.b, pre, action))

    def test_exact_step_layers_and_parents(self) -> None:
        res = frontier_search(self.b, horizon=self.b_settler_n(), stop_on_goal=True,
                              keep_frontiers=True, validate=True)
        assert res.n is not None and res.layers is not None and res.parents is not None
        self.assertEqual(res.layer_sizes[0], 1)
        self.assertEqual(len(res.layer_sizes), res.n + 1)
        for t in range(1, res.n + 1):
            for s in res.layers[t]:
                self.assertIn(s, res.parents[t])
                prev, action = res.parents[t][s]
                self.assertEqual(step(self.b, prev, action), s)

    # -- baseline / witness replay -------------------------------------------
    def test_baseline_n(self) -> None:
        res = frontier_search(self.b, horizon=EXECUTION_HORIZON, stop_on_goal=True, validate=True)
        self.assertEqual(res.n, 20)
        self.assertLessEqual(res.n, EXECUTION_HORIZON)

    def test_cost110_n(self) -> None:
        res = frontier_search(self.c, horizon=EXECUTION_HORIZON, stop_on_goal=True, validate=True)
        self.assertEqual(res.n, 25)
        self.assertLessEqual(res.n, EXECUTION_HORIZON)

    def test_baseline_witness_replay(self) -> None:
        n = self.b_settler_n()
        path, checks = find_witness(self.b, n)
        self.assertEqual(len(path), 20)
        self.assertTrue(checks["goal"])
        self.assertTrue(checks["idleFree"])
        self.assertTrue(checks["progZeroBeforePop2"])
        self.assertTrue(checks["nonnegativeSurplus"])
        self.assertTrue(checks["noGoalBeforeN"])
        self.assertTrue(checks["settlerPreturnLegal"])
        self.assertEqual(checks["finalState"][3], 1)

    def test_cost110_witness_replay(self) -> None:
        res = frontier_search(self.c, horizon=EXECUTION_HORIZON, stop_on_goal=True, validate=True)
        assert res.n is not None
        path, checks = find_witness(self.c, res.n)
        self.assertEqual(len(path), res.n)
        self.assertTrue(checks["goal"])
        self.assertTrue(checks["idleFree"])
        self.assertTrue(checks["progZeroBeforePop2"])
        self.assertTrue(checks["nonnegativeSurplus"])
        self.assertEqual(checks["finalState"][3], 1)

    def test_contract_style_witness_replays(self) -> None:
        path = contract_style_path(self.b)
        self.assertEqual(len(path), 20)
        rows = witness_rows(self.b, path)
        checks = verify_witness(self.b, rows, 20)
        self.assertTrue(checks["goal"])
        self.assertTrue(checks["idleFree"])
        self.assertEqual(checks["finalState"], [1, 1430, 190, 1])
        self.assertEqual(_q_at_pop1_gh(self.b), 420)  # not the fixture's 525

    # -- guards / exactness / determinism ------------------------------------
    def test_guards_baseline(self) -> None:
        g = guard_report(self.b)
        st = g["allReachable"]["stats"]
        self.assertEqual(st["maxPop"], 3)
        self.assertFalse(st["pop4Seen"])
        self.assertEqual(st["maxFoodPop2"], 2310)
        self.assertEqual(st["maxFoodPop3"], 990)
        self.assertFalse(st["t3Crossed"])
        self.assertGreaterEqual(st["housingLeftAtMaxPop"], 2)
        self.assertEqual(g["allReachable"]["firstGoal"], 20)

    def test_exactness_and_integer_only(self) -> None:
        res = frontier_search(self.b, horizon=self.b_settler_n(), stop_on_goal=True,
                              keep_frontiers=True, validate=True)
        assert res.layers is not None
        checked = 0
        for layer in res.layers:
            for s in layer:
                for action in structural_actions(s.pop):
                    info = explain_step(self.b, s, action)
                    if info is None:
                        continue
                    checked += 1
                    self.assertIsInstance(info.q, int)
                    self.assertIsInstance(info.growth, int)
                    self.assertEqual(info.q_raw % 100, 0)
                    self.assertEqual((info.surplus * _GROWTH_MULT[tier(self.b, info.surplus_pop)]) % 100, 0)
                    self.assertNotIsInstance(info.q, float)
        self.assertGreater(checked, 0)

    def test_deterministic_baseline(self) -> None:
        r1 = frontier_search(self.b, horizon=EXECUTION_HORIZON, stop_on_goal=True, validate=True)
        r2 = frontier_search(self.b, horizon=EXECUTION_HORIZON, stop_on_goal=True, validate=True)
        self.assertEqual(r1.n, r2.n)
        self.assertEqual(r1.layer_sizes, r2.layer_sizes)
        self.assertEqual(r1.stats.as_dict(prepare(self.b)), r2.stats.as_dict(prepare(self.b)))

    def test_prediction_comparison_is_not_a_source(self) -> None:
        # This test deliberately checks the analyst prediction only AFTER the
        # independent result has been computed.
        res = frontier_search(self.b, horizon=EXECUTION_HORIZON, stop_on_goal=True, validate=True)
        predicted = SCENARIO.raw["predictions"]["baselineTheta"]["predictedN"]
        self.assertEqual(res.n, predicted)


def run_self_tests() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(MVPModelTests)
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    return 0 if result.wasSuccessful() else 1


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--self-test", action="store_true", help="run the model test suite")
    parser.add_argument("--guards", action="store_true", help="run H=27 guard enumeration for baseline/cost110")
    parser.add_argument("--all", action="store_true", help="run all 128 theta combinations")
    parser.add_argument("--write-fixture", action="store_true", help="write fixtures/mvp-baseline.json")
    parser.add_argument("--check-fixture", action="store_true", help="replay/validate the frozen fixture")
    parser.add_argument("--no-all", action="store_true", help="with --write-fixture, skip the 128 search")
    parser.add_argument("--verbose", action="store_true", help="progress output")
    args = parser.parse_args(argv)

    if args.self_test:
        return run_self_tests()
    if args.check_fixture:
        print(json.dumps(check_fixture(), indent=2))
        return 0
    if args.guards:
        print(json.dumps({"baseline": guard_report(baseline_theta()),
                          "cost110": guard_report(cost110_theta())}, indent=2))
        return 0
    if args.all:
        result = all_theta_search(verbose=True)
        print(json.dumps({k: v for k, v in result.items() if k != "results"}, indent=2))
        return 0
    if args.write_fixture:
        report = build_fixture_report(run_all=not args.no_all, verbose=True)
        write_fixture(report)
        print(fixture_summary(report))
        print(f"wrote {BASELINE_FIXTURE_PATH}")
        return 0

    # Default: baseline + counterpart quick report.
    report = build_fixture_report(run_all=False, verbose=False)
    print(fixture_summary(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
