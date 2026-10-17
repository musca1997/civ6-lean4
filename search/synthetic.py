#!/usr/bin/env python3
"""Synthetic tiny "city" benchmark (NOT Civilization VI).

Purpose
-------
Provide a *deliberately fake*, fully integer, tiny turn-based benchmark with the
same proof shape the Lean development needs:

  * one city, population 1..2, a food-vs-production citizen tradeoff,
  * an explicitly finite legal action set,
  * a deterministic, fully specified round order,
  * a monotone completed-settler counter,
  * goal = "at least one settler completed" with a population prerequisite,
  * exhaustive, no-pruning BFS that yields an earliest-goal candidate plus a
    replayable witness.

The numbers produced here are SYNTHETIC. They are not Civ6 formulas, not a
Civ6 optimum, and carry no claim about the real game. The Python search is an
UNTRUSTED candidate generator; the authoritative artifact is
`fixtures/synthetic-v0.json` (rules + initial state), which Lean can re-implement
and decide exhaustively later.

Files owned by this module: search/synthetic.py, fixtures/synthetic-v0.json,
scripts/check-synthetic.py, research/SYNTHETIC.md. Python standard library only.

Usage
-----
    python3 search/synthetic.py                 # run BFS, print report
    python3 search/synthetic.py --json          # machine-readable candidate
    python3 search/synthetic.py --emit-fixture  # print canonical fixture JSON
    python3 search/synthetic.py --self-test     # run the internal test suite
    python3 search/synthetic.py --check-fixture # semantic fixture check (all keys)
    python3 scripts/check-synthetic.py          # actual Lean output vs fixture

`--check-fixture` compares parsed JSON semantically (every top-level key), not
byte-by-byte, and treats a missing/corrupt fixture as an error (exit 2) rather
than a skipped test. Exit status is non-zero if a self-check fails.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import tempfile
import unittest
from dataclasses import asdict, dataclass, replace
from typing import Any, Dict, Iterable, Iterator, List, Optional, Sequence, Tuple

# ---------------------------------------------------------------------------
# 0. Model constants (the whole benchmark lives in these few numbers).
# ---------------------------------------------------------------------------

FIXTURE_ID = "synthetic-v0"

#: Tile ids understood by the v0 model. The tile set of a spec must be exactly
#: this set: an extra or renamed tile would be silently ignored otherwise.
TILE_IDS: Tuple[str, ...] = ("farm", "mine")

TILE_COMMENT = (
    "farm = more food, less production; mine = more production, no food. "
    "Farms also yield 1 production on purpose, so that 'grow this tick and "
    "complete this tick' is reachable and the round order is observable."
)
GROWTH_THRESHOLD_FORMULA = (
    "T(p) = 4*p for p in {1,2}; linear by design, NOT a Civ6 curve"
)
FOOD_CAP_RULE = (
    "after the food phase food <= T(pop)-1; surplus at popMax is discarded"
)


def _coverage_modelling() -> Dict[str, Any]:
    """Descriptive (non-behavioural) coverage notes, fresh copy each call."""
    return {
        "settlerProductionWhilePrereqUnmet": "progress capped at cost-1",
        "noBuy": True,
        "noQueueSwitch": True,
        "noChop": True,
        "noPolicy": True,
        "noStarvation": (
            "net food below zero floors food at 0, population never shrinks from hunger"
        ),
    }


#: Canonical rules block of the frozen fixture. This is spec *data*, not the
#: rule engine's state: `Rules.from_spec` validates it against the rule contract
#: (see `Rules`), and `Rules.to_spec` regenerates an equivalent block from any
#: `Rules` instance (including perturbed ones).
RULES_SPEC: Dict[str, Any] = {
    "synthetic": True,
    "civ6Model": False,
    "popMin": 1,
    "popMax": 2,
    "foodPerCitizenPerTick": 2,
    "tiles": [
        {"id": "farm", "food": 3, "production": 1},
        {"id": "mine", "food": 0, "production": 2},
    ],
    "tileComment": TILE_COMMENT,
    "growthThresholdByPop": {"1": 4, "2": 8},
    "growthThresholdFormula": GROWTH_THRESHOLD_FORMULA,
    "foodFloor": 0,
    "foodCapRule": FOOD_CAP_RULE,
    "settler": {
        "cost": 8,
        "populationCost": 1,
        "prereqPop": 2,
        "productionProgressCap": 7,
        "onCompleteFood": 0,
        "onCompleteProduction": 0,
    },
    "coverageModelling": _coverage_modelling(),
}

INITIAL_STATE_SPEC: Dict[str, Any] = {
    "tick": 0,
    "pop": 1,
    "food": 0,
    "production": 0,
    "settlersCompleted": 0,
}

GOAL_SPEC: Dict[str, Any] = {
    "predicate": "settlersCompleted >= 1",
    "requiresPopAtCompletion": 2,
    "note": "terminal: goal states have no outgoing actions in the search",
}


# ---------------------------------------------------------------------------
# 1. Rules / state / actions.
# ---------------------------------------------------------------------------


class IllegalAction(Exception):
    """Raised when an action is not in the finite legal action set."""


class IllegalState(Exception):
    """Raised when a state violates the model invariants."""


class RuleSpecError(ValueError):
    """Raised when a rule configuration violates the explicit rule contract."""


@dataclass(frozen=True)
class Rules:
    """Validated integer rule set of the synthetic model.

    Rule contract, enforced by ``__post_init__`` (and therefore also by
    ``dataclasses.replace``) and by ``from_spec``:

    * ``1 <= pop_min <= pop_max``;
    * growth thresholds are defined for exactly ``pop_min..pop_max`` and are
      strictly positive (so ``max_food p = T p - 1 >= 0``);
    * tile yields, per-citizen consumption and ``food_floor`` are non-negative;
    * ``settler_cost >= 1`` and the production-progress cap has a **single**
      source of truth: it is *derived* as ``settler_cost - 1``. There is no
      stored ``progress_cap`` field, so ``step`` (which caps progress) and
      ``check_state`` (which bounds the state) cannot disagree;
    * ``pop_min <= settler_prereq_pop <= pop_max``, and completion keeps the
      population in range: ``p - settler_pop_cost >= pop_min`` for every ``p``
      at which completion can happen;
    * the completion reset values fit the resulting state:
      ``0 <= on_complete_food <= max_food (p - settler_pop_cost)`` and
      ``0 <= on_complete_prod <= progress_cap``.

    A spec may still *state* ``productionProgressCap`` explicitly (the fixture
    does, for readability); ``from_spec`` checks that it equals the derived
    ``settler_cost - 1`` and rejects the spec otherwise.
    """

    pop_min: int
    pop_max: int
    food_per_citizen: int
    farm_food: int
    farm_prod: int
    mine_food: int
    mine_prod: int
    threshold_by_pop: Tuple[Tuple[int, int], ...]
    food_floor: int
    settler_cost: int
    settler_pop_cost: int
    settler_prereq_pop: int
    on_complete_food: int
    on_complete_prod: int

    def __post_init__(self) -> None:
        validate_rules(self)

    # -- derived helpers -------------------------------------------------
    def threshold(self, pop: int) -> int:
        for p, t in self.threshold_by_pop:
            if p == pop:
                return t
        raise IllegalState(f"no growth threshold defined for pop={pop}")

    def max_food(self, pop: int) -> int:
        return self.threshold(pop) - 1

    @property
    def progress_cap(self) -> int:
        """The single production-progress cap: always ``settler_cost - 1``."""
        return self.settler_cost - 1

    def max_progress(self) -> int:
        return self.progress_cap

    @staticmethod
    def from_spec(spec: Dict[str, Any]) -> "Rules":
        """Parse and validate a rules block; raises ``RuleSpecError`` on drift."""
        if not isinstance(spec, dict):
            raise RuleSpecError(f"rules spec must be an object, got {type(spec).__name__}")

        tiles_spec = spec.get("tiles")
        if not isinstance(tiles_spec, list):
            raise RuleSpecError("rules.tiles must be a list")
        tiles: Dict[str, Dict[str, Any]] = {}
        for entry in tiles_spec:
            if not isinstance(entry, dict) or "id" not in entry:
                raise RuleSpecError(f"rules.tiles entry malformed: {entry!r}")
            tid = entry["id"]
            if tid in tiles:
                raise RuleSpecError(f"rules.tiles: duplicate tile id {tid!r}")
            tiles[tid] = entry
        if set(tiles) != set(TILE_IDS):
            raise RuleSpecError(
                f"rules.tiles must be exactly {list(TILE_IDS)}, got {sorted(map(str, tiles))}"
            )

        thresholds_spec = spec.get("growthThresholdByPop")
        if not isinstance(thresholds_spec, dict):
            raise RuleSpecError("rules.growthThresholdByPop must be an object")
        thresholds = []
        for raw_pop, raw_threshold in thresholds_spec.items():
            try:
                pop_key = int(raw_pop)
            except (TypeError, ValueError):
                raise RuleSpecError(
                    f"rules.growthThresholdByPop: non-integer key {raw_pop!r}"
                ) from None
            if isinstance(raw_threshold, bool) or not isinstance(raw_threshold, int):
                raise RuleSpecError(
                    f"rules.growthThresholdByPop[{raw_pop!r}]: expected a plain "
                    f"int, got {raw_threshold!r} ({type(raw_threshold).__name__})"
                )
            thresholds.append((pop_key, raw_threshold))

        settler = spec.get("settler")
        if not isinstance(settler, dict):
            raise RuleSpecError("rules.settler must be an object")

        rules = Rules(
            pop_min=_spec_int(spec, "popMin", "rules"),
            pop_max=_spec_int(spec, "popMax", "rules"),
            food_per_citizen=_spec_int(spec, "foodPerCitizenPerTick", "rules"),
            farm_food=_spec_int(tiles["farm"], "food", "rules.tiles.farm"),
            farm_prod=_spec_int(tiles["farm"], "production", "rules.tiles.farm"),
            mine_food=_spec_int(tiles["mine"], "food", "rules.tiles.mine"),
            mine_prod=_spec_int(tiles["mine"], "production", "rules.tiles.mine"),
            threshold_by_pop=tuple(sorted(thresholds)),
            food_floor=_spec_int(spec, "foodFloor", "rules"),
            settler_cost=_spec_int(settler, "cost", "rules.settler"),
            settler_pop_cost=_spec_int(settler, "populationCost", "rules.settler"),
            settler_prereq_pop=_spec_int(settler, "prereqPop", "rules.settler"),
            on_complete_food=_spec_int(settler, "onCompleteFood", "rules.settler"),
            on_complete_prod=_spec_int(
                settler, "onCompleteProduction", "rules.settler"
            ),
        )
        declared_cap = _spec_int(settler, "productionProgressCap", "rules.settler")
        if declared_cap != rules.progress_cap:
            raise RuleSpecError(
                "rules.settler.productionProgressCap="
                f"{declared_cap} contradicts the single-source cap "
                f"settler_cost-1={rules.progress_cap} (cost={rules.settler_cost})"
            )
        return rules

    def to_spec(self) -> Dict[str, Any]:
        """Regenerate a rules block from *this* instance (never the default).

        ``default_rules().to_spec() == RULES_SPEC`` holds; perturbed instances
        produce their own block, so emitting a fixture for perturbed rules can
        no longer silently advertise the default constants.
        """
        return {
            "synthetic": True,
            "civ6Model": False,
            "popMin": self.pop_min,
            "popMax": self.pop_max,
            "foodPerCitizenPerTick": self.food_per_citizen,
            "tiles": [
                {"id": "farm", "food": self.farm_food, "production": self.farm_prod},
                {"id": "mine", "food": self.mine_food, "production": self.mine_prod},
            ],
            "tileComment": TILE_COMMENT,
            "growthThresholdByPop": {
                str(p): t for p, t in sorted(self.threshold_by_pop)
            },
            "growthThresholdFormula": GROWTH_THRESHOLD_FORMULA,
            "foodFloor": self.food_floor,
            "foodCapRule": FOOD_CAP_RULE,
            "settler": {
                "cost": self.settler_cost,
                "populationCost": self.settler_pop_cost,
                "prereqPop": self.settler_prereq_pop,
                "productionProgressCap": self.progress_cap,
                "onCompleteFood": self.on_complete_food,
                "onCompleteProduction": self.on_complete_prod,
            },
            "coverageModelling": _coverage_modelling(),
        }


def _spec_int(mapping: Dict[str, Any], key: str, where: str) -> int:
    """Fetch a required plain-int field; reject bools, strings and floats."""
    if key not in mapping:
        raise RuleSpecError(f"{where}: missing required integer field {key!r}")
    value = mapping[key]
    if isinstance(value, bool) or not isinstance(value, int):
        raise RuleSpecError(
            f"{where}.{key}: expected a plain int, got {value!r} "
            f"({type(value).__name__})"
        )
    return value


def validate_rules(r: Rules) -> None:
    """Enforce the rule contract documented on ``Rules``."""

    def fail(message: str) -> None:
        raise RuleSpecError(message)

    if r.pop_min < 1:
        fail(f"pop_min must be >= 1, got {r.pop_min}")
    if r.pop_max < r.pop_min:
        fail(f"pop_max ({r.pop_max}) < pop_min ({r.pop_min})")
    for name, value in (
        ("food_per_citizen", r.food_per_citizen),
        ("farm_food", r.farm_food),
        ("farm_prod", r.farm_prod),
        ("mine_food", r.mine_food),
        ("mine_prod", r.mine_prod),
        ("food_floor", r.food_floor),
    ):
        if value < 0:
            fail(f"{name} must be non-negative, got {value}")
    if r.settler_cost < 1:
        fail(f"settler_cost must be >= 1, got {r.settler_cost}")
    if not (r.pop_min <= r.settler_prereq_pop <= r.pop_max):
        fail(
            f"settler_prereq_pop ({r.settler_prereq_pop}) outside "
            f"[{r.pop_min},{r.pop_max}]"
        )
    if r.settler_pop_cost < 0:
        fail(f"settler_pop_cost must be non-negative, got {r.settler_pop_cost}")

    pops = list(range(r.pop_min, r.pop_max + 1))
    table = dict(r.threshold_by_pop)
    if len(table) != len(r.threshold_by_pop):
        fail("growth threshold table contains duplicate populations")
    missing = [p for p in pops if p not in table]
    if missing:
        fail(f"growth thresholds missing for populations {missing}")
    extra = [p for p in table if p not in pops]
    if extra:
        fail(f"growth thresholds given for out-of-range populations {extra}")
    for p in pops:
        if table[p] <= 0:
            fail(f"growth threshold T({p}) must be positive, got {table[p]}")
        if r.max_food(p) < 0:
            fail(f"max_food({p}) < 0")

    for p in range(r.settler_prereq_pop, r.pop_max + 1):
        after = p - r.settler_pop_cost
        if after < r.pop_min:
            fail(
                f"completion at pop {p} with cost {r.settler_pop_cost} leaves "
                f"pop {after} < pop_min {r.pop_min}"
            )
        if not (0 <= r.on_complete_food <= r.max_food(after)):
            fail(
                f"on_complete_food={r.on_complete_food} outside "
                f"[0,{r.max_food(after)}] for completion pop {after}"
            )
        if not (0 <= r.on_complete_prod <= r.progress_cap):
            fail(
                f"on_complete_prod={r.on_complete_prod} outside "
                f"[0,{r.progress_cap}]"
            )


def default_rules() -> Rules:
    return Rules.from_spec(RULES_SPEC)


#: State = (pop, food, production, settlersCompleted). Integer only.
State = Tuple[int, int, int, int]

#: Action = (citizensOnFarm, citizensOnMine). Every citizen works exactly one
#: tile; two citizens may work the same tile in this synthetic model.
Action = Tuple[int, int]

INITIAL_STATE: State = (
    int(INITIAL_STATE_SPEC["pop"]),
    int(INITIAL_STATE_SPEC["food"]),
    int(INITIAL_STATE_SPEC["production"]),
    int(INITIAL_STATE_SPEC["settlersCompleted"]),
)


def state_key(s: State) -> str:
    """Canonical, implementation-independent encoding of a state."""
    return f"pop={s[0]};food={s[1]};prod={s[2]};done={s[3]}"


def action_key(a: Action) -> str:
    return f"farm={a[0]},mine={a[1]}"


def goal(s: State) -> bool:
    """Goal is the monotone history marker, never a queue/progress check."""
    return s[3] >= 1


def check_state(r: Rules, s: State) -> None:
    """Enforce the canonical state invariants (used by tests and search)."""
    if len(s) != 4:
        raise IllegalState(f"state must have 4 components, got {s!r}")
    pop, food, prod, done = s
    for name, v in (("pop", pop), ("food", food), ("production", prod), ("done", done)):
        if not isinstance(v, int) or isinstance(v, bool):
            raise IllegalState(f"{name} must be a plain int, got {v!r}")
    if not (r.pop_min <= pop <= r.pop_max):
        raise IllegalState(f"pop {pop} outside [{r.pop_min},{r.pop_max}]")
    if not (r.food_floor <= food <= r.max_food(pop)):
        raise IllegalState(f"food {food} outside [{r.food_floor},{r.max_food(pop)}]")
    if not (0 <= prod <= r.max_progress()):
        raise IllegalState(f"production {prod} outside [0,{r.max_progress()}]")
    if done not in (0, 1):
        raise IllegalState(f"settlersCompleted {done} not in {{0,1}}")


def legal_actions(r: Rules, s: State) -> List[Action]:
    """Enumerate ALL legal actions in canonical order.

    For a state with population p and no completed settler, exactly p+1
    actions are legal: (k, p-k) for k = 0..p, ordered by increasing k (i.e.
    lexicographic on the farm count). Assignment is total: no citizen idles,
    and no other action kinds exist in this model.
    """
    check_state(r, s)
    if goal(s):
        return []
    pop = s[0]
    return [(k, pop - k) for k in range(pop + 1)]


def _validate_action(r: Rules, s: State, a: Action) -> None:
    check_state(r, s)
    if goal(s):
        raise IllegalAction(f"state {state_key(s)} is terminal (goal reached)")
    if not (isinstance(a, tuple) and len(a) == 2):
        raise IllegalAction(f"action must be a 2-tuple, got {a!r}")
    for v in a:
        if not isinstance(v, int) or isinstance(v, bool):
            raise IllegalAction(f"action components must be plain ints, got {a!r}")
    nfarm, nmine = a
    if nfarm < 0 or nmine < 0:
        raise IllegalAction(f"negative assignment in {a!r}")
    if nfarm + nmine != s[0]:
        raise IllegalAction(
            f"assignment {a!r} does not employ exactly pop={s[0]} citizens"
        )
    if a not in legal_actions(r, s):
        raise IllegalAction(f"action {a!r} not in enumerated set")


def step(r: Rules, s: State, a: Action) -> State:
    """Apply exactly one tick: yields -> food phase/growth -> production phase.

    See research/SYNTHETIC.md for the mathematical statement; the order below
    is normative and is what Lean must reproduce.
    """
    _validate_action(r, s, a)
    pop, food, prod, done = s
    nfarm, nmine = a

    # (1) yields, computed from the PRE-growth population
    net_food = (
        nfarm * r.farm_food
        + nmine * r.mine_food
        - pop * r.food_per_citizen
    )
    gained_prod = nfarm * r.farm_prod + nmine * r.mine_prod

    # (2) food phase: floor at 0 (no starvation), then growth loop
    food2 = max(r.food_floor, food + net_food)
    pop2 = pop
    while pop2 < r.pop_max and food2 >= r.threshold(pop2):
        food2 -= r.threshold(pop2)
        pop2 += 1
    if pop2 == r.pop_max:
        # at max population, surplus beyond T(pop)-1 is discarded
        food2 = min(food2, r.max_food(pop2))

    # (3) production phase: prerequisite gate, then completion
    raw_prod = prod + gained_prod
    if pop2 >= r.settler_prereq_pop:
        if raw_prod >= r.settler_cost:
            new_state = (
                pop2 - r.settler_pop_cost,
                r.on_complete_food,
                r.on_complete_prod,
                done + 1,
            )
        else:
            new_state = (pop2, food2, raw_prod, done)
    else:
        # prerequisite unmet: progress may accumulate but cannot complete
        new_state = (pop2, food2, min(raw_prod, r.progress_cap), done)

    check_state(r, new_state)
    if new_state[3] < s[3]:
        raise AssertionError("completion marker decreased (must be monotone)")
    return new_state  # type: ignore[return-value]


# ---------------------------------------------------------------------------
# 2. Exhaustive no-pruning BFS + witness.
# ---------------------------------------------------------------------------


@dataclass
class BfsResult:
    rules: Rules
    initial: State
    optimum: Optional[int]
    layers: List[List[State]]  # distinct states reachable in exactly t ticks
    parents: Dict[State, Tuple[State, Action]]
    goal_states: List[State]
    witness: List[Action]
    witness_states: List[State]
    transitions: int  # number of (state, action) pairs expanded

    def layer_counts(self) -> List[int]:
        return [len(layer) for layer in self.layers]

    def layer_digests(self) -> List[str]:
        return [layer_digest(layer) for layer in self.layers]


def layer_digest(layer: Iterable[State]) -> str:
    """Stable digest of a layer's distinct canonical state encodings."""
    payload = "\n".join(sorted(state_key(s) for s in layer)).encode("ascii")
    return hashlib.sha256(payload).hexdigest()[:16]


def bfs(r: Rules, initial: State, max_ticks: int) -> BfsResult:
    """Breadth-first, no pruning, goal states are terminal (never expanded).

    Deduplication is only `state -> earliest layer`; no dominance or
    heuristic pruning is performed. Dropping a duplicate at a later layer is
    exact because transitions are Markovian: anything reachable from the later
    occurrence is reachable from the earlier one.
    """
    check_state(r, initial)
    layers: List[List[State]] = [[initial]]
    parents: Dict[State, Tuple[State, Action]] = {}
    seen = {initial: 0}
    transitions = 0
    optimum: Optional[int] = None
    goal_states: List[State] = []

    if goal(initial):
        optimum = 0
        goal_states = [initial]

    for t in range(max_ticks):
        if optimum is not None:
            break
        frontier = layers[t]
        nxt: List[State] = []
        for s in frontier:
            if goal(s):
                continue
            for a in legal_actions(r, s):
                transitions += 1
                s2 = step(r, s, a)
                if s2 in seen and seen[s2] <= t + 1:
                    continue
                seen[s2] = t + 1
                parents[s2] = (s, a)
                nxt.append(s2)
        layers.append(nxt)
        if any(goal(s) for s in nxt):
            optimum = t + 1
            goal_states = sorted(s for s in nxt if goal(s))

    witness: List[Action] = []
    witness_states: List[State] = []
    if optimum is not None and goal_states:
        target = lexmin_goal_state(r, initial, goal_states, parents)
        chain_states: List[State] = [target]
        chain_actions: List[Action] = []
        cur = target
        while cur != initial:
            prev, act = parents[cur]
            chain_actions.append(act)
            chain_states.append(prev)
            cur = prev
        chain_actions.reverse()
        chain_states.reverse()
        witness = chain_actions
        witness_states = chain_states

    return BfsResult(
        rules=r,
        initial=initial,
        optimum=optimum,
        layers=layers,
        parents=parents,
        goal_states=goal_states,
        witness=witness,
        witness_states=witness_states,
        transitions=transitions,
    )


def lexmin_goal_state(
    r: Rules,
    initial: State,
    goal_states: Sequence[State],
    parents: Dict[State, Tuple[State, Action]],
) -> State:
    """Pick a deterministic goal state: smallest path under lexicographic order.

    Deterministic only; it does not affect earliest-goal optimality.
    """
    best: Optional[Tuple[Tuple[Action, ...], State]] = None
    for g in goal_states:
        chain_actions: List[Action] = []
        cur = g
        while cur != initial:
            prev, act = parents[cur]
            chain_actions.append(act)
            cur = prev
        chain_actions.reverse()
        cand = (tuple(chain_actions), g)
        if best is None or cand[0] < best[0]:
            best = cand
    assert best is not None
    return best[1]


def replay(r: Rules, initial: State, actions: Sequence[Action]) -> List[State]:
    """Replay an action sequence; returns states at ticks 0..len(actions)."""
    states = [initial]
    check_state(r, initial)
    cur = initial
    for a in actions:
        if goal(cur):
            raise IllegalAction("cannot act in a goal state")
        cur = step(r, cur, a)
        states.append(cur)
    return states


# ---------------------------------------------------------------------------
# 3. Enumeration oracle: all legal action sequences of length t (no dedupe).
#    It deliberately reuses `step`/`legal_actions`; the independence is only
#    from the BFS layer bookkeeping, not from the transition semantics.
# ---------------------------------------------------------------------------


def brute_force_sequences(
    r: Rules, initial: State, length: int
) -> Iterator[Tuple[Tuple[Action, ...], State]]:
    """Yield every legal sequence of exactly `length` ticks and its final state."""
    if length == 0:
        yield (), initial
        return
    for acts, s in brute_force_sequences(r, initial, length - 1):
        if goal(s):
            continue
        for a in legal_actions(r, s):
            yield acts + (a,), step(r, s, a)


def brute_force_layer(r: Rules, initial: State, length: int) -> List[State]:
    """All states reachable in EXACTLY `length` ticks (no dedupe across ticks)."""
    return sorted({s for _, s in brute_force_sequences(r, initial, length)})


def optimal_sequences(r: Rules, initial: State, ticks: int) -> List[Tuple[Action, ...]]:
    """Every legal action sequence of exactly `ticks` ticks that ends in a goal."""
    return [acts for acts, s in brute_force_sequences(r, initial, ticks) if goal(s)]


def exact_step_frontiers(r: Rules, initial: State, max_ticks: int) -> List[List[State]]:
    """Lean-core notion: states reachable in EXACTLY t ticks (revisits allowed).

    This is what `Civ6Verify/Reachability/Finite.lean` computes as `Frontier M t`.
    """
    return [brute_force_layer(r, initial, t) for t in range(max_ticks + 1)]


def brute_force_distance_layers(
    r: Rules, initial: State, max_ticks: int
) -> List[List[State]]:
    """Distance layers computed only from exact-length reachability sets.

    dist(s) = min{t : s reachable in exactly t ticks}. This is an oracle that
    is independent of the BFS dedupe logic, including its bookkeeping.
    """
    out: List[List[State]] = []
    seen: set = set()
    for t in range(max_ticks + 1):
        exact = set(brute_force_layer(r, initial, t))
        out.append(sorted(exact - seen))
        seen |= exact
    return out


# ---------------------------------------------------------------------------
# 4. Candidate report + fixture generation.
# ---------------------------------------------------------------------------


def build_candidate(max_ticks: int = 8) -> BfsResult:
    return bfs(default_rules(), INITIAL_STATE, max_ticks)


def candidate_document(result: BfsResult) -> Dict[str, Any]:
    """Machine-readable candidate summary (still untrusted; no Civ6 claim)."""
    r = result.rules
    layer_counts = result.layer_counts()
    return {
        "fixtureId": FIXTURE_ID,
        "kind": "candidate-search-result",
        "trusted": False,
        "note": (
            "Python output. Candidate only; it establishes nothing by itself. "
            "Synthetic benchmark, not Civilization VI."
        ),
        "rulesDigest": rules_digest(r),
        "initialState": state_to_json(result.initial),
        "earliestGoalTick": result.optimum,
        "witness": [list(a) for a in result.witness],
        "witnessStates": [state_to_json(s) for s in result.witness_states],
        "layerCounts": layer_counts,
        "layerDigests": result.layer_digests(),
        "distanceLayerCounts": layer_counts,
        "distanceLayerDigests": result.layer_digests(),
        "exactStepFrontierCounts": [
            len(layer) for layer in exact_step_frontiers(r, result.initial, len(layer_counts) - 1)
        ],
        "exactStepFrontierDigests": [
            layer_digest(layer)
            for layer in exact_step_frontiers(r, result.initial, len(layer_counts) - 1)
        ],
        "distinctStatesTotal": sum(layer_counts),
        "expandedTransitions": result.transitions,
        "goalStatesAtOptimum": [state_to_json(s) for s in result.goal_states],
        "goalStateKeysAtOptimum": [state_key(s) for s in result.goal_states],
        "optimalSequenceCount": (
            len(optimal_sequences(result.rules, result.initial, result.optimum))
            if result.optimum is not None
            else 0
        ),
        "goalStatesInEarlierLayers": sum(
            1
            for t, layer in enumerate(result.layers)
            if result.optimum is not None and t < result.optimum
            for s in layer
            if goal(s)
        ),
        "maxFood": {str(p): r.max_food(p) for p in range(r.pop_min, r.pop_max + 1)},
    }


def state_to_json(s: State) -> Dict[str, int]:
    return {
        "pop": s[0],
        "food": s[1],
        "production": s[2],
        "settlersCompleted": s[3],
    }


def rules_digest(r: Rules) -> str:
    """Digest of the actual rule fields (works for perturbed rule sets too)."""
    payload = json.dumps(asdict(r), sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


def fixture_document(result: BfsResult) -> Dict[str, Any]:
    """The frozen spec: exact rules, initial state, goal, expected candidate."""
    r = result.rules
    cand = candidate_document(result)
    return {
        "fixtureId": FIXTURE_ID,
        "version": 0,
        "kind": "synthetic-benchmark",
        "synthetic": True,
        "civ6Model": False,
        "disclaimer": (
            "Fully synthetic. Growth thresholds, yields, settler cost and the "
            "round order are invented for proof-engineering. Nothing here is a "
            "Civilization VI formula, value, or optimum, and no claim about the "
            "real game follows from any number in this file."
        ),
        "purpose": (
            "A tiny, exhaustive-state benchmark whose rules Lean can re-implement "
            "and decide for all t (pop<=2, food<=7, production<=7, done in {0,1} "
            "=> at most 96 non-goal states)."
        ),
        "timeModel": {
            "tickSymbol": "t",
            "initialTick": 0,
            "tickSemantics": "one full settlement of all phases; state at t=k is after k settlements",
            "goalTick": "first t with settlersCompleted >= 1",
        },
        "rules": r.to_spec(),
        "roundOrder": [
            "1. read the citizen assignment chosen for this tick (from the state at the start of the tick)",
            (
                "2. compute yields from the PRE-growth population: "
                f"netFood = {r.farm_food}*nFarm + {r.mine_food}*nMine - {r.food_per_citizen}*pop, "
                f"gainedProduction = {r.farm_prod}*nFarm + {r.mine_prod}*nMine"
            ),
            (
                "3. food phase: food' = max("
                f"{r.food_floor}, food + netFood)  (floor: no starvation, no pop loss)"
            ),
            (
                "4. growth phase: while pop < "
                f"{r.pop_max} and food' >= T(pop): food' -= T(pop); pop += 1; "
                f"then if pop = {r.pop_max}: food' = min(food', T({r.pop_max})-1 = {r.max_food(r.pop_max)})"
            ),
            "5. production phase: raw = production + gainedProduction",
            (
                f"6. prerequisite gate: if pop < {r.settler_prereq_pop}, "
                f"production' = min(raw, {r.progress_cap}) and no completion is possible"
            ),
            (
                f"7. completion: if pop >= {r.settler_prereq_pop} and raw >= {r.settler_cost}: "
                f"settlersCompleted += 1, pop -= {r.settler_pop_cost}, "
                f"production' = {r.on_complete_prod}, food' = {r.on_complete_food}"
            ),
        ],
        "growthThresholds": {"1": 4, "2": 8},
        "actionEnumeration": {
            "definition": "A(p) = { (k, p-k) : 0 <= k <= p } for pop p, ordered by increasing k",
            "cardinality": "p+1 for a non-goal state; 0 in goal states",
            "totality": "every citizen works exactly one tile; two citizens may share a tile",
            "excluded": [
                "idle / unassigned citizens",
                "gold or faith purchase",
                "queue switch or alternate build items",
                "chops, improvements, trade, barbarians",
                "district/building/wonder/policy effects",
            ],
            "canonicalOrdering": "increasing citizens-on-farm, then mine count determined",
        },
        "initialState": state_to_json(result.initial),
        "initialGoal": goal(result.initial),
        "goal": GOAL_SPEC,
        "expected": {
            "syntheticEarliestGoalTick": cand["earliestGoalTick"],
            "witness": cand["witness"],
            "witnessStates": cand["witnessStates"],
            "layerCounts": cand["layerCounts"],
            "layerDigests": cand["layerDigests"],
            "reachableLayers": [
                sorted(state_key(st) for st in layer) for layer in result.layers
            ],
            "distanceLayerCounts": cand["distanceLayerCounts"],
            "distanceLayerDigests": cand["distanceLayerDigests"],
            "exactStepFrontiers": [
                sorted(state_key(st) for st in layer)
                for layer in exact_step_frontiers(r, result.initial, len(result.layers) - 1)
            ],
            "exactStepFrontierCounts": cand["exactStepFrontierCounts"],
            "exactStepFrontierDigests": cand["exactStepFrontierDigests"],
            "cartesianStateUpperBound": sum(
                (r.max_food(p) + 1) * r.settler_cost for p in range(r.pop_min, r.pop_max + 1)
            )
            * 2,  # done in {0,1}
            "completionReachableUpperBound": sum(
                (r.max_food(p) + 1) * r.settler_cost for p in range(r.pop_min, r.pop_max + 1)
            )
            + 1,  # any completion yields the single state (1,0,0,1)
            "completionStateKey": state_key(
                (r.pop_min, r.on_complete_food, r.on_complete_prod, 1)
            ),
            "distinctStatesTotal": cand["distinctStatesTotal"],
            "expandedTransitions": cand["expandedTransitions"],
            "goalStatesAtOptimum": cand["goalStatesAtOptimum"],
            "goalStateKeysAtOptimum": cand["goalStateKeysAtOptimum"],
            "optimalSequenceCount": cand["optimalSequenceCount"],
            "rulesDigest": cand["rulesDigest"],
            "trusted": False,
            "source": "search/synthetic.py (untrusted candidate; regenerate with --emit-fixture)",
        },
    }


def first_difference(a: Any, b: Any, path: str = "") -> Optional[str]:
    """Dotted path of the first structural difference between two JSON values.

    Returns ``None`` when the values are semantically equal. Used to make
    fixture mismatch reports actionable ("expected.exactStepFrontierCounts[3]").
    """
    if type(a) is not type(b):
        return path or "<root>"
    if isinstance(a, dict):
        for key in sorted(set(a) | set(b), key=str):
            sub = f"{path}.{key}" if path else str(key)
            if key not in a or key not in b:
                return sub
            diff = first_difference(a[key], b[key], sub)
            if diff is not None:
                return diff
        return None
    if isinstance(a, list):
        if len(a) != len(b):
            return f"{path} (length {len(a)} != {len(b)})"
        for index, (x, y) in enumerate(zip(a, b)):
            diff = first_difference(x, y, f"{path}[{index}]")
            if diff is not None:
                return diff
        return None
    return None if a == b else (path or "<root>")


def fixture_mismatches(
    doc: Dict[str, Any],
    result: Optional[BfsResult] = None,
    *,
    fresh: Optional[Dict[str, Any]] = None,
) -> List[str]:
    """Top-level fixture keys whose *parsed value* differs from a fresh build.

    Equality is JSON-semantic (Python object equality), not byte equality:
    whitespace, indentation and key order are irrelevant. All top-level keys are
    compared, including `fixtureId`, `version`, `disclaimer`, `purpose`,
    `timeModel` and any extra key; nothing is skipped.
    """
    if fresh is None:
        if result is None:
            raise TypeError("fixture_mismatches needs a BfsResult or a fresh document")
        fresh = fixture_document(result)
    return [k for k in sorted(set(doc) | set(fresh), key=str) if doc.get(k) != fresh.get(k)]


# ---------------------------------------------------------------------------
# 5. Human-readable report.
# ---------------------------------------------------------------------------


def format_report(result: BfsResult) -> str:
    r = result.rules
    out: List[str] = []
    out.append(f"SYNTHETIC benchmark {FIXTURE_ID} - NOT Civilization VI")
    out.append("=" * 66)
    out.append(
        f"rules: farm=(food {r.farm_food}, prod {r.farm_prod})  "
        f"mine=(food {r.mine_food}, prod {r.mine_prod})  "
        f"consumption={r.food_per_citizen}/citizen"
    )
    out.append(
        f"growth T(1)={r.threshold(1)}, T(2)={r.threshold(2)}; "
        f"settler cost={r.settler_cost}, prereq pop={r.settler_prereq_pop}, "
        f"pop cost={r.settler_pop_cost}"
    )
    out.append(f"initial state: {state_key(result.initial)} (goal={goal(result.initial)})")
    out.append("")
    out.append("layer | distance | exact-step | goal states")
    out.append("------+----------+------------+------------")
    exact = exact_step_frontiers(r, result.initial, len(result.layers) - 1)
    for t, layer in enumerate(result.layers):
        gcount = sum(1 for s in layer if goal(s))
        out.append(f"{t:5d} | {len(layer):8d} | {len(exact[t]):10d} | {gcount:11d}")
    out.append("")
    total = sum(result.layer_counts())
    non_goal = sum(1 for layer in result.layers for st in layer if not goal(st))
    out.append(f"distinct states overall: {total} (non-goal {non_goal})")
    out.append(f"expanded (state, action) pairs: {result.transitions}")
    out.append(f"earliest goal tick (candidate): {result.optimum}")
    out.append("")
    if result.optimum is not None:
        out.append("witness (tick: action -> resulting state):")
        for t, (a, s) in enumerate(zip(result.witness, result.witness_states[1:]), start=1):
            out.append(f"  t={t}: {action_key(a):>16s} -> {state_key(s)}")
        out.append("")
        out.append("per-tick table:")
        out.append("  t | pop | food | prod | done | assignment")
        out.append("  --+-----+------+------+------+-----------")
        for t, s in enumerate(result.witness_states):
            if t == 0:
                out.append(f"  {t:1d} | {s[0]:3d} | {s[1]:4d} | {s[2]:4d} | {s[3]:4d} | (initial)")
            else:
                a = result.witness[t - 1]
                out.append(
                    f"  {t:1d} | {s[0]:3d} | {s[1]:4d} | {s[2]:4d} | {s[3]:4d} | "
                    f"farm={a[0]},mine={a[1]}"
                )
    out.append("")
    out.append(
        "This is a synthetic candidate only: no Civ6 formula, value or optimum "
        "is asserted anywhere."
    )
    return "\n".join(out)


# ---------------------------------------------------------------------------
# 6. Internal test suite (owned here on purpose: one file, stdlib only).
# ---------------------------------------------------------------------------


class TestSyntheticModel(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.r = default_rules()
        cls.res = bfs(cls.r, INITIAL_STATE, 8)

    # -- fixture / spec consistency -------------------------------------
    def test_rules_roundtrip(self) -> None:
        spec = self.r.to_spec()
        self.assertEqual(Rules.from_spec(spec), self.r)
        self.assertTrue(spec["synthetic"])
        self.assertFalse(spec["civ6Model"])

    def test_fixture_file_matches_spec(self) -> None:
        doc = load_fixture()
        self.assertEqual(fixture_mismatches(doc, self.res), [])
        self.assertEqual(doc["rules"], RULES_SPEC)
        self.assertEqual(doc["initialState"], state_to_json(INITIAL_STATE))
        self.assertTrue(doc["synthetic"])
        self.assertFalse(doc["civ6Model"])
        exp = doc["expected"]
        self.assertEqual(exp["syntheticEarliestGoalTick"], self.res.optimum)
        self.assertEqual(exp["layerCounts"], self.res.layer_counts())
        self.assertEqual(exp["layerDigests"], self.res.layer_digests())
        self.assertEqual(exp["distinctStatesTotal"], sum(self.res.layer_counts()))
        self.assertEqual(exp["witness"], [list(a) for a in self.res.witness])
        self.assertEqual(exp["rulesDigest"], rules_digest(self.r))

    def test_fixture_checker_detects_tampering(self) -> None:
        doc = load_fixture()
        tampered = json.loads(json.dumps(doc))
        tampered["expected"]["syntheticEarliestGoalTick"] = 4
        self.assertEqual(fixture_mismatches(tampered, self.res), ["expected"])
        tampered = json.loads(json.dumps(doc))
        tampered["rules"]["tiles"][0]["production"] = 0
        self.assertIn("rules", fixture_mismatches(tampered, self.res))
        tampered = json.loads(json.dumps(doc))
        tampered["expected"]["layerCounts"] = [1, 2, 4, 6, 7]
        self.assertEqual(fixture_mismatches(tampered, self.res), ["expected"])

    def test_horizon_shorter_than_optimum_finds_no_goal(self) -> None:
        short = bfs(self.r, INITIAL_STATE, 4)
        self.assertIsNone(short.optimum)
        self.assertEqual(short.witness, [])
        self.assertFalse(any(goal(s) for layer in short.layers for s in layer))
        exact = bfs(self.r, INITIAL_STATE, 5)
        self.assertEqual(exact.optimum, self.res.optimum)
        self.assertEqual(exact.witness, self.res.witness)

    # -- goal marker -----------------------------------------------------
    def test_initial_state_is_not_goal(self) -> None:
        self.assertFalse(goal(INITIAL_STATE))
        self.assertEqual(INITIAL_STATE[3], 0)

    def test_goal_predicate_and_monotone_marker(self) -> None:
        self.assertTrue(goal((1, 0, 0, 1)))
        self.assertTrue(goal((2, 5, 3, 1)))
        # monotone along every BFS edge and every replay step
        for s in self.res.witness_states[:-1]:
            for a in legal_actions(self.r, s):
                self.assertGreaterEqual(step(self.r, s, a)[3], s[3])
        # no goal state is ever expanded: legal_actions is empty
        for s in self.res.goal_states:
            self.assertEqual(legal_actions(self.r, s), [])
        # completion count never exceeds 1 within the horizon
        self.assertTrue(all(s[3] in (0, 1) for layer in self.res.layers for s in layer))

    # -- action enumeration ---------------------------------------------
    def test_legal_action_enumeration_is_total_and_exact(self) -> None:
        for pop in (1, 2):
            s = (pop, 0, 0, 0)
            acts = legal_actions(self.r, s)
            self.assertEqual(acts, [(k, pop - k) for k in range(pop + 1)])
            self.assertEqual(len(acts), pop + 1)
            self.assertEqual(len(set(acts)), len(acts))
            for a in acts:
                self.assertEqual(a[0] + a[1], pop)
                self.assertTrue(a[0] >= 0 and a[1] >= 0)
            # every assignment outside the enumerated set is rejected
            for nfarm in range(-1, pop + 2):
                for nmine in range(-1, pop + 2):
                    if (nfarm, nmine) not in acts:
                        with self.assertRaises(IllegalAction):
                            step(self.r, s, (nfarm, nmine))

    def test_illegal_assignments_rejected(self) -> None:
        bad_states_actions = [
            ((1, 0, 0, 0), (1, 1)),   # over-assigned
            ((1, 0, 0, 0), (0, 0)),   # under-assigned
            ((2, 0, 0, 0), (3, -1)),  # negative
            ((1, 0, 0, 0), (-1, 2)),  # negative
            ((1, 0, 0, 0), (1, 0, 0)),  # wrong arity
            ((1, 0, 0, 0), "farm"),   # wrong type
            ((1, 0, 0, 0), (True, 0)),  # bool is not an int assignment
            ((1, 0, 0, 1), (1, 0)),   # acting after the goal
        ]
        for s, a in bad_states_actions:
            with self.assertRaises(IllegalAction):
                step(self.r, s, a)  # type: ignore[arg-type]

    def test_illegal_states_rejected(self) -> None:
        bad_states = [
            (0, 0, 0, 0),
            (3, 0, 0, 0),
            (1, 4, 0, 0),   # food above T(1)-1
            (2, 8, 0, 0),   # food above T(2)-1
            (1, -1, 0, 0),
            (1, 0, 8, 0),   # production above cost-1
            (1, 0, -1, 0),
            (1, 0, 0, 2),   # completion count out of range
        ]
        for s in bad_states:
            with self.assertRaises(IllegalState):
                check_state(self.r, s)
            with self.assertRaises(IllegalState):
                legal_actions(self.r, s)

    # -- transition semantics -------------------------------------------
    def test_growth_then_production_order(self) -> None:
        # pop 1, food 3 (one short), production 7: a farm tick grows to pop 2
        # AND completes the settler in the same tick -> order matters.
        s = (1, 3, 7, 0)
        self.assertEqual(step(self.r, s, (1, 0)), (1, 0, 0, 1))

    def test_prereq_gate_caps_progress(self) -> None:
        # pop 1 with 7/8 production: a mine tick cannot complete (needs pop 2)
        s = (1, 0, 7, 0)
        self.assertEqual(step(self.r, s, (0, 1)), (1, 0, 7, 0))
        # same production at pop 2 completes
        s2 = (2, 0, 7, 0)
        self.assertEqual(step(self.r, s2, (0, 2)), (1, 0, 0, 1))

    def test_food_floor_and_max_pop_cap(self) -> None:
        # 2 mines at pop 2: net -4 food, floor 0, +4 production
        self.assertEqual(step(self.r, (2, 0, 0, 0), (0, 2)), (2, 0, 4, 0))
        # surplus at max pop is discarded beyond T(2)-1 = 7
        self.assertEqual(step(self.r, (2, 5, 0, 0), (2, 0)), (2, 7, 2, 0))
        # growth carries the overflow and farms also add 1 production
        self.assertEqual(step(self.r, (1, 3, 0, 0), (1, 0)), (2, 0, 1, 0))

    def test_progress_cap_while_prereq_unmet_wastes_production(self) -> None:
        # at pop 1 production cannot be banked beyond cost-1 = 7
        self.assertEqual(step(self.r, (1, 0, 6, 0), (0, 1)), (1, 0, 7, 0))
        self.assertEqual(step(self.r, (1, 0, 7, 0), (0, 1)), (1, 0, 7, 0))

    def test_step_is_deterministic(self) -> None:
        for layer in self.res.layers:
            for s in layer:
                for a in legal_actions(self.r, s):
                    self.assertEqual(step(self.r, s, a), step(self.r, s, a))

    # -- search completeness --------------------------------------------
    def test_bfs_is_exact_against_bruteforce(self) -> None:
        # BFS layers are DISTANCE layers (earliest tick), so compare them with
        # distance layers derived from exact-length sequence enumeration, and
        # also check that every exact-length state appeared no later than t.
        oracle = brute_force_distance_layers(self.r, INITIAL_STATE, 6)
        self.assertEqual(len(self.res.layers), int(self.res.optimum) + 1)
        for t in range(len(self.res.layers)):
            self.assertEqual(
                sorted(self.res.layers[t]),
                oracle[t],
                msg=f"distance layer {t} mismatch vs full sequence enumeration",
            )
            known = {s for layer in oracle[: t + 1] for s in layer}
            self.assertTrue(set(brute_force_layer(self.r, INITIAL_STATE, t)) <= known)
        # earliest goal, computed without any dedupe at all
        goal_ticks = [
            t
            for t in range(0, 7)
            if any(goal(s) for _, s in brute_force_sequences(self.r, INITIAL_STATE, t))
        ]
        self.assertEqual(goal_ticks[0], self.res.optimum)
        # frozen candidate horizon for v0; also bounded by the search budget
        self.assertEqual(self.res.optimum, 5)
        self.assertLessEqual(int(self.res.optimum), 8)

    def test_exact_step_frontiers_match_lean_frontier_notion(self) -> None:
        # The Lean core computes exact-step frontiers (revisits kept), which are
        # NOT the same as the BFS distance layers used for the optimality search.
        opt = int(self.res.optimum)
        exact = exact_step_frontiers(self.r, INITIAL_STATE, opt)
        self.assertEqual([len(f) for f in exact], [1, 2, 4, 7, 9, 10])
        self.assertEqual(self.res.layer_counts(), [1, 2, 4, 6, 7, 7])
        for t, layer in enumerate(self.res.layers):
            self.assertLessEqual(set(layer), set(exact[t]))
            self.assertTrue(all(not goal(s) for s in exact[t]) if t < opt else True)

    def test_no_goal_before_optimum(self) -> None:
        self.assertIsNotNone(self.res.optimum)
        for t in range(0, int(self.res.optimum)):
            self.assertFalse(any(goal(s) for s in self.res.layers[t]), msg=f"goal at t={t}")

    def test_all_successors_are_covered_by_layers(self) -> None:
        # completeness of enumeration: every legal successor of a layer-t state
        # lands in some layer d <= t+1 (it may be an already-seen earlier state)
        known = [set(layer) for layer in self.res.layers]
        for t, layer in enumerate(self.res.layers):
            for s in layer:
                for a in legal_actions(self.r, s):
                    s2 = step(self.r, s, a)
                    self.assertTrue(
                        any(s2 in known[d] for d in range(min(t + 2, len(known)))),
                        msg=f"successor {state_key(s2)} of {state_key(s)} at t={t} escaped",
                    )

    def test_rules_contract_rejects_malformed_configurations(self) -> None:
        def mutated(mutator):
            spec = json.loads(json.dumps(RULES_SPEC))
            mutator(spec)
            return spec

        def set_settler(key, value):
            return lambda sp: sp["settler"].__setitem__(key, value)

        cases = {
            "cap contradicts cost": set_settler("productionProgressCap", 9),
            "cost zero": set_settler("cost", 0),
            "missing threshold": lambda sp: sp["growthThresholdByPop"].pop("2"),
            "zero threshold": lambda sp: sp["growthThresholdByPop"].__setitem__("1", 0),
            "threshold out of range": lambda sp: sp["growthThresholdByPop"].__setitem__("3", 12),
            "popMax below popMin": lambda sp: sp.__setitem__("popMax", 0),
            "negative mine yield": lambda sp: sp["tiles"][1].__setitem__("production", -2),
            "negative consumption": lambda sp: sp.__setitem__("foodPerCitizenPerTick", -1),
            "negative food floor": lambda sp: sp.__setitem__("foodFloor", -1),
            "prereq above popMax": set_settler("prereqPop", 3),
            "pop cost empties city": set_settler("populationCost", 2),
            "completion food too high": set_settler("onCompleteFood", 99),
            "completion prod above cap": set_settler("onCompleteProduction", 8),
            "string cost is not an int": set_settler("cost", "8"),
            "bool threshold is not an int": lambda sp: sp["growthThresholdByPop"].__setitem__("1", True),
            "renamed tile": lambda sp: sp["tiles"][0].__setitem__("id", "granary"),
            "extra tile": lambda sp: sp["tiles"].append({"id": "forest", "food": 1, "production": 1}),
            "duplicate tile": lambda sp: sp["tiles"].append(dict(sp["tiles"][0])),
            "missing tiles": lambda sp: sp.pop("tiles"),
            "missing settler block": lambda sp: sp.pop("settler"),
        }
        for name, mutate in cases.items():
            with self.subTest(case=name):
                with self.assertRaises(RuleSpecError):
                    Rules.from_spec(mutated(mutate))
        # the canonical spec itself is valid
        self.assertEqual(Rules.from_spec(RULES_SPEC), default_rules())

    def test_rule_contract_applies_to_dataclass_replace(self) -> None:
        with self.assertRaises(RuleSpecError):
            replace(self.r, on_complete_prod=8)  # above the derived cap
        with self.assertRaises(RuleSpecError):
            replace(self.r, settler_cost=0)
        with self.assertRaises(RuleSpecError):
            replace(self.r, pop_max=1)  # threshold table no longer matches
        valid = replace(self.r, settler_cost=9, food_per_citizen=3)
        self.assertEqual(valid.progress_cap, 8)
        self.assertEqual(valid.food_per_citizen, 3)

    def test_progress_cap_has_a_single_source(self) -> None:
        self.assertEqual(self.r.progress_cap, self.r.settler_cost - 1)
        self.assertEqual(self.r.max_progress(), self.r.progress_cap)
        # perturb the cost: the cap follows and step/check_state stay in sync
        r6 = replace(self.r, settler_cost=6, on_complete_prod=0)
        self.assertEqual(r6.progress_cap, 5)
        self.assertEqual(step(r6, (1, 0, 5, 0), (0, 1)), (1, 0, 5, 0))
        with self.assertRaises(IllegalState):
            check_state(r6, (1, 0, 6, 0))
        # the old desynchronisation is now unrepresentable: there is no cap field
        with self.assertRaises(TypeError):
            replace(self.r, progress_cap=9)  # type: ignore[call-arg]

    def test_to_spec_respects_instance_fields(self) -> None:
        self.assertEqual(self.r.to_spec(), RULES_SPEC)
        r0 = replace(self.r, farm_prod=0)
        spec0 = r0.to_spec()
        self.assertEqual(spec0["tiles"][0]["production"], 0)
        self.assertNotEqual(spec0, RULES_SPEC)
        self.assertEqual(Rules.from_spec(spec0), r0)
        r9 = replace(self.r, settler_cost=9)
        self.assertEqual(r9.to_spec()["settler"]["productionProgressCap"], 8)
        self.assertEqual(Rules.from_spec(r9.to_spec()).progress_cap, 8)
        # a spec that states a contradicting cap is rejected, not silently fixed
        bad = json.loads(json.dumps(spec0))
        bad["settler"]["productionProgressCap"] = 3
        with self.assertRaises(RuleSpecError):
            Rules.from_spec(bad)

    def test_fixture_comparison_is_semantic_and_covers_every_key(self) -> None:
        doc = load_fixture()
        self.assertEqual(fixture_mismatches(doc, self.res), [])
        self.assertEqual(fixture_mismatches(doc, fresh=fixture_document(self.res)), [])
        for key, value in (
            ("fixtureId", "synthetic-v0-typo"),
            ("version", 1),
            ("disclaimer", "tampered"),
            ("purpose", "tampered"),
        ):
            tampered = json.loads(json.dumps(doc))
            tampered[key] = value
            self.assertEqual(fixture_mismatches(tampered, self.res), [key], msg=key)
        nested = json.loads(json.dumps(doc))
        nested["timeModel"]["tickSymbol"] = "round"
        self.assertEqual(fixture_mismatches(nested, self.res), ["timeModel"])
        self.assertEqual(
            first_difference(nested["timeModel"], doc["timeModel"], "timeModel"),
            "timeModel.tickSymbol",
        )
        extra = json.loads(json.dumps(doc))
        extra["surprise"] = 1
        self.assertEqual(fixture_mismatches(extra, self.res), ["surprise"])
        self.assertIsNone(first_difference(doc["expected"], doc["expected"]))

    def test_missing_or_corrupt_fixture_is_an_error(self) -> None:
        missing = "/tmp/synthetic-v0-definitely-missing-fixture.json"
        if os.path.exists(missing):  # pragma: no cover
            os.unlink(missing)
        with self.assertRaises(FixtureError):
            load_fixture(missing)
        try:
            load_fixture(missing)
        except FixtureError:
            pass
        except unittest.SkipTest:  # pragma: no cover
            self.fail("a missing fixture must fail, not skip")
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
            fh.write("{not json")
            corrupt = fh.name
        self.addCleanup(os.unlink, corrupt)
        with self.assertRaises(FixtureError):
            load_fixture(corrupt)

    def test_farm_production_sensitivity_is_documented(self) -> None:
        # NOT part of the frozen fixture: a perturbation that guards the claim in
        # research/SYNTHETIC.md (farms bank production, so farm_prod=0 is slower).
        r0 = replace(self.r, farm_prod=0)
        self.assertEqual(bfs(r0, INITIAL_STATE, 8).optimum, 6)
        # and the naive "grow then produce" sum is wrong for the frozen rules
        self.assertEqual(self.res.optimum, 5)

    def test_no_pruning_bounds(self) -> None:
        # tiny state space by construction: |states| <= 2*8*8*2
        self.assertLessEqual(sum(self.res.layer_counts()), 2 * 8 * 8 * 2)
        self.assertEqual(self.res.layer_counts()[0], 1)

    # -- witness ---------------------------------------------------------
    def test_witness_replay(self) -> None:
        self.assertIsNotNone(self.res.optimum)
        states = replay(self.r, INITIAL_STATE, self.res.witness)
        self.assertEqual(states, self.res.witness_states)
        self.assertEqual(len(states) - 1, self.res.optimum)
        for s in states[:-1]:
            self.assertFalse(goal(s))
        self.assertTrue(goal(states[-1]))
        self.assertEqual(states[-1][3], 1)
        check_state(self.r, states[-1])
        # witness is a lexicographically minimal optimal sequence
        best = None
        for acts, s in brute_force_sequences(self.r, INITIAL_STATE, int(self.res.optimum)):
            if goal(s):
                if best is None or acts < best:
                    best = acts
        self.assertEqual(tuple(self.res.witness), best)

    def test_witness_tamper_detected(self) -> None:
        # dropping the last tick must lose the goal
        w = list(self.res.witness)
        self.assertNotEqual(replay(self.r, INITIAL_STATE, w[:-1])[-1][3], 1)
        # changing the last assignment to a legal but too-weak one must also fail
        weak = w[:-1] + [(1, 1)]
        self.assertEqual(replay(self.r, INITIAL_STATE, weak)[-1][3], 0)
        # changing the first move makes a later witness action illegal
        bad = list(w)
        bad[0] = (0, 1)
        with self.assertRaises(IllegalAction):
            replay(self.r, INITIAL_STATE, bad)


# ---------------------------------------------------------------------------
# 7. CLI.
# ---------------------------------------------------------------------------


class FixtureError(RuntimeError):
    """The frozen fixture is missing or not valid JSON.

    A missing fixture is an *error*, never a skipped test: without it the
    repository has no frozen spec to compare against.
    """


def load_fixture(path: Optional[str] = None) -> Dict[str, Any]:
    resolved = path or fixture_path()
    if not os.path.exists(resolved):
        raise FixtureError(
            f"missing frozen fixture: {resolved} "
            "(regenerate with `python3 search/synthetic.py --emit-fixture`)"
        )
    try:
        with open(resolved, "r", encoding="utf-8") as fh:
            doc = json.load(fh)
    except json.JSONDecodeError as exc:
        raise FixtureError(f"fixture {resolved} is not valid JSON: {exc}") from exc
    if not isinstance(doc, dict):
        raise FixtureError(f"fixture {resolved} must be a JSON object")
    return doc


def fixture_path() -> str:
    here = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(os.path.dirname(here), "fixtures", f"{FIXTURE_ID}.json")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true", help="print candidate JSON")
    parser.add_argument(
        "--emit-fixture",
        action="store_true",
        help="print the canonical fixture document (rules + expected candidate)",
    )
    parser.add_argument("--self-test", action="store_true", help="run internal tests")
    parser.add_argument(
        "--check-fixture",
        action="store_true",
        help="verify the frozen fixture file against this module",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestSyntheticModel)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if result.wasSuccessful() else 1

    if args.check_fixture:
        try:
            frozen = load_fixture()
        except FixtureError as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            return 2
        fresh = fixture_document(build_candidate(8))
        bad = fixture_mismatches(frozen, fresh=fresh)
        if not bad:
            print(
                f"OK: {fixture_path()} matches this module semantically "
                f"(all {len(fresh)} top-level keys; parsed-JSON equality, not byte equality)"
            )
            return 0
        print(f"MISMATCH: {fixture_path()} disagrees on: {', '.join(bad)}")
        for key in bad:
            detail = first_difference(frozen.get(key), fresh.get(key), key)
            print(f"  first difference at: {detail}")
        return 1

    res = build_candidate(8)
    if args.emit_fixture:
        print(json.dumps(fixture_document(res), indent=2, ensure_ascii=False))
        return 0
    if args.json:
        print(json.dumps(candidate_document(res), indent=2, ensure_ascii=False))
        return 0
    print(format_report(res))
    return 0


if __name__ == "__main__":
    sys.exit(main())
