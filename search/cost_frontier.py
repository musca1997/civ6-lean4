#!/usr/bin/env python3
"""Cost-dependent pop2-vs-pop3 strategy frontier (untrusted bounded search).

This module is an *empirical, executable* companion to ``search/mvp.py`` and
``mvp/LOWER-BOUND.md``.  It does not re-implement the settlement step: it
imports ``search/mvp.py`` and reuses the normative ``_step_prepared`` relation
with a locally built ``Prepared`` object so that the settler cost can be varied
outside the frozen {8000, 11000} fixture box.  Nothing here is a Civ6 fact and
nothing here is a proof of a general strategy theorem.

Question
--------
For which settler costs does a play that grows to population 3 complete a
Settler strictly earlier than any play that never grows to population 3?

Explicit definitions (all within the exact-step model of ``search/mvp.py``,
baseline theta, ``basket = zero``, growth_first, newCitizen = best):

* ``N_all(c)``  = least ``t`` with ``trained >= 1`` over all plays, population
  capped at 3 (population 4 is *forbidden* so that the comparison is exactly a
  pop-2 vs pop-3 question; see the note on pop 4 below).
* ``N_p2(c)``   = least ``t`` with ``trained >= 1`` over plays whose every
  state has ``pop <= 2`` ("forbid growing to pop 3").
* ``N_p3(c)``   = least ``t`` with ``trained >= 1`` over plays that reach
  ``pop = 3`` at some *pre-completion* time ``t < g``, where ``g`` is the first
  completion time.  The pre-completion flag is set only from the pre-state of a
  step (``next_flag = flag or pre.pop == 3``), so the population drop caused by
  the completion itself can never make a trajectory count as pop-3.  This is
  the "avoid drop after completion" convention.
* ``pop3_helps(c) := N_p3(c) < N_p2(c)``.

The first cost where ``pop3_helps`` holds is reported together with witnesses.
Because the search is a finite sample over a cost grid, this is *not* a claim
that the property is monotone or that there is a universal crossover interval;
the doc ``mvp/COST-FRONTIER.md`` states exactly what is and is not inferred.

Boundedness
-----------
The search horizon is ``N2_upper(c) = 7 + ceil(c / 630)``, the exact pop-2
completion time (``PH,P`` credits 630 every step after the 1->2 growth).  If no
pop-3 completion appears by then, then ``N_p3(c) >= N_p2(c)`` within the search
box, so no larger horizon is needed to refute "pop 3 helps" at that cost.
Layer dedup is exact *within* a layer (the same convention as ``frontier_search``),
over the product state ``(pop, food, prog, trained, precompletion_pop3)``.

Usage
-----
    python3 search/cost_frontier.py --self-test
    python3 search/cost_frontier.py --scan 8000 16000 500
    python3 search/cost_frontier.py --cost 11000
    python3 search/cost_frontier.py --find-crossover
    python3 search/cost_frontier.py --write-fixture
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

# --- import the independent model module without touching it -----------------
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import mvp  # noqa: E402  (search/mvp.py, read-only reuse)

FIXTURE_PATH = ROOT / "fixtures" / "cost-frontier.json"
POP_CAP = 3  # isolate the pop-2 vs pop-3 question; pop 4 is forbidden here
COST_QUANTUM = 100  # mvp cost axis is settlerCost * 100
POP2_RATE = 630  # max credited q at pop 2 with no growth (GH,PH or PH,P)
POP3_SLACK = 8  # extra layers used to *report* N_p3 when it is > N_p2
UNRESTRICTED_POP_CAP = 4  # used only for the pop-4 side check

Key = Tuple[mvp.State, bool]


# ---------------------------------------------------------------------------
# Lifting the cost parameter
# ---------------------------------------------------------------------------


def prepared_for_cost(cost: int) -> mvp.Prepared:
    """Build a ``Prepared`` with an arbitrary cost, reusing the baseline axes.

    ``mvp.prepare`` validates the settler cost against the frozen {8000, 11000}
    box.  The cost is the only axis that affects completion; all multiplier /
    threshold data is copied verbatim from the validated baseline ``Prepared``,
    so the normative step relation ``mvp._step_prepared`` is used unchanged.
    """
    if cost <= 0:
        raise ValueError(f"cost must be a positive integer, got {cost}")
    base = mvp.prepare(mvp.baseline_theta())
    theta = base.theta._replace(settler_cost=cost)
    return mvp.Prepared(
        theta=theta,
        cost=cost,
        order=base.order,
        new_citizen=base.new_citizen,
        stock=base.stock,
        basket=base.basket,
        rounding=base.rounding,
        T=base.T,
        gm=base.gm,
        pm=base.pm,
    )


def step_lifted(p: mvp.Prepared, s: mvp.State, a: mvp.Action) -> Optional[mvp.State]:
    """The normative step, borrowed verbatim from ``search/mvp.py``."""
    out = mvp._step_prepared(p, s, a)
    assert out is None or isinstance(out, mvp.State)
    return out  # type: ignore[return-value]


def n2_upper(cost: int) -> int:
    """Exact pop-2 completion time 7 + ceil(cost/630) for this sigma."""
    return 7 + -(-cost // POP2_RATE)


def credit_envelope(horizon: int = 44, flag_mode: str = "growth") -> Dict[str, Any]:
    """Max cumulative credit at each completion step, with *no* cost cutoff.

    Running the step relation with a huge cost (so completion never fires)
    turns the reachability graph into its cost-free form.  For each step ``t``:

    * ``M2[t]`` = max credit a strict pop-2 play can have at step ``t``
      (``630*(t-7)``, first credited step ``t = 8``);
    * ``M3[t]`` = max credit a play that reaches pop 3 can have at a
      ``SETTLER`` step ``t`` (the credited ``q`` is included).  With
      ``flag_mode = "growth"`` (default) the completing step may itself be the
      growth 2 -> 3 step; with ``flag_mode = "standing"`` a standing pop-3
      state must already exist strictly before the completing step.

    Then ``N_p2(c) = min {t : M2[t] >= c}`` and ``N_p3(c) = min {t : M3[t] >= c}``,
    so the envelope determines the first helping cost exactly (within the
    envelope horizon) without one BFS per cost.
    """
    assert flag_mode in ("growth", "standing"), flag_mode
    p = prepared_for_cost(100_000_000)
    layer: set[Key] = {(mvp.START, False)}
    m3: List[Optional[int]] = [None] * (horizon + 1)
    m3[0] = 0
    max_pop_seen = 1
    for t in range(1, horizon + 1):
        best: Optional[int] = None
        # advance set computed together with the completing-credit scan
        nxt: set[Key] = set()
        par: Dict[Key, Tuple[Key, mvp.Action]] = {}
        for key in layer:
            s, flag = key
            for a in mvp.structural_actions(s.pop):
                traced = mvp._step_prepared(p, s, a, trace=True)
                if traced is None:
                    continue
                ns, info = traced
                target = s.pop + 1 if info.grew else s.pop
                if target > POP_CAP or ns.pop > POP_CAP:
                    continue
                if ns.pop > max_pop_seen:
                    max_pop_seen = ns.pop
                grew3 = info.grew and target >= 3
                if flag_mode == "growth":
                    eligible = flag or grew3
                    nflag = flag or grew3
                else:  # standing: a pop-3 state at time <= t-1 must exist
                    eligible = flag or s.pop == 3
                    nflag = flag or s.pop == 3
                if eligible and a.build == "SETTLER":
                    credit = s.prog + info.credited
                    if best is None or credit > best:
                        best = credit
                nkey: Key = (ns, nflag)
                nxt.add(nkey)
                if nkey not in par:
                    par[nkey] = (key, a)
        m3[t] = best if best is not None else (m3[t - 1] or 0)
        layer = nxt
        if not layer:
            break
    m2 = [0] * (horizon + 1)
    for t in range(8, horizon + 1):
        m2[t] = POP2_RATE * (t - 7)
    # first cost whose pop-3 line is strictly earlier than the pop-2 line
    first_helping: Optional[int] = None
    max_c = int(m3[horizon] or 0)
    for c in range(1, max_c + 1):
        n3 = next((t for t in range(1, horizon + 1) if (m3[t] or 0) >= c), None)
        n2 = next((t for t in range(1, horizon + 1) if m2[t] >= c), None)
        if n3 is not None and n2 is not None and n3 < n2:
            first_helping = c
            break
    return {
        "horizon": horizon,
        "flagMode": flag_mode,
        "maxPopSeen": max_pop_seen,
        "M2": m2,
        "M3": [int(x) if x is not None else None for x in m3],
        "firstHelpingCostExact": first_helping,
        "maxCostSampled": max_c,
        "note": (
            "Envelope from one cost-free BFS with the population capped at 3. "
            "M3/M2 are max credited progress at the completing step; the first "
            "cost with N_p3 < N_p2 is exact inside the envelope horizon."
        ),
    }


# ---------------------------------------------------------------------------
# Bounded exact-layer search with a pre-completion pop-3 flag
# ---------------------------------------------------------------------------


def frontier(
    p: mvp.Prepared, horizon: int, pop_cap: int = POP_CAP, flag_mode: str = "growth"
) -> Dict[str, Any]:
    """Exact-layer BFS over ``(State, pop3_flag)``.

    ``flag_mode = "growth"`` sets the flag on a growth *event* whose target
    population is >= 3 (``growth_first``).  This is the primary definition: a
    SETTLER that completes on the same step that grows 2 -> 3 ends at pop 2
    again, so counting only post-states would let such a play pass as
    "pop 2 only"; the completion drop never sets the flag.

    ``flag_mode = "standing"`` sets the flag when a *pre-state* already has
    ``pop = 3`` (a standing pop-3 state strictly before the completion).  It is
    reported only as a secondary, stricter reading; the strict pop-2 class is
    always the growth-event class.
    """
    assert p.order == "growth_first", "cost frontier is defined for the baseline growth_first order"
    assert flag_mode in ("growth", "standing"), flag_mode
    # Key = (state, a growth to pop >= 3 has already happened on this trajectory).
    # Flag-False goals are exactly the strict "never grow to pop 3" plays.
    start: Key = (mvp.START, False)
    layer: set[Key] = {start}
    parents: List[Dict[Key, Optional[Tuple[Key, mvp.Action]]]] = [{start: None}]
    layer_sizes: List[int] = [1]
    max_pop_seen = 1
    cap_blocked = 0
    first: Dict[str, Optional[int]] = {"any": None, "p2": None, "p3": None}
    goals: Dict[str, Optional[Key]] = {"any": None, "p2": None, "p3": None}
    states_visited = 1
    t0 = time.time()

    for t in range(horizon):
        nxt: set[Key] = set()
        par: Dict[Key, Tuple[Key, mvp.Action]] = {}
        for key in sorted(layer):
            s, flag = key
            for a in mvp.structural_actions(s.pop):
                traced = mvp._step_prepared(p, s, a, trace=True)
                if traced is None:
                    continue
                ns, info = traced  # (post state, StepInfo)
                target = s.pop + 1 if info.grew else s.pop
                if target > pop_cap or ns.pop > pop_cap:
                    cap_blocked += 1
                    continue
                if ns.pop > max_pop_seen:
                    max_pop_seen = ns.pop
                grew3 = info.grew and target >= 3
                if flag_mode == "growth":
                    nflag = flag or grew3
                else:  # standing: the pre-state is already pop 3
                    nflag = flag or s.pop == 3
                nkey: Key = (ns, nflag)
                nxt.add(nkey)
                if nkey not in par:
                    par[nkey] = (key, a)
        t_goal = t + 1
        for nkey in sorted(nxt):
            ns, nf = nkey
            if ns.trained >= 1:
                if first["any"] is None:
                    first["any"] = t_goal
                    goals["any"] = nkey
                cls = "p3" if nf else "p2"
                if first[cls] is None:
                    first[cls] = t_goal
                    goals[cls] = nkey
        layer_sizes.append(len(nxt))
        states_visited += len(nxt)
        parents.append(par)
        layer = nxt
        if not layer:
            break

    witnesses = {
        cls: _reconstruct(parents, goals[cls], first[cls])
        for cls in ("any", "p2", "p3")
    }
    return {
        "horizon": horizon,
        "popCap": pop_cap,
        "flagMode": flag_mode,
        "nAny": first["any"],
        "nP2": first["p2"],
        "nP3": first["p3"],
        "maxPopSeen": max_pop_seen,
        "pop4TransitionsBlocked": cap_blocked,
        "layerSizes": layer_sizes,
        "layersReached": len(layer_sizes) - 1,
        "statesVisited": states_visited,
        "finalLayerSize": layer_sizes[-1],
        "witnesses": witnesses,
        "elapsedSeconds": round(time.time() - t0, 3),
    }


def _reconstruct(
    parents: List[Dict[Key, Optional[Tuple[Key, mvp.Action]]]],
    goal: Optional[Key],
    goal_time: Optional[int],
) -> Optional[List[Dict[str, Any]]]:
    if goal is None or goal_time is None:
        return None
    key = goal
    rows: List[Dict[str, Any]] = []
    for t in range(goal_time, 0, -1):
        entry = parents[t].get(key)
        if entry is None:  # pragma: no cover - a first-goal key is always parented
            raise mvp.ModelError(f"missing parent for first-goal key at t={t}")
        prev, action = entry
        rows.append({
            "t": t,
            "pre": list(prev[0]),
            "prePop3": prev[1],
            "action": _action_ids(action),
            "post": list(key[0]),
            "postPop3": key[1],
        })
        key = prev
    rows.reverse()
    return rows


def _action_ids(action: mvp.Action) -> Dict[str, Any]:
    return {
        "work": [mvp.TILE_IDS[i] for i in range(mvp.N_TILES) if (action.work >> i) & 1],
        "workMask": action.work,
        "extra": mvp.TILE_IDS[action.extra] if action.extra is not None else None,
        "build": action.build,
    }


# ---------------------------------------------------------------------------
# Cost evaluation and grid scan
# ---------------------------------------------------------------------------


def evaluate(
    cost: int,
    *,
    pop_cap: int = POP_CAP,
    keep_witnesses: bool = True,
    report_horizon: Optional[int] = None,
    include_standing: bool = False,
) -> Dict[str, Any]:
    p = prepared_for_cost(cost)
    n2_horizon = n2_upper(cost)
    if report_horizon is None:
        report_horizon = n2_horizon + POP3_SLACK
    horizon = max(n2_horizon, int(report_horizon))
    res = frontier(p, horizon, pop_cap=pop_cap, flag_mode="growth")
    nP2 = res["nP2"]
    nP3 = res["nP3"]
    # The frontier decision only needs t <= N_p2; a strictly earlier pop-3
    # completion is always found by horizon max(n2_horizon, report_horizon).
    helps = nP3 is not None and nP2 is not None and nP3 < nP2
    row: Dict[str, Any] = {
        "cost": cost,
        "costAxis": cost // COST_QUANTUM,
        "horizon": horizon,
        "n2Horizon": n2_horizon,
        "n2Upper": n2_horizon,
        "nP2": nP2,
        "nP3": nP3,
        "nAny": res["nAny"],
        "pop3Helps": helps,
        "maxPopSeen": res["maxPopSeen"],
        "pop4TransitionsBlocked": res["pop4TransitionsBlocked"],
        "finalLayerSize": res["finalLayerSize"],
        "elapsedSeconds": res["elapsedSeconds"],
    }
    if keep_witnesses:
        row["witnesses"] = res["witnesses"]
    if include_standing:
        stand = frontier(p, horizon, pop_cap=pop_cap, flag_mode="standing")
        nP3s = stand["nP3"]
        row["nP3Standing"] = nP3s
        row["pop3HelpsStanding"] = nP3s is not None and nP2 is not None and nP3s < nP2
        if keep_witnesses:
            row["witnessStandingP3"] = stand["witnesses"]["p3"]
    return row


def scan(costs: List[int], *, keep_witnesses: bool = False, verbose: bool = False) -> List[Dict[str, Any]]:
    out: List[Dict[str, Any]] = []
    t0 = time.time()
    for i, cost in enumerate(costs, start=1):
        # For a grid decision only the N_p2 horizon is needed: an earlier pop-3
        # completion is always below N_p2, and a later one cannot help.
        row = evaluate(
            cost,
            keep_witnesses=keep_witnesses,
            report_horizon=(n2_upper(cost) if not keep_witnesses else None),
        )
        out.append(row)
        if verbose and (i % 5 == 0 or i == len(costs)):
            print(f"  scan {i}/{len(costs)} cost={cost} elapsed={time.time()-t0:.1f}s", file=sys.stderr)
    return out


def first_helping_cost(lo: int, hi: int, step: int = COST_QUANTUM) -> Dict[str, Any]:
    """Coarse scan then exact refinement on a cost grid.

    The grid is only a sample: "first on this grid" is reported, not a claim of
    a universal threshold.  Refinement halves the gap until consecutive grid
    points differ by one quantum, so the returned cost is the exact first
    helping cost *on the scanned quantum grid* if the property is monotone
    there; the fixture records the neighbouring non-helping cost as evidence.
    """
    assert lo % step == 0 and hi % step == 0 and lo < hi
    t0 = time.time()
    costs = list(range(lo, hi + 1, step))
    rows = scan(costs, keep_witnesses=False)
    by_cost = {r["cost"]: r for r in rows}
    helps = [r["cost"] for r in rows if r["pop3Helps"]]
    result: Dict[str, Any] = {
        "gridLo": lo,
        "gridHi": hi,
        "gridStep": step,
        "gridSize": len(costs),
        "helpingCosts": helps,
        "nonHelpingCosts": [r["cost"] for r in rows if not r["pop3Helps"]],
        "elapsedSeconds": round(time.time() - t0, 3),
    }
    if not helps:
        result["firstHelpingCost"] = None
        result["note"] = "no helping cost on this grid (sample, not a global negative)"
        return result
    first = helps[0]
    # refine between the previous non-helping grid point and the first helping one
    prev_helps = [r["cost"] for r in rows if r["cost"] < first and not r["pop3Helps"]]
    if not prev_helps:
        result["firstHelpingCost"] = first
        result["refined"] = False
        return result
    last_nonhelp = max(prev_helps)
    a, b = last_nonhelp, first  # a does not help, b helps
    while b - a > COST_QUANTUM:
        mid = ((a + b) // 2)
        mid -= mid % COST_QUANTUM
        if mid <= a:
            mid = a + COST_QUANTUM
        if mid >= b:
            break
        r = evaluate(mid, keep_witnesses=False)
        if r["pop3Helps"]:
            b = mid
        else:
            a = mid
    refined_rows = scan([a, b], keep_witnesses=True)
    result["firstHelpingCost"] = b
    result["lastNonHelpingCost"] = a
    result["boundary"] = refined_rows
    result["refined"] = True
    result["elapsedSeconds"] = round(time.time() - t0, 3)
    return result


# ---------------------------------------------------------------------------
# Pop-4 side check (honesty about the restriction)
# ---------------------------------------------------------------------------


def helping_windows(m2: List[int], m3: List[Optional[int]]) -> List[Dict[str, int]]:
    """Costs for which the pop-3 line is strictly earlier, from M2/M3 intervals."""
    windows: List[Dict[str, int]] = []
    for t in range(1, len(m2)):
        lo = max(int(m3[t - 1] or 0), m2[t]) + 1
        hi = int(m3[t] or 0)
        if hi >= lo:
            windows.append({"completionTime": t, "loCost": lo, "hiCost": hi})
    return windows


def pop4_side_check(cost: int, extra_horizon: int = 12) -> Dict[str, Any]:
    """Does the *unrestricted* pop<=4 model reach pop 4 near this cost?

    This is deliberately separate from the frontier comparison: it documents
    that the pop<=3 restriction is a real restriction at large horizons, so the
    crossover is not silently promoted to a global statement.
    """
    p = prepared_for_cost(cost)
    horizon = n2_upper(cost) + extra_horizon
    try:
        res = frontier(p, horizon, pop_cap=UNRESTRICTED_POP_CAP)
        return {
            "cost": cost,
            "horizon": horizon,
            "unrestrictedMaxPopSeen": res["maxPopSeen"],
            "unrestrictedNAny": res["nAny"],
            "unrestrictedNP3": res["nP3"],
            "popBeyondCap3TransitionsBlocked": res["pop4TransitionsBlocked"],
        }
    except mvp.ModelError as exc:  # pragma: no cover - outside the MVP table
        return {"cost": cost, "horizon": horizon, "error": str(exc)}


# ---------------------------------------------------------------------------
# Self tests
# ---------------------------------------------------------------------------


def self_test() -> Dict[str, Any]:
    failures: List[str] = []

    def check(name: str, cond: bool, detail: Any = None) -> None:
        if not cond:
            failures.append(f"{name}: {detail}")

    # 1. Lifting agrees with the public model at the two frozen costs.
    for axis, cost in ((80, 8000), (110, 11000)):
        b_theta = mvp.baseline_theta()._replace(settler_cost=cost)
        p = prepared_for_cost(cost)
        check(f"prepare-equivalence-{axis}", p.T == mvp.prepare(b_theta).T and p.gm == mvp.prepare(b_theta).gm)
        layer = {mvp.START}
        seen = 0
        for _ in range(6):
            nxt = set()
            for s in sorted(layer):
                for a in mvp.structural_actions(s.pop):
                    a1 = step_lifted(p, s, a)
                    a2 = mvp.step(b_theta, s, a)
                    check(f"step-equiv-{axis}", a1 == a2, (s, a, a1, a2))
                    seen += 1
                    if a1 is not None:
                        nxt.add(a1)
            layer = nxt
        check(f"step-equiv-count-{axis}", seen > 0, seen)

    # 2. Reproduce the documented 20 / 25 baselines and pop-3 non-help at 80/110.
    r80 = evaluate(8000)
    r110 = evaluate(11000)
    check("baseline80-N", r80["nAny"] == 20, r80)
    check("baseline110-N", r110["nAny"] == 25, r110)
    check("cost80-pop3-no-help", r80["pop3Helps"] is False, r80["nP3"])
    check("cost110-pop3-no-help", r110["pop3Helps"] is False, r110["nP3"])
    check("cost80-Np3-22", r80["nP3"] == 22, r80["nP3"])
    check("cost110-Np3-26", r110["nP3"] == 26, r110["nP3"])

    # 3. The pop-2 upper bound is attained (nP2 == 7 + ceil(cost/630)).
    for cost in (8000, 12100, 20000):
        r = evaluate(cost, keep_witnesses=False)
        check(f"nP2-formula-{cost}", r["nP2"] == n2_upper(cost), r)

    # 4. Witness replay: every witness row is legal and the final state is a goal.
    for cost in (8000, 11000):
        r = evaluate(cost, keep_witnesses=True)
        for cls in ("p2", "p3"):
            rows = r["witnesses"][cls]
            if rows is None:
                continue
            cur = mvp.START
            for row in rows:
                a = mvp.Action(
                    row["action"]["workMask"],
                    mvp._tile_index(row["action"]["extra"]),
                    row["action"]["build"],
                )
                check(f"witness-pre-{cost}-{cls}", tuple(row["pre"]) == cur, (row, cur))
                nxt = mvp.step(mvp.baseline_theta()._replace(settler_cost=cost), cur, a)
                check(f"witness-legal-{cost}-{cls}", nxt is not None, (cur, a))
                check(f"witness-post-{cost}-{cls}", list(nxt) == row["post"], (nxt, row))
                cur = nxt  # type: ignore[assignment]
            check(f"witness-goal-{cost}-{cls}", cur.trained >= 1, cur)
            if cls == "p3":
                check(f"witness-p3flag-{cost}", rows[-1]["postPop3"] is True, rows[-1])

    # 5. Pop-3 is genuinely forbidden in the p2 class: every pre-state pop <= 2.
    for cost in (8000, 11000):
        rows = evaluate(cost, keep_witnesses=True)["witnesses"]["p2"]
        if rows is not None:
            check(f"p2-witness-pop-{cost}", all(row["pre"][0] <= 2 for row in rows), rows)

    # 6. Determinism of one evaluated row.
    check("determinism", evaluate(11000, keep_witnesses=False)["nAny"] == r110["nAny"])

    # 7. Cost frontier: global envelope and direct boundary checks.
    env_g = credit_envelope(44, "growth")
    env_s = credit_envelope(44, "standing")
    check("envelope-growth-first", env_g["firstHelpingCostExact"] == 13861, env_g["firstHelpingCostExact"])
    check("envelope-standing-first", env_s["firstHelpingCostExact"] == 13861, env_s["firstHelpingCostExact"])
    r_lo = evaluate(13860, keep_witnesses=False, include_standing=True)
    r_hi = evaluate(13861, keep_witnesses=True, include_standing=True)
    check("just-below-no-help", (r_lo["nP2"], r_lo["nP3"], r_lo["pop3Helps"]) == (29, 29, False), r_lo)
    check("exact-first-helps", (r_hi["nP2"], r_hi["nP3"], r_hi["pop3Helps"]) == (30, 29, True), r_hi)
    check("exact-first-helps-standing", r_hi["pop3HelpsStanding"] is True, r_hi.get("nP3Standing"))
    # The first helping growth witness completes on the very step it grows.
    w3 = r_hi["witnesses"]["p3"]
    check("first-helping-p2-credit-735", w3[-1]["post"][2] == 104, w3[-1])
    check("first-helping-pre-state-pop2", w3[-1]["pre"][0] == 2, w3[-1])
    check("first-helping-post-flag", w3[-1]["postPop3"] is True, w3[-1])

    return {"ok": not failures, "failures": failures, "checks": "see failures list"}


# ---------------------------------------------------------------------------
# Fixture
# ---------------------------------------------------------------------------


def check_fixture(path: Path = FIXTURE_PATH) -> Dict[str, Any]:
    """Replay the frozen fixture's witnesses and re-derive the boundary."""
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    assert data["fixtureId"] == "cost-frontier-v1"
    assert data["untrusted"] is True and data["gameFactClaim"] is False
    results: Dict[str, Any] = {}
    for label, entry in data["boundaryWitnesses"].items():
        cost = entry["cost"]
        p = prepared_for_cost(cost)
        checks: Dict[str, Any] = {}
        for wkey, cls in (("witnessP2", "p2"), ("witnessP3Growth", "p3"), ("witnessP3Standing", "p3")):
            rows = entry.get(wkey)
            if not rows:
                continue
            cur = mvp.START
            grew3 = False
            for row in rows:
                a = mvp.Action(
                    row["action"]["workMask"],
                    mvp._tile_index(row["action"]["extra"]),
                    row["action"]["build"],
                )
                traced = mvp._step_prepared(p, cur, a, trace=True)
                assert traced is not None, (label, wkey, row)
                nxt, info = traced
                assert tuple(row["pre"]) == cur, (label, wkey, row, cur)
                assert list(nxt) == row["post"], (label, wkey, nxt, row)
                target = cur.pop + 1 if info.grew else cur.pop
                if info.grew and target >= 3:
                    grew3 = True
                cur = nxt
            assert cur.trained >= 1, (label, wkey, cur)
            if cls == "p2":
                assert not grew3, (label, wkey, "pop-2 witness grew to pop 3")
            else:
                assert grew3, (label, wkey, "pop-3 witness never grew to pop 3")
            checks[wkey] = {"rows": len(rows), "final": list(cur), "grewToPop3": grew3}
        results[label] = {"cost": cost, "nP2": entry["nP2"], "nP3Growth": entry["nP3Growth"],
                          "nP3Standing": entry["nP3Standing"], "witnessChecks": checks}
    exact = int(data["envelopeGrowth"]["firstHelpingCostExact"])
    r_lo = evaluate(exact - 1, keep_witnesses=False)
    r_hi = evaluate(exact, keep_witnesses=False)
    assert r_lo["pop3Helps"] is False, r_lo
    assert r_hi["pop3Helps"] is True, r_hi
    return {"ok": True, "envelopeFirstHelping": exact, "boundary": results,
            "justBelow": {"cost": exact - 1, "nP2": r_lo["nP2"], "nP3": r_lo["nP3"]},
            "first": {"cost": exact, "nP2": r_hi["nP2"], "nP3": r_hi["nP3"]}}


def build_fixture() -> Dict[str, Any]:
    t0 = time.time()
    env_growth = credit_envelope(44, "growth")
    env_standing = credit_envelope(44, "standing")
    exact = int(env_growth["firstHelpingCostExact"])

    def grid_row(r: Dict[str, Any]) -> Dict[str, Any]:
        return {
            "cost": r["cost"],
            "costAxis": r["costAxis"],
            "horizon": r["horizon"],
            "nP2": r["nP2"],
            "nP3": r["nP3"],
            "pop3Helps": r["pop3Helps"],
            "maxPopSeen": r["maxPopSeen"],
        }

    grid_window = [grid_row(r) for r in scan(list(range(13700, 14101, 100)))]
    grid_early = [grid_row(r) for r in scan(list(range(8000, 13801, 1000)))]
    grid_late = [grid_row(r) for r in scan([17000, 17011, 17200, 18000, 20000])]

    boundary: Dict[str, Any] = {}
    for label, cost in (
        ("lastNonHelpingExact", exact - 1),
        ("firstHelpingExact", exact),
        ("firstHelpingGrid100", 13900),
    ):
        r = evaluate(cost, keep_witnesses=True, include_standing=True)
        boundary[label] = {
            "cost": cost,
            "costAxis": cost // COST_QUANTUM,
            "nP2": r["nP2"],
            "nP3Growth": r["nP3"],
            "nP3Standing": r["nP3Standing"],
            "pop3HelpsGrowth": r["pop3Helps"],
            "pop3HelpsStanding": r["pop3HelpsStanding"],
            "witnessP3Growth": r["witnesses"]["p3"],
            "witnessP3Standing": r["witnessStandingP3"],
            "witnessP2": r["witnesses"]["p2"],
        }

    side = {
        "lastNonHelpingExact": pop4_side_check(exact - 1),
        "firstHelpingExact": pop4_side_check(exact),
    }
    return {
        "fixtureId": "cost-frontier-v1",
        "version": 1,
        "kind": "untrusted-bounded-cost-frontier-search",
        "untrusted": True,
        "gameFactClaim": False,
        "modelModule": "search/mvp.py",
        "lowerBoundDoc": "mvp/LOWER-BOUND.md",
        "doc": "mvp/COST-FRONTIER.md",
        "baselineTheta": mvp._theta_dict(mvp.baseline_theta()),
        "definitions": {
            "N_p2": "least completion time over plays that never grow from pop 2 to pop 3 (growth-event reading; the strict pop-2 class)",
            "N_p3_growth": "least completion time over plays with a growth event whose target is >= 3, including when that growth happens on the completing step",
            "N_p3_standing": "least completion time over plays with a standing pop-3 state strictly before the completing step",
            "pop3Helps": "N_p3 < N_p2 for the corresponding N_p3 reading",
            "populationCap": POP_CAP,
            "pop4Note": "pop 4 is forbidden in the frontier comparison; see pop4SideCheck",
            "horizon": "N2_upper(c) = 7 + ceil(c/630), the exact strict pop-2 completion time",
            "layerDedup": "exact within-layer dedup over (pop, food, prog, trained, pop3Flag)",
            "costUnits": "cost in 1/100 production units; costAxis = cost/100",
        },
        "populationCap": POP_CAP,
        "envelopeGrowth": env_growth,
        "envelopeStanding": env_standing,
        "helpingWindowsGrowth": helping_windows(env_growth["M2"], env_growth["M3"]),
        "gridWindow": grid_window,
        "gridEarly": grid_early,
        "gridLate": grid_late,
        "boundaryWitnesses": boundary,
        "pop4SideCheck": side,
        "selfTest": self_test(),
        "elapsedSeconds": round(time.time() - t0, 3),
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _print_row(r: Dict[str, Any]) -> None:
    print(
        f"cost={r['cost']:>6} axis={r['costAxis']:>4} H={r['horizon']:>3} "
        f"N_p2={str(r['nP2']):>4} N_p3={str(r['nP3']):>4} "
        f"helps={str(r['pop3Helps']):>5} maxPop={r['maxPopSeen']}"
    )


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--scan", nargs=3, metavar=("LO", "HI", "STEP"), type=int)
    parser.add_argument("--cost", type=int)
    parser.add_argument("--find-crossover", action="store_true")
    parser.add_argument("--envelope", action="store_true")
    parser.add_argument("--write-fixture", action="store_true")
    parser.add_argument("--check-fixture", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    if args.self_test:
        out = self_test()
        print(json.dumps(out, indent=2))
        return 0 if out["ok"] else 1

    if args.cost is not None:
        row = evaluate(args.cost, keep_witnesses=True)
        if args.json:
            print(json.dumps(row, indent=2))
        else:
            _print_row(row)
            for cls in ("p2", "p3"):
                rows = row["witnesses"][cls]
                if rows:
                    print(f"  witness[{cls}] length={len(rows)} final={rows[-1]['post']} pop3Flag={rows[-1]['postPop3']}")
        return 0

    if args.scan:
        lo, hi, step = args.scan
        rows = scan(list(range(lo, hi + 1, step)), keep_witnesses=False)
        if args.json:
            print(json.dumps(rows, indent=2))
        else:
            for r in rows:
                _print_row(r)
        return 0

    if args.envelope:
        env = credit_envelope()
        if args.json:
            print(json.dumps(env, indent=2))
        else:
            print(f"envelope horizon={env['horizon']} maxCostSampled={env['maxCostSampled']} "
                  f"firstHelpingCostExact={env['firstHelpingCostExact']}")
            print("  t : M2 M3")
            for t in range(1, env["horizon"] + 1):
                print(f"  {t:>2} : {env['M2'][t]:>6} {env['M3'][t]}")
        return 0

    if args.find_crossover:
        cross = first_helping_cost(13000, 14500, 100)
        if args.json:
            print(json.dumps(cross, indent=2))
        else:
            print(json.dumps({k: v for k, v in cross.items() if k != "boundary"}, indent=2))
            for r in cross.get("boundary", []):
                _print_row(r)
        return 0

    if args.check_fixture:
        out = check_fixture()
        print(json.dumps(out, indent=2))
        return 0

    if args.write_fixture:
        fixture = build_fixture()
        FIXTURE_PATH.write_text(json.dumps(fixture, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"first helping cost (envelope, growth reading): {fixture['envelopeGrowth']['firstHelpingCostExact']}")
        print(f"first helping cost (envelope, standing reading): {fixture['envelopeStanding']['firstHelpingCostExact']}")
        print(f"selfTest ok={fixture['selfTest']['ok']}")
        print(f"wrote {FIXTURE_PATH}  elapsed={fixture['elapsedSeconds']}s")
        return 0 if fixture["selfTest"]["ok"] else 1

    parser.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
