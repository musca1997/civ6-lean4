#!/usr/bin/env python3
"""Urban Planning policy-variant executable for the civ6-lean4 breakthrough task.

This file is an **untrusted candidate generator / semantic executable**, not a
Civ6 fact claim and not a proof.  It consumes the frozen conditional MVP
semantics in ``search/mvp.py`` (module ``mvp``) and adds exactly one modelling
assumption:

    [POLICY-ASSUME] the Urban Planning policy is in effect from ``t = 0`` and
                    contributes **+1 base city production** (``+100`` in the
                    1/100 fixed-point units of ``M_MVP``) to
                    ``baseProd = 300 + workProd`` before the Happy production
                    multiplier is applied: ``P = 400 + workProd``.

Scope of the claim
------------------
* The variant is **conditional**: the policy's unlock cost, civics, culture and
  the policy-slot system are *not* modelled.  Nothing here says the policy is
  free, available, or that real Civ6 works this way.  This is the same
  conditional-model discipline as ``M_MVP``: the variant differs from
  ``M_MVP`` by one explicit additive production term and *nothing else*.
* Legality and growth semantics are **literally reused** from ``mvp`` by
  swapping only ``Scenario.base_prod`` (300 -> 400).  Every other part of the
  step -- the starvation guard, the pre-turn-population settler prerequisite,
  the IDLE/no-extra/worked-tile legality, the food surplus, the growth event,
  the basket reset, the multiplier tiers and the build credit rule -- is the
  same code path as the baseline.  ``bonus = 0`` therefore reproduces the
  baseline executable bit for bit, which is checked explicitly below.
* The result is a **strict breakthrough in the model**: the baseline (no
  policy) cannot train the first Settler before step 20 (Lean:
  ``noEarlier_20``), while the policy variant does so at step 18 (< 20).  The
  cost-110 counterpart is 25 (baseline) vs 22 (policy, < 25).  The Lean module
  ``Civ6Verify/Scenarios/UrbanPlanning.lean`` owns the kernel-checked version of
  the *achievability* half and pairs it with the baseline lower bound.

Owned by this module:
  * ``search/policy.py``
  * ``fixtures/policy-breakthrough.json``  (written by ``--write-fixture``)
  * ``mvp/POLICY.md``

Python standard library only.  Integer 1/100 units throughout; no floats.

Usage:
    python3 search/policy.py                  # baseline vs policy report
    python3 search/policy.py --self-test      # test suite
    python3 search/policy.py --write-fixture  # freeze fixtures/policy-breakthrough.json
    python3 search/policy.py --check-fixture  # replay/validate the frozen fixture
    python3 search/policy.py --lean-probe     # Lean #eval/#check cross-check
"""

from __future__ import annotations

import argparse
import contextlib
import dataclasses
import json
import os
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from typing import Any, Dict, Iterator, List, Optional, Sequence, Tuple

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "search"))

import mvp  # noqa: E402  (owned by the MVP task; imported read-only)

POLICY_FIXTURE_PATH = ROOT / "fixtures" / "policy-breakthrough.json"
LEAN_MODULE = "Civ6Verify.Scenarios.UrbanPlanning"
LEAN_FILE = ROOT / "Civ6Verify" / "Scenarios" / "UrbanPlanning.lean"
LEAN_ENV = ROOT / "scripts" / "lean-env"

#: The one new modelling assumption, in 1/100 production units.
POLICY_BONUS = 100
VARIANT_ID = "urban-planning-plus1-base-production"
TASK_HORIZON = 27

BASELINE_THETA = mvp.baseline_theta()
COST110_THETA = mvp.cost110_theta()


class PolicyError(ValueError):
    """The policy variant left the conditional contract box."""


def _require(cond: bool, msg: str) -> None:
    if not cond:
        raise PolicyError(msg)


# ---------------------------------------------------------------------------
# The variant: swap the base production only
# ---------------------------------------------------------------------------


@contextlib.contextmanager
def variant_scenario(bonus: int) -> Iterator[Any]:
    """Temporarily set ``mvp.SCENARIO.base_prod`` to ``300 + bonus``.

    This is the whole variant.  ``mvp._step_prepared`` reads the module-global
    ``SCENARIO`` at call time, so every downstream function (``step``,
    ``frontier_search``, ``contract_style_path``) uses the policy production
    while sharing the baseline legality/growth code path verbatim.
    """
    _require(isinstance(bonus, int) and bonus >= 0, "bonus must be a nonnegative int")
    original = mvp.SCENARIO
    patched = dataclasses.replace(original, base_prod=original.base_prod + bonus)
    mvp.SCENARIO = patched
    try:
        yield patched
    finally:
        mvp.SCENARIO = original


def policy_base_prod() -> int:
    return mvp.SCENARIO.base_prod + POLICY_BONUS


def step_variant(theta: mvp.Theta, state: mvp.State, action: mvp.Action,
                 bonus: int = POLICY_BONUS) -> Optional[mvp.State]:
    with variant_scenario(bonus):
        return mvp.step(theta, state, action)


def explain_variant(theta: mvp.Theta, state: mvp.State, action: mvp.Action,
                    bonus: int = POLICY_BONUS) -> Optional[mvp.StepInfo]:
    with variant_scenario(bonus):
        return mvp.explain_step(theta, state, action)


def frontier(theta: mvp.Theta, bonus: int, horizon: int = TASK_HORIZON,
             **kwargs: Any) -> mvp.SearchResult:
    with variant_scenario(bonus):
        return mvp.frontier_search(theta, horizon=horizon, **kwargs)


def contract_path(theta: mvp.Theta, bonus: int) -> List[Tuple[int, mvp.State, mvp.Action, mvp.State]]:
    """The shared contract-style witness: GH x7 IDLE, then GH+PH SETTLER."""
    with variant_scenario(bonus):
        return mvp.contract_style_path(theta, limit=TASK_HORIZON)


def witness_rows(theta: mvp.Theta, bonus: int) -> List[Dict[str, Any]]:
    path = contract_path(theta, bonus)
    with variant_scenario(bonus):
        return mvp.witness_rows(theta, path)


def goal_of(state: mvp.State) -> bool:
    return mvp.goal(state)


#: The exact Lean witness as a compact action list: 7x (GH, IDLE), then
#: ``settlerSteps`` x (GH+PH, SETTLER).  ``extra`` is always ``None``.
LEAN_MASK_GH = 1 << mvp.TILE_IDS.index("GH")                       # 0b0010
LEAN_MASK_GH_PH = LEAN_MASK_GH | (1 << mvp.TILE_IDS.index("PH"))   # 0b0110


def lean_witness(settler_steps: int) -> List[Dict[str, Any]]:
    out = [{"workMask": LEAN_MASK_GH, "extra": None, "build": "IDLE"} for _ in range(7)]
    out += [{"workMask": LEAN_MASK_GH_PH, "extra": None, "build": "SETTLER"}
            for _ in range(settler_steps)]
    return out


def lean_witness_rows(theta: mvp.Theta, bonus: int) -> List[Dict[str, Any]]:
    """Rows of the Lean witness; must equal the contract-style path rows."""
    rows = witness_rows(theta, bonus)
    return rows


def _row_actions(rows: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    return [dict(r["action"]) for r in rows]


def _action_key(a: Dict[str, Any]) -> Tuple[Any, Any, Any]:
    return (a.get("workMask"), a.get("extra"), a.get("build"))


# ---------------------------------------------------------------------------
# Crosschecks and negative controls
# ---------------------------------------------------------------------------


def bonus_zero_reproduces_baseline(theta: mvp.Theta) -> Dict[str, Any]:
    """``bonus = 0`` must be the baseline executable, not a new model."""
    base = mvp.frontier_search(theta, horizon=TASK_HORIZON, stop_on_goal=True, validate=True)
    zero = frontier(theta, 0, stop_on_goal=True, validate=True)
    mismatches = 0
    checked = 0
    # Transition-by-transition comparison on the baseline witness prefix states.
    rows = mvp.witness_rows(theta, mvp.contract_style_path(theta, limit=TASK_HORIZON))
    states = [mvp.START] + [mvp.State(*r["post"]) for r in rows]
    with variant_scenario(0):
        for s in states:
            for action in mvp.structural_actions(s.pop):
                checked += 1
                if mvp.step(theta, s, action) != step_variant(theta, s, action, bonus=0):
                    mismatches += 1
    return {
        "baselineN": base.n,
        "bonusZeroN": zero.n,
        "transitionsChecked": checked,
        "transitionMismatches": mismatches,
        "ok": base.n == zero.n and mismatches == 0 and checked > 0,
    }


def growth_is_unchanged(theta: mvp.Theta) -> Dict[str, Any]:
    """The bonus must not touch the food/growth pipeline (no hidden effect)."""
    mismatches = 0
    checked = 0
    with variant_scenario(0):
        rows = mvp.witness_rows(theta, mvp.contract_style_path(theta, limit=TASK_HORIZON))
    states = [mvp.START] + [mvp.State(*r["post"]) for r in rows]
    for s in states:
        for action in mvp.structural_actions(s.pop):
            i0 = mvp.explain_step(theta, s, action)
            i1 = explain_variant(theta, s, action, bonus=POLICY_BONUS)
            if i0 is None or i1 is None:
                if (i0 is None) != (i1 is None):
                    mismatches += 1
                continue
            checked += 1
            # The food/growth pipeline must be untouched: food yield, surplus,
            # growth amount and the growth flag all agree.
            if (i0.food_yield, i0.surplus, i0.growth, i0.grew) != \
               (i1.food_yield, i1.surplus, i1.growth, i1.grew):
                mismatches += 1
                continue
            # A post-population difference is legal only as the completion the
            # extra production caused; anything else is a hidden semantic change.
            if i0.state.pop != i1.state.pop and not (i1.completed and not i0.completed):
                mismatches += 1
    return {"transitionsChecked": checked, "growthMismatches": mismatches, "ok": mismatches == 0}


def production_delta(theta: mvp.Theta) -> Dict[str, Any]:
    """The production delta is exactly ``bonus * prodMult / 100`` and integral."""
    deltas: set[int] = set()
    nonintegral = 0
    checked = 0
    with variant_scenario(0):
        rows = mvp.witness_rows(theta, mvp.contract_style_path(theta, limit=TASK_HORIZON))
    states = [mvp.START] + [mvp.State(*r["post"]) for r in rows]
    for s in states:
        for action in mvp.structural_actions(s.pop):
            i0 = mvp.explain_step(theta, s, action)
            i1 = explain_variant(theta, s, action, bonus=POLICY_BONUS)
            if i0 is None or i1 is None:
                continue
            checked += 1
            if i1.q_raw % 100 != 0:
                nonintegral += 1
            deltas.add(i1.q - i0.q)
    return {
        "deltasObserved": sorted(deltas),
        "nonintegralQ": nonintegral,
        "checked": checked,
        "ok": nonintegral == 0 and all(d >= 0 for d in deltas),
    }


def banking_control(theta: mvp.Theta, bonus: int = POLICY_BONUS) -> Dict[str, Any]:
    """IDLE must accrue no settler progress in the policy variant either."""
    res = frontier(theta, bonus, stop_on_goal=True, keep_frontiers=True, validate=True)
    _require(res.layers is not None, "frontiers required")
    seen = 0
    violated = 0
    for layer in res.layers:
        for s in layer:
            for action in mvp.structural_actions(s.pop):
                if action.build != "IDLE":
                    continue
                with variant_scenario(bonus):
                    nxt = mvp.step(theta, s, action)
                if nxt is None:
                    continue
                seen += 1
                if nxt.prog != s.prog or nxt.trained != s.trained:
                    violated += 1
    return {"idleStepsChecked": seen, "bankingViolations": violated, "ok": seen > 0 and violated == 0}


def illegal_action_control(theta: mvp.Theta, bonus: int = POLICY_BONUS) -> Dict[str, Any]:
    """Pre-turn settler and structural illegalities stay illegal under the policy."""
    start = mvp.START
    settler_pop1 = mvp.Action(LEAN_MASK_GH, None, "SETTLER")
    idle_extra = mvp.Action(LEAN_MASK_GH, mvp.TILE_IDS.index("PH"), "IDLE")
    extra_worked = mvp.Action(0b0110, mvp.TILE_IDS.index("GH"), "SETTLER")
    starving = mvp.Action(1 << mvp.TILE_IDS.index("P"), None, "SETTLER")
    pop3 = mvp.State(3, 0, 0, 0)
    results = {
        "settler_at_pop1": step_variant(theta, start, settler_pop1, bonus) is None,
        "idle_with_extra": step_variant(theta, start, idle_extra, bonus) is None,
        "extra_already_worked": step_variant(theta, mvp.State(2, 0, 0, 0), extra_worked, bonus) is None,
        "starving_work_set": step_variant(theta, pop3, starving, bonus) is None,
    }
    return {"rejections": results, "ok": all(results.values())}


def strict_breakthrough_control() -> Dict[str, Any]:
    base80 = mvp.frontier_search(BASELINE_THETA, horizon=TASK_HORIZON, stop_on_goal=True, validate=True)
    base110 = mvp.frontier_search(COST110_THETA, horizon=TASK_HORIZON, stop_on_goal=True, validate=True)
    pol80 = frontier(BASELINE_THETA, POLICY_BONUS, stop_on_goal=True, validate=True)
    pol110 = frontier(COST110_THETA, POLICY_BONUS, stop_on_goal=True, validate=True)
    return {
        "baselineN": base80.n,
        "policyN": pol80.n,
        "baselineN110": base110.n,
        "policyN110": pol110.n,
        "strictlyFaster": bool(pol80.n is not None and base80.n is not None and pol80.n < base80.n
                               and pol110.n is not None and base110.n is not None and pol110.n < base110.n),
        "withinTaskHorizon": all(n is not None and n < 20 for n in (pol80.n,))
        and bool(base80.n == 20 and pol80.n is not None and pol80.n < 20),
    }


# ---------------------------------------------------------------------------
# Report / fixture
# ---------------------------------------------------------------------------


CONDITIONAL_ASSUMPTIONS: List[Dict[str, str]] = [
    {
        "id": "POLICY-ASSUME",
        "text": "Urban Planning is in effect from t=0 and adds +1 base city production "
                "(+100 in 1/100 units) to baseProd = 300 + workProd, before prodMult.",
    },
    {
        "id": "INHERIT-MVP",
        "text": "The variant inherits every M_MVP v2.1 conditional assumption verbatim "
                "(A1/A2/A8, growth_first, newCitizen=best, amenityStock=2, basketOnGrowth=zero, "
                "productionRounding=exact, thresholdRounding=exact, no progress before pop 2 or on IDLE, "
                "starvation illegal, extraGain(none)=0, extra never feeds food).",
    },
    {
        "id": "UNLOCK-NOT-MODELLED",
        "text": "Civics, culture, policy slots and the policy's unlock cost are NOT modelled. "
                "The variant does not say the policy is free; it is an explicit conditional assumption.",
    },
    {
        "id": "NOT-A-FULLGAME-COMPARISON",
        "text": "This is a comparison of two conditional models that differ only by the +100 production term. "
                "It is not a full-game comparison and not a Civ6 claim.",
    },
]

NOT_CLAIMED: List[str] = [
    "No Civilization VI fact: [V] = 0, no build pinned, no fixture run in game.",
    "No claim that the policy is unlocked for free or at t=0 in the real game.",
    "No claim that N=18 (cost 80) or N=22 (cost 110) is optimal for the policy variant; "
    "only achievability is proved in Lean and paired with the baseline lower bound.",
    "No full-game comparison: no culture, no civics tree, no opportunity cost of the policy slot.",
    "No claim about any other theta axis; only the cost axis is instantiated (80/110).",
]


def build_report() -> Dict[str, Any]:
    t0 = time.time()
    crosschecks = {
        "bonusZeroReproducesBaseline": bonus_zero_reproduces_baseline(BASELINE_THETA),
        "growthUnchanged": growth_is_unchanged(BASELINE_THETA),
        "productionDelta": production_delta(BASELINE_THETA),
        "banking": banking_control(BASELINE_THETA),
        "illegalActions": illegal_action_control(BASELINE_THETA),
        "strictBreakthrough": strict_breakthrough_control(),
    }

    pol_rows = lean_witness_rows(BASELINE_THETA, POLICY_BONUS)
    contract_rows = contract_path(BASELINE_THETA, POLICY_BONUS)
    with variant_scenario(POLICY_BONUS):
        pol_checks = mvp.verify_witness(BASELINE_THETA, pol_rows, len(pol_rows))
    lean_actions = [_action_key(a) for a in _row_actions(pol_rows)]
    _require(lean_actions == [_action_key(a) for a in lean_witness(len(pol_rows) - 7)],
             "contract witness is not the Lean witness")

    base80 = mvp.frontier_search(BASELINE_THETA, horizon=TASK_HORIZON, stop_on_goal=True, validate=True)
    pol80 = frontier(BASELINE_THETA, POLICY_BONUS, stop_on_goal=True, validate=True)
    base110 = mvp.frontier_search(COST110_THETA, horizon=TASK_HORIZON, stop_on_goal=True, validate=True)
    pol110 = frontier(COST110_THETA, POLICY_BONUS, stop_on_goal=True, validate=True)
    c110_rows = lean_witness_rows(COST110_THETA, POLICY_BONUS)
    with variant_scenario(POLICY_BONUS):
        c110_checks = mvp.verify_witness(COST110_THETA, c110_rows, len(c110_rows))

    report: Dict[str, Any] = {
        "fixtureId": "policy-breakthrough-v1",
        "version": 1,
        "kind": "policy-variant-executable",
        "untrusted": True,
        "gameFactClaim": False,
        "owner": "policy breakthrough task",
        "policyVariant": {
            "id": VARIANT_ID,
            "effect": "+1 base city production (Urban Planning), applied as baseProd 300 -> 400",
            "bonusUnits": POLICY_BONUS,
            "baselineBaseProduction": mvp.SCENARIO.base_prod,
            "policyBaseProduction": mvp.SCENARIO.base_prod + POLICY_BONUS,
            "appliedBefore": "prodMult (Happy 105): q = (400 + workProd + growthExtra) * 105 / 100",
            "sharedCodePath": "search/mvp.py via Scenario.base_prod swap only; legality/growth reused verbatim",
        },
        "conditionalAssumptions": CONDITIONAL_ASSUMPTIONS,
        "notClaimed": NOT_CLAIMED,
        "leanAnchors": {
            "module": "Civ6Verify/Scenarios/UrbanPlanning.lean",
            "theorems": {
                "bonus_zero_eq_baseline_step": "Civ6Verify.Scenarios.UrbanPlanning.bonusStep_zero",
                "policy_model": "Civ6Verify.Scenarios.UrbanPlanning.policyModel",
                "policy_achievable_18": "Civ6Verify.Scenarios.UrbanPlanning.policy_achievable_18",
                "policy_achievable_22": "Civ6Verify.Scenarios.UrbanPlanning.policy_achievable_22",
                "baseline_lower_bound_20": "Civ6Verify.Bounds.MvpOptimality.noEarlier_20",
                "baseline_lower_bound_25": "Civ6Verify.Bounds.MvpOptimality.noEarlier_25",
                "breakthrough": "Civ6Verify.Scenarios.UrbanPlanning.urbanPlanning_breakthrough",
            },
            "expected": {"policyN80": pol80.n, "policyN110": pol110.n,
                         "baselineN80": base80.n, "baselineN110": base110.n},
        },
        "baseline": {
            "theta": mvp._theta_dict(BASELINE_THETA),
            "n": base80.n,
            "layerSizes": base80.layer_sizes,
        },
        "policy": {
            "theta": mvp._theta_dict(BASELINE_THETA),
            "n": pol80.n,
            "goalState": list(pol80.goal_state) if pol80.goal_state else None,
            "layerSizes": pol80.layer_sizes,
            "witnessKind": "contract-style Lean witness: 7x GH IDLE then kx (GH+PH) SETTLER",
            "witnessActions": lean_witness(len(pol_rows) - 7),
            "witness": pol_rows,
            "witnessChecks": pol_checks,
        },
        "cost110": {
            "baselineN": base110.n,
            "policyN": pol110.n,
            "witnessActions": lean_witness(len(c110_rows) - 7),
            "witness": c110_rows,
            "witnessChecks": c110_checks,
            "goalState": list(pol110.goal_state) if pol110.goal_state else None,
        },
        "crosschecks": crosschecks,
        "execution": {
            "horizon": TASK_HORIZON,
            "seconds": round(time.time() - t0, 3),
            "python": sys.version.split()[0],
        },
    }
    return report


def report_summary(report: Dict[str, Any]) -> str:
    lines = [
        "Urban Planning policy variant (untrusted search)",
        f"  variant: {report['policyVariant']['id']}  ({report['policyVariant']['effect']})",
        f"  baseline cost80 N = {report['baseline']['n']}   policy cost80 N = {report['policy']['n']}"
        f"  (<20: {report['policy']['n'] < 20})",
        f"  baseline cost110 N = {report['cost110']['baselineN']}   policy cost110 N = {report['cost110']['policyN']}",
        f"  policy witness final = {report['policy']['witnessChecks']['finalState']}",
        "  crosschecks:",
    ]
    for key, value in report["crosschecks"].items():
        lines.append(f"    {key}: ok={value.get('ok', value.get('strictlyFaster'))}  {value}")
    return "\n".join(lines)


def write_fixture(report: Dict[str, Any], path: Path = POLICY_FIXTURE_PATH) -> None:
    path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def check_fixture(path: Path = POLICY_FIXTURE_PATH) -> Dict[str, Any]:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    _require(data.get("fixtureId") == "policy-breakthrough-v1", "unexpected fixture id")
    _require(data.get("untrusted") is True, "fixture must be untrusted")
    _require(data.get("gameFactClaim") is False, "fixture must not claim a game fact")
    _require(data["policyVariant"]["bonusUnits"] == POLICY_BONUS, "bonus mismatch")
    results: Dict[str, Any] = {}

    base80 = mvp.frontier_search(BASELINE_THETA, horizon=TASK_HORIZON, stop_on_goal=True, validate=True)
    pol80 = frontier(BASELINE_THETA, POLICY_BONUS, stop_on_goal=True, validate=True)
    base110 = mvp.frontier_search(COST110_THETA, horizon=TASK_HORIZON, stop_on_goal=True, validate=True)
    pol110 = frontier(COST110_THETA, POLICY_BONUS, stop_on_goal=True, validate=True)
    results["baselineN"] = base80.n
    results["policyN"] = pol80.n
    results["baselineN110"] = base110.n
    results["policyN110"] = pol110.n
    _require(base80.n == data["baseline"]["n"], "baseline N mismatch")
    _require(pol80.n == data["policy"]["n"], "policy N mismatch")
    _require(base110.n == data["cost110"]["baselineN"], "cost110 baseline N mismatch")
    _require(pol110.n == data["cost110"]["policyN"], "cost110 policy N mismatch")
    _require(pol80.n < base80.n < 20 or (pol80.n < base80.n and pol80.n < 20),
             "policy is not a strict breakthrough under step 20")

    # Replay the recorded Lean witnesses.
    with variant_scenario(POLICY_BONUS):
        mvp.verify_witness(BASELINE_THETA, data["policy"]["witness"], data["policy"]["n"])
        mvp.verify_witness(COST110_THETA, data["cost110"]["witness"], data["cost110"]["policyN"])
    results["policyWitnessRows"] = len(data["policy"]["witness"])
    results["cost110WitnessRows"] = len(data["cost110"]["witness"])

    # Recompute the crosschecks / negative controls independently.
    results["bonusZeroReproducesBaseline"] = bonus_zero_reproduces_baseline(BASELINE_THETA)["ok"]
    results["growthUnchanged"] = growth_is_unchanged(BASELINE_THETA)["ok"]
    results["banking"] = banking_control(BASELINE_THETA)["ok"]
    results["illegalActions"] = illegal_action_control(BASELINE_THETA)["ok"]
    _require(all(bool(results[k]) for k in ("bonusZeroReproducesBaseline", "growthUnchanged",
                                            "banking", "illegalActions")), "a crosscheck failed")
    results["ok"] = True
    return results


# ---------------------------------------------------------------------------
# Lean probe (optional): #eval the witness and #check the theorem anchors
# ---------------------------------------------------------------------------

LEAN_PROBE_MARKER = "@@POLICY-PROBE@@"


def _lean_cmd() -> List[str]:
    if LEAN_ENV.exists():
        return [str(LEAN_ENV), "lake", "env", "lean"]
    return ["lake", "env", "lean"]


def lean_probe(timeout: int = 600) -> Dict[str, Any]:
    """Evaluate the Lean witness and check the headline constants exist."""
    checks = [
        f"#check @{LEAN_MODULE}.policy_achievable_18",
        f"#check @{LEAN_MODULE}.policy_achievable_22",
        f"#check @{LEAN_MODULE}.urbanPlanning_breakthrough",
        f"#check @{LEAN_MODULE}.bonusStep_zero",
        f"#eval {LEAN_MODULE}.policyWitness.length",
        f"#eval {LEAN_MODULE}.policyWitness110.length",
        f'#eval toString (repr (Civ6Verify.Reachability.run ({LEAN_MODULE}.policyModel '
        f"Civ6Verify.Model.Mvp.baselineParams) Civ6Verify.Model.Mvp.init "
        f"{LEAN_MODULE}.policyWitness))",
    ]
    source = f"import {LEAN_MODULE}\n\n" + "\n".join(checks) + f"\n\n-- {LEAN_PROBE_MARKER}\n"
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "PolicyProbe.lean"
        probe.write_text(source, encoding="utf-8")
        cmd = _lean_cmd() + [str(probe)]
        proc = subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True, timeout=timeout)
    ok = proc.returncode == 0
    return {
        "ok": ok,
        "returncode": proc.returncode,
        "stdout": proc.stdout.strip(),
        "stderr": proc.stderr.strip()[-2000:],
    }


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


class PolicyVariantTests(unittest.TestCase):
    def test_variant_bonus_is_only_base_production(self) -> None:
        self.assertEqual(mvp.SCENARIO.base_prod, 300)
        self.assertEqual(policy_base_prod(), 400)
        self.assertEqual(LEAN_MASK_GH, 0b0010)
        self.assertEqual(LEAN_MASK_GH_PH, 0b0110)

    def test_bonus_zero_is_baseline(self) -> None:
        self.assertTrue(bonus_zero_reproduces_baseline(BASELINE_THETA)["ok"])

    def test_growth_and_legality_unchanged(self) -> None:
        self.assertTrue(growth_is_unchanged(BASELINE_THETA)["ok"])

    def test_production_delta_is_integral(self) -> None:
        d = production_delta(BASELINE_THETA)
        self.assertTrue(d["ok"])
        self.assertEqual(d["nonintegralQ"], 0)
        self.assertIn(105, d["deltasObserved"])
        for delta in d["deltasObserved"]:
            self.assertEqual(delta % 5, 0)

    def test_policy_is_faster(self) -> None:
        c = strict_breakthrough_control()
        self.assertEqual(c["baselineN"], 20)
        self.assertEqual(c["policyN"], 18)
        self.assertEqual(c["baselineN110"], 25)
        self.assertEqual(c["policyN110"], 22)
        self.assertTrue(c["strictlyFaster"])
        self.assertTrue(c["withinTaskHorizon"])

    def test_lean_witness_action_sequence(self) -> None:
        rows = lean_witness_rows(BASELINE_THETA, POLICY_BONUS)
        self.assertEqual(len(rows), 18)
        self.assertEqual([_action_key(a) for a in _row_actions(rows)],
                         [_action_key(a) for a in lean_witness(11)])
        self.assertEqual(rows[-1]["action"]["workMask"], LEAN_MASK_GH_PH)
        self.assertEqual(rows[-1]["post"], [1, 1210, 85, 1])

    def test_cost110_witness(self) -> None:
        rows = lean_witness_rows(COST110_THETA, POLICY_BONUS)
        self.assertEqual(len(rows), 22)
        self.assertEqual(rows[-1]["post"], [1, 1650, 25, 1])

    def test_settler_q_values(self) -> None:
        s = mvp.State(2, 0, 0, 0)
        a = mvp.Action(LEAN_MASK_GH_PH, None, "SETTLER")
        i0 = mvp.explain_step(BASELINE_THETA, s, a)
        i1 = explain_variant(BASELINE_THETA, s, a)
        assert i0 is not None and i1 is not None
        self.assertEqual(i0.q, 630)
        self.assertEqual(i1.q, 735)
        self.assertEqual(i1.q - i0.q, 105)
        self.assertEqual(i1.prod_used, 700)
        self.assertEqual(i1.food_yield, i0.food_yield)
        self.assertEqual(i1.growth, i0.growth)

    def test_banking_control(self) -> None:
        self.assertTrue(banking_control(BASELINE_THETA)["ok"])

    def test_illegal_actions_control(self) -> None:
        self.assertTrue(illegal_action_control(BASELINE_THETA)["ok"])

    def test_no_free_unlock_in_legality(self) -> None:
        # The policy does not legalise a pre-turn settler, does not add actions,
        # and does not change the legality predicate at all.
        start = mvp.START
        self.assertIsNone(step_variant(BASELINE_THETA, start,
                                       mvp.Action(LEAN_MASK_GH, None, "SETTLER")))
        with variant_scenario(POLICY_BONUS):
            pol_actions = {tuple(a) for a in mvp.structural_actions(2)}
        base_actions = {tuple(a) for a in mvp.structural_actions(2)}
        self.assertEqual(pol_actions, base_actions)

    def test_scenario_restored(self) -> None:
        self.assertEqual(mvp.SCENARIO.base_prod, 300)


def run_self_tests() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(PolicyVariantTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--write-fixture", action="store_true")
    parser.add_argument("--check-fixture", action="store_true")
    parser.add_argument("--lean-probe", action="store_true")
    args = parser.parse_args(argv)

    if args.self_test:
        return run_self_tests()
    if args.check_fixture:
        print(json.dumps(check_fixture(), indent=2))
        return 0
    if args.lean_probe:
        print(json.dumps(lean_probe(), indent=2))
        return 0
    if args.write_fixture:
        report = build_report()
        write_fixture(report)
        print(report_summary(report))
        print(f"wrote {POLICY_FIXTURE_PATH}")
        return 0

    print(report_summary(build_report()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
