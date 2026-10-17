#!/usr/bin/env python3
"""Cross-check `fixtures/synthetic-v0.json` against the *actual* Lean scenario.

This is an integration drift check for the synthetic benchmark (`synthetic-v0`,
**NOT Civilization VI**). It does not re-state any expected number: every
expectation is read from the frozen fixture, and every actual value is produced
by evaluating `Civ6Verify.Scenarios.Synthetic` with Lean. The script only
supplies the horizon and the fixture witness actions to the probe.

What is compared
----------------
* rule constants re-declared in the Lean scenario  vs  `fixture.rules`
  (including the derived production cap `settler_cost - 1`);
* `Frontier model t` (exact-step, the core notion) counts/contents
  vs  `expected.exactStepFrontierCounts` / `expected.exactStepFrontiers`;
* `distLayer t` (BFS distance layers) counts/contents
  vs  `expected.distanceLayerCounts` / `expected.reachableLayers`;
* `earliestGoalTick? model goalB bound`  vs  `expected.syntheticEarliestGoalTick`;
* `checkCertificate model goalB N` is true and `... (N-1)` is false;
* replaying the fixture witness through `run model init` lands on
  `expected.completionStateKey`, and the scenario's own `witnessStates`
  match `expected.witnessStates`;
* `actionSequences N` goal count  vs  `expected.optimalSequenceCount`;
* `expected.distinctStatesTotal` and `expected.expandedTransitions`.

Neither side is trusted: the fixture is an untrusted Python candidate (see
`research/SYNTHETIC.md`), and the Lean scenario is owned by a different task.
A mismatch is a real drift signal in at least one of them; this script does not
decide which side is "right".

Exit codes
----------
0  all checks passed
1  at least one semantic mismatch
2  fixture missing / invalid / missing expected fields
3  Lean toolchain (`scripts/lean-env`) unavailable
4  Lean build or probe evaluation failed (e.g. scenario mid-edit, renamed API)

Usage
-----
    python3 scripts/check-synthetic.py
    python3 scripts/check-synthetic.py --json
    python3 scripts/check-synthetic.py --no-build          # use existing olean
    python3 scripts/check-synthetic.py --force-build       # rebuild regardless of mtime
    python3 scripts/check-synthetic.py --keep-probe /tmp/p.lean

The probe file is written to a temporary directory outside the repository. The
only repository writes come from `lake build` (build artifacts), and only when
the scenario/core sources are newer than the existing `.olean` (or with
`--build`). No Lean source is modified.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURE_DEFAULT = REPO_ROOT / "fixtures" / "synthetic-v0.json"
SCENARIO_MODULE = "Civ6Verify.Scenarios.Synthetic"
SCENARIO_FILE = REPO_ROOT / "Civ6Verify" / "Scenarios" / "Synthetic.lean"
CORE_FILE = REPO_ROOT / "Civ6Verify" / "Reachability" / "Finite.lean"
OLEAN_FILE = (
    REPO_ROOT
    / ".lake"
    / "build"
    / "lib"
    / "lean"
    / "Civ6Verify"
    / "Scenarios"
    / "Synthetic.olean"
)
LEAN_ENV = REPO_ROOT / "scripts" / "lean-env"
MARKER = "@@SYNTHETIC@@"

EXIT_OK = 0
EXIT_MISMATCH = 1
EXIT_FIXTURE = 2
EXIT_TOOLCHAIN = 3
EXIT_LEAN = 4


class CheckError(Exception):
    """Fatal setup problem carrying the intended exit code."""

    def __init__(self, message: str, code: int) -> None:
        super().__init__(message)
        self.code = code


# ---------------------------------------------------------------------------
# fixture side (expectations only; no numbers are written here)
# ---------------------------------------------------------------------------


def load_fixture(path: Path) -> Dict[str, Any]:
    if not path.exists():
        raise CheckError(f"missing fixture: {path}", EXIT_FIXTURE)
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise CheckError(f"fixture {path} is not valid JSON: {exc}", EXIT_FIXTURE) from exc
    if not isinstance(doc, dict):
        raise CheckError(f"fixture {path} must be a JSON object", EXIT_FIXTURE)
    return doc


REQUIRED_EXPECTED = (
    "syntheticEarliestGoalTick",
    "layerCounts",
    "distanceLayerCounts",
    "exactStepFrontierCounts",
    "reachableLayers",
    "exactStepFrontiers",
    "witness",
    "witnessStates",
    "goalStateKeysAtOptimum",
    "optimalSequenceCount",
    "distinctStatesTotal",
    "expandedTransitions",
)


def require_expected(doc: Dict[str, Any]) -> Dict[str, Any]:
    expected = doc.get("expected")
    if not isinstance(expected, dict):
        raise CheckError("fixture has no `expected` object", EXIT_FIXTURE)
    missing = [k for k in REQUIRED_EXPECTED if k not in expected]
    if missing:
        raise CheckError(
            f"fixture `expected` is missing fields: {', '.join(missing)}", EXIT_FIXTURE
        )
    return expected


def canonical_state(state: Dict[str, Any]) -> str:
    """Same encoding as `search/synthetic.py:state_key` (and the Lean probe)."""
    return (
        f"pop={state['pop']};food={state['food']};"
        f"prod={state['production']};done={state['settlersCompleted']}"
    )


def layer_digest(layer: Sequence[str]) -> str:
    """Same 16-hex digest rule as `search/synthetic.py:layer_digest`."""
    payload = "\n".join(sorted(layer)).encode("ascii")
    return hashlib.sha256(payload).hexdigest()[:16]


def expected_rules(doc: Dict[str, Any]) -> Dict[str, Any]:
    rules = doc["rules"]
    tiles = {tile["id"]: tile for tile in rules["tiles"]}
    thresholds = {int(k): int(v) for k, v in rules["growthThresholdByPop"].items()}
    settler = rules["settler"]
    return {
        "popMin": rules["popMin"],
        "popMax": rules["popMax"],
        "foodPerCitizen": rules["foodPerCitizenPerTick"],
        "farmFood": tiles["farm"]["food"],
        "farmProd": tiles["farm"]["production"],
        "mineFood": tiles["mine"]["food"],
        "mineProd": tiles["mine"]["production"],
        "settleCost": settler["cost"],
        "settlePopCost": settler["populationCost"],
        "prereqPop": settler["prereqPop"],
        "progressCap": settler["productionProgressCap"],
        "threshold1": thresholds[1],
        "threshold2": thresholds[2],
        "foodCap1": thresholds[1] - 1,
        "foodCap2": thresholds[2] - 1,
    }


# ---------------------------------------------------------------------------
# Lean side (probe generation + evaluation)
# ---------------------------------------------------------------------------


def build_probe(horizon: int, witness: Sequence[Sequence[int]]) -> str:
    """Lean probe source. Only the horizon and fixture witness are injected."""
    if horizon < 1:
        raise CheckError(f"fixture optimum horizon must be >= 1, got {horizon}", EXIT_FIXTURE)
    witness_lean = ", ".join(
        f"{{ farm := {int(a[0])}, mine := {int(a[1])} }}" for a in witness
    )
    return f"""import Lean.Data.Json
import Civ6Verify.Scenarios.Synthetic

open Lean
open Civ6Verify.Scenarios.Synthetic
open Civ6Verify.Reachability

namespace SyntheticCheck

/-- Horizon taken from the fixture (`expected.syntheticEarliestGoalTick`). -/
def H : Nat := {horizon}
/-- Scan bound for `earliestGoalTick?`: beyond H so a later tick is observable. -/
def bound : Nat := H + 3

/-- Canonical state encoding shared with the fixture/Python (`state_key`). -/
def stateStr (s : State) : String :=
  s!"pop={{s.pop}};food={{s.food}};prod={{s.prod}};done={{s.done}}"

/-- The fixture's `expected.witness`, replayed through the scenario's transition. -/
def fixtureWitness : List Action := [{witness_lean}]

def payload : Json :=
  Json.mkObj
    [ ("popMin", toJson popMin)
    , ("popMax", toJson popMax)
    , ("foodPerCitizen", toJson foodPerCitizen)
    , ("farmFood", toJson farmFood)
    , ("farmProd", toJson farmProd)
    , ("mineFood", toJson mineFood)
    , ("mineProd", toJson mineProd)
    , ("settleCost", toJson settleCost)
    , ("settlePopCost", toJson settlePopCost)
    , ("prereqPop", toJson prereqPop)
    , ("progressCap", toJson progressCap)
    , ("threshold1", toJson (growthThreshold 1))
    , ("threshold2", toJson (growthThreshold 2))
    , ("foodCap1", toJson (foodCap 1))
    , ("foodCap2", toJson (foodCap 2))
    , ("frontierCounts", toJson ((List.range (H + 1)).map (fun t => (Frontier model t).length)))
    , ("frontierLayers", toJson ((List.range (H + 1)).map (fun t => (Frontier model t).map stateStr)))
    , ("distLayerCounts", toJson ((List.range (H + 1)).map (fun t => (distLayer t).length)))
    , ("distLayerLayers", toJson ((List.range (H + 1)).map (fun t => (distLayer t).map stateStr)))
    , ("earliestSome", toJson (earliestGoalTick? model goalB bound).isSome)
    , ("earliestVal", toJson ((earliestGoalTick? model goalB bound).getD 0))
    , ("checkCertificateAtH", toJson (checkCertificate model goalB H))
    , ("checkCertificateBelowH", toJson (checkCertificate model goalB (H - 1)))
    , ("fixtureWitnessFinal", Json.str (stateStr (run model init fixtureWitness)))
    , ("scenarioWitnessFinal", Json.str (stateStr (run model init witness)))
    , ("scenarioWitnessStates", toJson (witnessStates.map stateStr))
    , ("goalSeqCount", toJson ((actionSequences H).filter (fun as => goalB (run model init as))).length)
    , ("allSeqCount", toJson (actionSequences H).length)
    , ("distinctStatesTotal",
        toJson ((List.range (H + 1)).foldl (fun acc t => acc + (distLayer t).length) 0))
    , ("expandedTransitions",
        toJson ((List.range H).foldl
          (fun acc t => acc + (distLayer t).foldl (fun acc s => acc + (legalActions s).length) 0) 0))
    ]

end SyntheticCheck

#eval IO.println s!"{MARKER}{{SyntheticCheck.payload.compress}}"
"""


def run_command(cmd: List[str], timeout: float) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def tailless(text: str, limit: int = 4000) -> str:
    text = text.strip()
    return text if len(text) <= limit else "…\n" + text[-limit:]


def needs_build() -> bool:
    if not OLEAN_FILE.exists():
        return True
    olean_mtime = OLEAN_FILE.stat().st_mtime
    for source in (SCENARIO_FILE, CORE_FILE):
        if source.exists() and source.stat().st_mtime > olean_mtime:
            return True
    return False


def ensure_olean(no_build: bool, force_build: bool, timeout: float, verbose: bool) -> None:
    if no_build or not (force_build or needs_build()):
        if not OLEAN_FILE.exists():
            raise CheckError(
                f"--no-build was given but {OLEAN_FILE} does not exist; "
                "build with `scripts/lean-env lake build "
                f"{SCENARIO_MODULE}`",
                EXIT_LEAN,
            )
        return
    proc = run_command(
        [str(LEAN_ENV), "lake", "build", SCENARIO_MODULE], timeout=timeout
    )
    if verbose:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
    if proc.returncode != 0:
        raise CheckError(
            f"Lean build of {SCENARIO_MODULE} failed (exit {proc.returncode}). "
            "The scenario may be mid-edit by its owner; this script never edits it.\n"
            f"{tailless(proc.stderr or proc.stdout)}",
            EXIT_LEAN,
        )


def evaluate_probe(probe: Path, timeout: float, verbose: bool) -> Dict[str, Any]:
    proc = run_command([str(LEAN_ENV), "lake", "env", "lean", str(probe)], timeout=timeout)
    if verbose:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
    if proc.returncode != 0:
        raise CheckError(
            f"Lean probe failed (exit {proc.returncode}); the scenario API may "
            f"have been renamed.\n{tailless(proc.stderr or proc.stdout)}",
            EXIT_LEAN,
        )
    payloads = [
        line[len(MARKER):]
        for line in proc.stdout.splitlines()
        if line.startswith(MARKER)
    ]
    if not payloads:
        raise CheckError(
            "Lean probe produced no payload line "
            f"({MARKER}…); stdout tail:\n{tailless(proc.stdout)}",
            EXIT_LEAN,
        )
    try:
        return json.loads(payloads[-1])
    except json.JSONDecodeError as exc:
        raise CheckError(
            f"probe payload is not valid JSON: {exc}", EXIT_LEAN
        ) from exc


# ---------------------------------------------------------------------------
# comparison
# ---------------------------------------------------------------------------


class Report:
    def __init__(self) -> None:
        self.checks: List[Dict[str, Any]] = []

    def add(self, name: str, expected: Any, actual: Any) -> bool:
        ok = expected == actual
        self.checks.append(
            {"check": name, "expected": expected, "actual": actual, "ok": ok}
        )
        return ok

    @property
    def ok(self) -> bool:
        return all(c["ok"] for c in self.checks)


def fixture_internal_checks(doc: Dict[str, Any]) -> Report:
    """Check the fixture against itself (aliases, lists, digests, witness)."""
    expected = require_expected(doc)
    report = Report()
    reachable = expected["reachableLayers"]
    exact = expected["exactStepFrontiers"]
    distance_counts = [len(layer) for layer in reachable]
    exact_counts = [len(layer) for layer in exact]

    report.add("fixture.layerCounts == distanceLayerCounts",
               expected["layerCounts"], expected["distanceLayerCounts"])
    report.add("fixture.layerCounts match reachableLayers", expected["layerCounts"], distance_counts)
    report.add("fixture.distanceLayerCounts match reachableLayers",
               expected["distanceLayerCounts"], distance_counts)
    report.add("fixture.exactStepFrontierCounts match exactStepFrontiers",
               expected["exactStepFrontierCounts"], exact_counts)
    report.add("fixture.layerDigests match reachableLayers",
               expected["layerDigests"], [layer_digest(layer) for layer in reachable])
    report.add("fixture.distanceLayerDigests match reachableLayers",
               expected["distanceLayerDigests"], [layer_digest(layer) for layer in reachable])
    report.add("fixture.exactStepFrontierDigests match exactStepFrontiers",
               expected["exactStepFrontierDigests"], [layer_digest(layer) for layer in exact])
    report.add("fixture.distinctStatesTotal == sum(distanceLayerCounts)",
               expected["distinctStatesTotal"], sum(distance_counts))

    initial_key = canonical_state(doc["initialState"])
    final_keys = expected["goalStateKeysAtOptimum"]
    report.add("fixture.witnessStates start at initialState",
               initial_key, canonical_state(expected["witnessStates"][0]))
    report.add("fixture.witnessStates end in a goal state",
               True, canonical_state(expected["witnessStates"][-1]) in final_keys)
    report.add("fixture.optimalSequenceCount >= 1", True, expected["optimalSequenceCount"] >= 1)
    report.add("fixture.initialState is not a goal", True, doc["initialState"]["settlersCompleted"] == 0)
    report.add("fixture.rules cap == cost-1",
               (doc["rules"]["settler"]["cost"] or 0) - 1,
               doc["rules"]["settler"]["productionProgressCap"])
    report.add("fixture.witness length == optimum",
               expected["syntheticEarliestGoalTick"], len(expected["witness"]))
    report.add("fixture.witnessStates length == optimum + 1",
               expected["syntheticEarliestGoalTick"] + 1, len(expected["witnessStates"]))
    report.add("fixture.layers cover 0..optimum",
               expected["syntheticEarliestGoalTick"] + 1, len(reachable))
    report.add("fixture.exactStepFrontiers cover 0..optimum",
               expected["syntheticEarliestGoalTick"] + 1, len(exact))
    return report


def compare(doc: Dict[str, Any], lean: Dict[str, Any]) -> Report:
    expected = require_expected(doc)
    rules_expected = expected_rules(doc)
    report = fixture_internal_checks(doc)

    # 1. rules re-declared in Lean vs the fixture, plus Lean's own cap contract
    for key, value in rules_expected.items():
        report.add(f"rules.{key}", value, lean.get(key))
    report.add(
        "rules.progressCap == settleCost - 1 (Lean contract)",
        True,
        lean.get("progressCap") == (lean.get("settleCost") or 0) - 1,
    )

    horizon = int(expected["syntheticEarliestGoalTick"])

    # 2. frontiers (exact-step, core notion)
    report.add(
        "exactStepFrontierCounts", expected["exactStepFrontierCounts"],
        lean.get("frontierCounts"),
    )
    report.add(
        "exactStepFrontiers",
        [sorted(layer) for layer in expected["exactStepFrontiers"]],
        [sorted(layer) for layer in (lean.get("frontierLayers") or [])],
    )

    # 3. BFS distance layers
    report.add("distanceLayerCounts", expected["distanceLayerCounts"], lean.get("distLayerCounts"))
    report.add(
        "reachableLayers",
        [sorted(layer) for layer in expected["reachableLayers"]],
        [sorted(layer) for layer in (lean.get("distLayerLayers") or [])],
    )

    # 4. earliest goal / certificate
    report.add("earliestGoalSome", True, lean.get("earliestSome"))
    report.add("earliestGoalTick", horizon, lean.get("earliestVal"))
    report.add("checkCertificate at N", True, lean.get("checkCertificateAtH"))
    report.add("checkCertificate below N", False, lean.get("checkCertificateBelowH"))

    # 5. witness (fixture actions replayed by Lean, and the Lean witness table)
    report.add(
        "fixture witness final state",
        expected["completionStateKey"] if "completionStateKey" in expected
        else expected["goalStateKeysAtOptimum"][-1],
        lean.get("fixtureWitnessFinal"),
    )
    report.add(
        "scenario witness final state",
        canonical_state(expected["witnessStates"][-1]),
        lean.get("scenarioWitnessFinal"),
    )
    report.add(
        "scenario witnessStates",
        [canonical_state(s) for s in expected["witnessStates"]],
        lean.get("scenarioWitnessStates"),
    )

    # 6. sequence enumeration and aggregate counts
    report.add("optimalSequenceCount", expected["optimalSequenceCount"], lean.get("goalSeqCount"))
    report.add("distinctStatesTotal", expected["distinctStatesTotal"], lean.get("distinctStatesTotal"))
    report.add("expandedTransitions", expected["expandedTransitions"], lean.get("expandedTransitions"))
    return report


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def print_table(report: Report) -> None:
    name_width = max(len(c["check"]) for c in report.checks)
    for c in report.checks:
        status = "ok  " if c["ok"] else "FAIL"
        line = f"{status}  {c['check']:<{name_width}}  "
        if c["ok"]:
            print(line + _short(c["actual"]))
        else:
            print(line + f"expected {_short(c['expected'])} | lean {_short(c['actual'])}")


def _short(value: Any, limit: int = 90) -> str:
    text = json.dumps(value, ensure_ascii=False, sort_keys=True)
    return text if len(text) <= limit else text[: limit - 1] + "…"


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--fixture", default=str(FIXTURE_DEFAULT), help="fixture JSON path")
    parser.add_argument("--json", action="store_true", help="machine-readable result")
    parser.add_argument("--no-build", action="store_true", help="use the existing .olean")
    parser.add_argument("--force-build", action="store_true", help="rebuild even if the .olean is fresh")
    parser.add_argument("--keep-probe", metavar="PATH", help="copy the generated probe here")
    parser.add_argument("--timeout", type=float, default=300.0, help="per-command timeout (s)")
    parser.add_argument("--verbose", action="store_true", help="echo Lean build/probe output")
    parser.add_argument("--quiet", action="store_true", help="only print the verdict")
    args = parser.parse_args(list(argv) if argv is not None else None)

    try:
        doc = load_fixture(Path(args.fixture))
        expected = require_expected(doc)
        if not LEAN_ENV.exists() or not os.access(LEAN_ENV, os.X_OK):
            raise CheckError(f"Lean toolchain wrapper missing: {LEAN_ENV}", EXIT_TOOLCHAIN)
        horizon = int(expected["syntheticEarliestGoalTick"])
        probe_source = build_probe(horizon, expected["witness"])

        with tempfile.TemporaryDirectory(prefix="synthetic-check-") as tmp:
            probe = Path(tmp) / "SyntheticCheck.lean"
            probe.write_text(probe_source, encoding="utf-8")
            if args.keep_probe:
                Path(args.keep_probe).write_text(probe_source, encoding="utf-8")
            ensure_olean(args.no_build, args.force_build, args.timeout, args.verbose)
            lean = evaluate_probe(probe, args.timeout, args.verbose)

        try:
            report = compare(doc, lean)
        except (KeyError, TypeError) as exc:
            raise CheckError(
                f"fixture structure error while comparing: {exc!r}", EXIT_FIXTURE
            ) from exc
    except CheckError as exc:
        level = "ERROR" if exc.code != EXIT_MISMATCH else "MISMATCH"
        if args.json:
            print(json.dumps({"ok": False, "error": str(exc), "exitCode": exc.code}, indent=2))
        else:
            print(f"{level}: {exc}", file=sys.stderr)
        return exc.code
    except subprocess.TimeoutExpired as exc:
        message = f"timed out after {exc.timeout}s: {exc.cmd}"
        if args.json:
            print(json.dumps({"ok": False, "error": message, "exitCode": EXIT_LEAN}, indent=2))
        else:
            print(f"ERROR: {message}", file=sys.stderr)
        return EXIT_LEAN

    if args.json:
        print(
            json.dumps(
                {
                    "ok": report.ok,
                    "fixture": str(Path(args.fixture).resolve()),
                    "scenario": SCENARIO_MODULE,
                    "checks": report.checks,
                    "leanReportedAllSequences": lean.get("allSeqCount"),
                },
                indent=2,
            )
        )
    elif not args.quiet:
        print_table(report)
        print()
        verdict = "PASS" if report.ok else "FAIL"
        failed = sum(1 for c in report.checks if not c["ok"])
        print(
            f"{verdict}: {len(report.checks) - failed}/{len(report.checks)} checks agree "
            f"(fixture vs Lean {SCENARIO_MODULE}; synthetic benchmark, not Civ6)"
        )
    else:
        print("PASS" if report.ok else "FAIL")
    return EXIT_OK if report.ok else EXIT_MISMATCH


if __name__ == "__main__":
    sys.exit(main())
