#!/usr/bin/env python3
"""Cross-check the MVP Lean model against the Python executable and the fixture.

This is an integration drift check for the *conditional MVP model*
`M_MVP(theta*, sigma)` of `mvp/RULE-CONTRACT.md` v2.1. It is **not** a proof and
it makes no Civilization VI claim. The kernel-checked Lean theorems in
`Civ6Verify/Model/Mvp.lean` and `Civ6Verify/Bounds/MvpOptimality.lean` remain the
authority; this script only detects drift between:

  * the Lean step semantics (`step`, `legalGuard`, `legalActionsFor`, `run`),
  * the untrusted Python executable (`search/mvp.py`), and
  * the frozen untrusted candidate `fixtures/mvp-baseline.json`.

What is compared (all expectations are read from the fixture or computed by the
Python model, never re-typed here as the "right" answer)
---------------------------------------------------------------------------
1. Anchors: `init` / `(model p).init` vs `scenario.initialState`; Lean tile,
   centre, palace and threshold constants vs `scenario`; witness lengths vs
   `baseline.n` / `cost110.n`; `contractStyleWitness.finalState` vs the Lean
   evaluation of `run (model baselineParams) init witness`.
2. Per-step transitions of **both** fixture witnesses (`baseline.witness`,
   `cost110.witness`): pre/post states, action, `F`, `P`, `d`, `e`, `grew`,
   `q`, `credited`, `completed`, `extraProd`, and `t`. Each row is checked
   Lean-vs-fixture and Python-vs-fixture.
3. The contract-style witness (GH x7 IDLE then GH+PH SETTLER; baseline and
   cost-110) replayed through Lean and through Python, including the extra
   `prod_used` field, the final state, and `pop1QComputed`.
4. Finite legal actions for every distinct witness pre-state plus growth,
   completion and post-growth sample states: sorted action-id sets and counts,
   Lean baseline vs Python, Lean cost-110 vs Python, and baseline vs cost-110
   (the guard is cost-independent).
5. Step legality/outputs for the meaningful case list: growth with an extra
   tile, growth without extra, completion, and the invalid assignments
   (SETTLER at pop 1, worked-tile overflow, extra already worked, IDLE with
   extra, starving work set).
6. `#check` availability of the headline theorems (`optimalAt_baseline`,
   `optimalAt_cost110`, `noEarlier_20`, `noEarlier_25`, `witness_run`,
   `witness110_run`). This only shows the constant exists with the expected
   type and was built; it is **not** a substitute for the proof or for the
   axiom audit.

`--self-test` additionally mutates the Lean payload (never the repository) in
seven ways and asserts that the comparison detects every mutation, so a silent
"everything matches" cannot hide a broken comparator.

Exit codes
----------
0  all checks passed
1  at least one semantic mismatch
2  fixture missing / invalid / missing fields
3  Lean toolchain not found
4  Lean build or probe evaluation failed (e.g. MVP modules mid-edit)

Usage
-----
    python3 scripts/check-mvp.py
    python3 scripts/check-mvp.py --self-test        # real checks + negative tests
    python3 scripts/check-mvp.py --json
    python3 scripts/check-mvp.py --no-build         # use existing olean
    python3 scripts/check-mvp.py --lean-env scripts/lean-env
    python3 scripts/check-mvp.py --keep-probe /tmp/mvp-probe.lean

Toolchain selection: `--lean-env PATH` forces a wrapper (e.g.
`scripts/lean-env`); otherwise `--lake`/PATH `lake` is used and the project
wrapper is only a fallback. `scripts/verify.sh` prepends the resolved toolchain
bin directory to PATH, so `lake` (and hence this script) works in both toolchain
modes. The probe lives in a temporary directory outside the repository; the
only repository writes are `lake build` artifacts.
"""

from __future__ import annotations

import argparse
import copy
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURE_DEFAULT = REPO_ROOT / "fixtures" / "mvp-baseline.json"
MVP_MODULE = "Civ6Verify.Bounds.MvpOptimality"
MVP_FILE = REPO_ROOT / "Civ6Verify" / "Bounds" / "MvpOptimality.lean"
MODEL_FILE = REPO_ROOT / "Civ6Verify" / "Model" / "Mvp.lean"
ARITH_FILE = REPO_ROOT / "Civ6Verify" / "Bounds" / "MvpArithmetic.lean"
CORE_FILE = REPO_ROOT / "Civ6Verify" / "Reachability" / "Finite.lean"
OLEAN_FILE = (
    REPO_ROOT / ".lake" / "build" / "lib" / "lean" / "Civ6Verify" / "Bounds" / "MvpOptimality.olean"
)
LEAN_ENV = REPO_ROOT / "scripts" / "lean-env"
MARKER = "@@MVP-CHECK@@"

EXIT_OK = 0
EXIT_MISMATCH = 1
EXIT_FIXTURE = 2
EXIT_TOOLCHAIN = 3
EXIT_LEAN = 4

#: `#check` constants that must exist after importing MvpOptimality, with a
#: substring that must occur in the printed type. Availability only: the proof
#: itself is checked by `lake build` and `scripts/audit-axioms.py`.
EXPECTED_THEOREMS: Tuple[Tuple[str, str], ...] = (
    ("Civ6Verify.Bounds.MvpOptimality.optimalAt_baseline", "OptimalAt (model baselineParams) goal 20"),
    ("Civ6Verify.Bounds.MvpOptimality.optimalAt_cost110", "OptimalAt (model cost110Params) goal 25"),
    ("Civ6Verify.Bounds.MvpOptimality.noEarlier_20", "NoEarlier"),
    ("Civ6Verify.Bounds.MvpOptimality.noEarlier_25", "NoEarlier"),
    ("Civ6Verify.Model.Mvp.witness_run", "food := 1430"),
    ("Civ6Verify.Model.Mvp.witness110_run", "food := 1980"),
)

#: Table-driven step cases. Each is (name, state, (mask, extra, build)).
#: The first five are invalid assignments; the last three are positive controls
#: covering growth with/without an extra tile and a completion step.
STEP_CASES: Tuple[Tuple[str, Tuple[int, int, int, int], Tuple[int, Optional[int], str]], ...] = (
    ("invalid_settler_at_pop1", (1, 0, 0, 0), (2, None, "SETTLER")),
    ("invalid_capacity_exceeded", (1, 1320, 0, 0), (3, None, "IDLE")),
    ("invalid_extra_already_worked", (2, 0, 0, 0), (6, 2, "SETTLER")),
    ("invalid_idle_with_extra", (2, 0, 0, 0), (2, 3, "IDLE")),
    ("invalid_starving_work_set", (2, 0, 0, 0), (4, None, "SETTLER")),
    ("growth_with_extra", (2, 2300, 0, 0), (6, 3, "SETTLER")),
    ("growth_idle_no_extra", (1, 1320, 0, 0), (2, None, "IDLE")),
    ("completion_step", (2, 0, 7560, 0), (12, None, "SETTLER")),
)

TRACE_FIELDS = (
    "t",
    "pre",
    "action",
    "F",
    "P",
    "d",
    "e",
    "grew",
    "q",
    "credited",
    "completed",
    "extraProd",
    "post",
)

PY_TRACE_FIELDS = (
    "F",
    "P",
    "Pused",
    "d",
    "e",
    "grew",
    "q",
    "credited",
    "completed",
    "extraProd",
    "post",
)

LEAN_FIELD_OF_PY = {
    "F": "food_yield",
    "P": "prod_base",
    "Pused": "prod_used",
    "d": "surplus",
    "e": "growth",
}


class CheckError(Exception):
    """Fatal setup problem carrying the intended exit code."""

    def __init__(self, message: str, code: int) -> None:
        super().__init__(message)
        self.code = code


# ---------------------------------------------------------------------------
# fixture side
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


def require_path(doc: Dict[str, Any], dotted: str) -> Any:
    node: Any = doc
    for part in dotted.split("."):
        if not isinstance(node, dict) or part not in node:
            raise CheckError(f"fixture is missing `{dotted}`", EXIT_FIXTURE)
        node = node[part]
    return node


def validate_fixture(doc: Dict[str, Any]) -> None:
    for dotted in (
        "scenario.initialState",
        "scenario.tileFood",
        "scenario.tileProduction",
        "scenario.centerFood",
        "scenario.baseProduction",
        "scenario.thresholds",
        "baseline.theta",
        "baseline.n",
        "baseline.goalState",
        "baseline.witness",
        "cost110.theta",
        "cost110.n",
        "cost110.goalState",
        "cost110.witness",
        "contractStyleWitness.n",
        "contractStyleWitness.finalState",
        "contractStyleWitness.pop1QComputed",
    ):
        require_path(doc, dotted)
    for key in ("baseline", "cost110"):
        witness = doc[key]["witness"]
        if not isinstance(witness, list) or not witness:
            raise CheckError(f"fixture `{key}.witness` must be a non-empty list", EXIT_FIXTURE)
        for i, row in enumerate(witness):
            for field in ("t", "pre", "action", "F", "P", "d", "e", "grew",
                          "q", "credited", "completed", "extraProd", "post"):
                if field not in row:
                    raise CheckError(
                        f"fixture `{key}.witness[{i}]` is missing `{field}`", EXIT_FIXTURE
                    )
            if "workMask" not in row["action"]:
                raise CheckError(
                    f"fixture `{key}.witness[{i}].action` has no `workMask`", EXIT_FIXTURE
                )


# ---------------------------------------------------------------------------
# shared encodings (must match the generated Lean probe)
# ---------------------------------------------------------------------------


def state_id(state: Sequence[int]) -> str:
    return ",".join(str(int(x)) for x in state)


def parse_state(text: str) -> Tuple[int, int, int, int]:
    parts = text.split(",")
    if len(parts) != 4:
        raise ValueError(f"bad state encoding {text!r}")
    return (int(parts[0]), int(parts[1]), int(parts[2]), int(parts[3]))


def action_id(mask: int, extra: Optional[int], build: str) -> str:
    return f"{int(mask)}:{'-' if extra is None else int(extra)}:{build}"


def parse_action(text: str) -> Tuple[int, Optional[int], str]:
    mask_s, extra_s, build = text.split(":")
    return (int(mask_s), None if extra_s == "-" else int(extra_s), build)


def fixture_action_id(row: Dict[str, Any]) -> str:
    action = row["action"]
    return action_id(action["workMask"], action.get("extra"), action["build"])


def fixture_state(row_state: Sequence[int]) -> Tuple[int, int, int, int]:
    return (int(row_state[0]), int(row_state[1]), int(row_state[2]), int(row_state[3]))


def fixture_theta(doc_theta: Dict[str, Any]) -> Any:
    import mvp  # local import so --help works without the search module

    return mvp.Theta(
        settler_cost=int(doc_theta["settlerCost"]) * 100,
        turn_order=str(doc_theta["turnOrder"]),
        new_citizen=str(doc_theta["newCitizen"]),
        amenity_stock=int(doc_theta["amenityStock"]),
        basket_on_growth=str(doc_theta["basketOnGrowth"]),
        production_rounding=str(doc_theta["productionRounding"]),
        threshold_rounding=str(doc_theta["thresholdRounding"]),
    )


def python_legal_actions(mvp_mod: Any, theta: Any, state: Sequence[int]) -> List[str]:
    """The full 160-candidate box filtered by the Python `legal` predicate."""
    out: List[str] = []
    for mask in range(16):
        for extra in (None, 0, 1, 2, 3):
            for build in ("IDLE", "SETTLER"):
                action = mvp_mod.Action(mask, extra, build)
                if mvp_mod.legal(theta, mvp_mod.State(*state), action):
                    out.append(action_id(mask, extra, build))
    return out


def python_guard_parts(mvp_mod: Any, state: Sequence[int],
                       mask: int, extra: Optional[int], build: str) -> Dict[str, Any]:
    pop = state[0]
    size, food_sum, _ = mvp_mod.WORK_META[mask]
    return {
        "workCount": size,
        "capacity": size <= pop,
        "extraOk": extra is None or (0 <= extra < 4 and not (mask >> extra) & 1),
        "settlerOk": build != "SETTLER" or pop >= 2,
        "idleOk": build != "IDLE" or extra is None,
        "starveOk": mvp_mod.SCENARIO.center_food + food_sum - 200 * pop >= 0,
    }


# ---------------------------------------------------------------------------
# probe generation
# ---------------------------------------------------------------------------


def lean_actions(actions: Iterable[Tuple[int, Optional[int], str]]) -> str:
    parts = []
    for mask, extra, build in actions:
        extra_s = "none" if extra is None else f"some {int(extra)}"
        parts.append(f'({int(mask)}, {extra_s}, "{build}")')
    return "[" + ", ".join(parts) + "]"


def lean_state(state: Sequence[int]) -> str:
    return (
        "{ pop := %d, food := %d, prog := %d, trained := %d }"
        % (state[0], state[1], state[2], state[3])
    )


PROBE_TEMPLATE = r"""import Lean.Data.Json
import Civ6Verify.Model.Mvp
import Civ6Verify.Bounds.MvpOptimality

open Lean
open Civ6Verify.Reachability
open Civ6Verify.Model.Mvp
open Civ6Verify.Bounds.MvpOptimality

#check Civ6Verify.Bounds.MvpOptimality.optimalAt_baseline
#check Civ6Verify.Bounds.MvpOptimality.optimalAt_cost110
#check Civ6Verify.Bounds.MvpOptimality.noEarlier_20
#check Civ6Verify.Bounds.MvpOptimality.noEarlier_25
#check Civ6Verify.Model.Mvp.witness_run
#check Civ6Verify.Model.Mvp.witness110_run

namespace MvpCheck

/-- Canonical state encoding `pop,food,prog,trained` (shared with the script). -/
def stateStr (s : State) : String :=
  s!"{s.pop},{s.food},{s.prog},{s.trained}"

/-- Canonical action encoding `mask:extra:build`, extra `-` for none. -/
def actionStr (a : Action) : String :=
  let e := match a.extra with
    | none => "-"
    | some t => toString t.val
  let b := match a.build with
    | .idle => "IDLE"
    | .settler => "SETTLER"
  s!"{a.work.val}:{e}:{b}"

/-- Build a model `Action` from the fixture/Python triple.  `w % 16` and
`t % 4` only discharge the `Fin` bounds; injected values are already in range. -/
def mkAction (w : Nat) (e : Option Nat) (b : String) : Action :=
  { work := ⟨w % 16, Nat.mod_lt _ (by decide)⟩
    extra := e.map (fun t => (⟨t % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4))
    build := if b = "SETTLER" then Build.settler else Build.idle }

structure Row where
  t : Nat
  pre : State
  action : Action
  F : Nat
  P : Nat
  Pused : Nat
  d : Nat
  e : Nat
  grew : Bool
  q : Nat
  credited : Nat
  completed : Bool
  extraProd : Nat
  post : State

/-- Per-step trace of a concrete action list, using only model definitions. -/
def traceFrom (p : Params) (s : State) (as : List Action) : List Row :=
  match as with
  | [] => []
  | a :: rest =>
      let grew := wouldGrow s a
      let post := step p s a
      { t := 1, pre := s, action := a, F := baseFood a, P := baseProd a,
        Pused := production s a, d := surplus s a, e := growthAmount s a,
        grew := grew, q := qOf s a, credited := credit a (qOf s a),
        completed := decide (completes p s a),
        extraProd := if grew then extraGain a else 0, post := post } ::
      (traceFrom p post rest).map (fun r => { r with t := r.t + 1 })

def rowJson (r : Row) : Json :=
  Json.mkObj
    [ ("t", toJson r.t)
    , ("pre", Json.str (stateStr r.pre))
    , ("action", Json.str (actionStr r.action))
    , ("F", toJson r.F)
    , ("P", toJson r.P)
    , ("Pused", toJson r.Pused)
    , ("d", toJson r.d)
    , ("e", toJson r.e)
    , ("grew", toJson r.grew)
    , ("q", toJson r.q)
    , ("credited", toJson r.credited)
    , ("completed", toJson r.completed)
    , ("extraProd", toJson r.extraProd)
    , ("post", Json.str (stateStr r.post)) ]

def traceJson (p : Params) (s : State) (as : List Action) : Json :=
  Json.arr ((traceFrom p s as).map rowJson |>.toArray)

def legalIds (p : Params) (s : State) : List String :=
  (legalActionsFor p s).map actionStr

def sampleStates : List (String × State) :=
  [__SAMPLE_STATES__]

def caseSpec : List (String × State × Action) :=
  [__CASES__]

def legalBlock (p : Params) : Json :=
  Json.mkObj (sampleStates.map (fun (_k, s) => (stateStr s, toJson (legalIds p s))))

def caseJson (p : Params) (spec : String × State × Action) : Json :=
  match spec with
  | (name, s, a) =>
      let ok : Bool := (step? p s a).isSome
      Json.mkObj
        [ ("name", Json.str name)
        , ("state", Json.str (stateStr s))
        , ("action", Json.str (actionStr a))
        , ("legal", toJson ok)
        , ("guard", toJson (decide (legalGuard s a)))
        , ("workCount", toJson (workCount a))
        , ("capacity", toJson (decide (workCount a ≤ s.pop)))
        , ("extraOk", toJson (extraUnworked a))
        , ("settlerOk", toJson (decide (a.build = Build.settler → 2 ≤ s.pop)))
        , ("idleOk", toJson (decide (a.build = Build.idle → a.extra = none)))
        , ("starveOk", toJson (decide (200 * s.pop ≤ baseFood a)))
        , ("row",
            match traceFrom p s [a] with
            | r :: _ => if ok then rowJson r else Json.null
            | [] => Json.null) ]

def bWitnessActions : List Action :=
  (__BASELINE_ACTIONS__).map (fun (w, e, b) => mkAction w e b)

def cWitnessActions : List Action :=
  (__COST110_ACTIONS__).map (fun (w, e, b) => mkAction w e b)

def contractActions : List Action :=
  (__CONTRACT_ACTIONS__).map (fun (w, e, b) => mkAction w e b)

def contract110Actions : List Action :=
  (__CONTRACT110_ACTIONS__).map (fun (w, e, b) => mkAction w e b)

def payload : Json :=
  Json.mkObj
    [ ("init", Json.str (stateStr init))
    , ("initBaselineModel", Json.str (stateStr (model baselineParams).init))
    , ("initCost110Model", Json.str (stateStr (model cost110Params).init))
    , ("tileFood", toJson ((List.finRange 4).map tileFood))
    , ("tileProd", toJson ((List.finRange 4).map tileProd))
    , ("baseFoodEmpty", toJson (baseFood (mkAction 0 none "IDLE")))
    , ("baseProdEmpty", toJson (baseProd (mkAction 0 none "IDLE")))
    , ("thresholds", toJson [threshold 1, threshold 2, threshold 3, threshold 4])
    , ("witnessLength", toJson witness.length)
    , ("witness110Length", toJson witness110.length)
    , ("witnessRun", Json.str (stateStr (run (model baselineParams) init witness)))
    , ("witness110Run", Json.str (stateStr (run (model cost110Params) init witness110)))
    , ("witnessLegal", toJson (legalPathB baselineParams init witness))
    , ("witness110Legal", toJson (legalPathB cost110Params init witness110))
    , ("traces", Json.mkObj
        [ ("baselineWitness", traceJson baselineParams init bWitnessActions)
        , ("cost110Witness", traceJson cost110Params init cWitnessActions)
        , ("contractStyle", traceJson baselineParams init contractActions)
        , ("contractStyle110", traceJson cost110Params init contract110Actions) ])
    , ("legalBaseline", legalBlock baselineParams)
    , ("legalCost110", legalBlock cost110Params)
    , ("casesBaseline", Json.arr ((caseSpec.map (caseJson baselineParams)).toArray))
    , ("casesCost110", Json.arr ((caseSpec.map (caseJson cost110Params)).toArray)) ]

end MvpCheck

#eval IO.println s!"@@MVP-CHECK@@{MvpCheck.payload.compress}"
"""


def build_probe(doc: Dict[str, Any], mvp_mod: Any) -> str:
    baseline_theta = fixture_theta(doc["baseline"]["theta"])
    cost110_theta = fixture_theta(doc["cost110"]["theta"])
    baseline_actions = [
        (row["action"]["workMask"], row["action"].get("extra"), row["action"]["build"])
        for row in doc["baseline"]["witness"]
    ]
    cost110_actions = [
        (row["action"]["workMask"], row["action"].get("extra"), row["action"]["build"])
        for row in doc["cost110"]["witness"]
    ]
    contract_rows = mvp_mod.contract_style_path(baseline_theta)
    contract110_rows = mvp_mod.contract_style_path(cost110_theta)
    contract_actions = [(a.work, a.extra, a.build) for _, _, a, _ in contract_rows]
    contract110_actions = [(a.work, a.extra, a.build) for _, _, a, _ in contract110_rows]

    # Distinct witness pre-states, both witnesses, plus important post-states.
    states: List[Tuple[str, Tuple[int, int, int, int]]] = []
    seen: Dict[Tuple[int, int, int, int], str] = {}

    def add_state(tag: str, state: Sequence[int]) -> None:
        key = (int(state[0]), int(state[1]), int(state[2]), int(state[3]))
        if key not in seen:
            seen[key] = tag
            states.append((tag, key))

    add_state("init", doc["scenario"]["initialState"])
    for key in ("baseline", "cost110"):
        for row in doc[key]["witness"]:
            add_state(f"{key}_pre", row["pre"])
            add_state(f"{key}_post", row["post"])
    add_state("contract_final", contract_rows[-1][3])
    add_state("contract110_final", contract110_rows[-1][3])
    for name, state, (mask, extra, build) in STEP_CASES:
        add_state(name, state)
        post = mvp_mod.step(baseline_theta, mvp_mod.State(*state), mvp_mod.Action(mask, extra, build))
        if post is not None:
            add_state(f"{name}_post", tuple(post))
    # Cap the sample deterministically; keep init/growth/completion states.
    if len(states) > 40:
        keep = [states[0]] + [st for st in states if "pre" in st[0]][:24] + states[-8:]
        uniq: List[Tuple[str, Tuple[int, int, int, int]]] = []
        keys = set()
        for tag, st in keep:
            if st not in keys:
                keys.add(st)
                uniq.append((tag, st))
        states = uniq
    sample_literal = ", ".join(
        '("%s", %s)' % (tag, lean_state(st)) for tag, st in states
    )
    cases_literal = ", ".join(
        '("%s", %s, mkAction %d (%s) "%s")'
        % (
            name,
            lean_state(state),
            mask,
            "none" if extra is None else f"some {extra}",
            build,
        )
        for name, state, (mask, extra, build) in STEP_CASES
    )
    return (
        PROBE_TEMPLATE.replace("__BASELINE_ACTIONS__", lean_actions(baseline_actions))
        .replace("__COST110_ACTIONS__", lean_actions(cost110_actions))
        .replace("__CONTRACT_ACTIONS__", lean_actions(contract_actions))
        .replace("__CONTRACT110_ACTIONS__", lean_actions(contract110_actions))
        .replace("__SAMPLE_STATES__", sample_literal)
        .replace("__CASES__", cases_literal)
    )


# ---------------------------------------------------------------------------
# Lean invocation
# ---------------------------------------------------------------------------


def subprocess_env() -> Dict[str, str]:
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    return env


def run_command(cmd: Sequence[str], timeout: float, verbose: bool) -> subprocess.CompletedProcess:
    proc = subprocess.run(
        list(cmd),
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
        env=subprocess_env(),
    )
    if verbose:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
    return proc


def tail(text: str, limit: int = 4000) -> str:
    text = text.strip()
    return text if len(text) <= limit else "...\n" + text[-limit:]


def resolve_lake(args: argparse.Namespace) -> List[str]:
    if args.lean_env:
        wrapper = Path(args.lean_env)
        if not wrapper.is_file():
            raise CheckError(f"--lean-env is not a file: {wrapper}", EXIT_TOOLCHAIN)
        if not os.access(wrapper, os.X_OK):
            raise CheckError(f"--lean-env is not executable: {wrapper}", EXIT_TOOLCHAIN)
        return [str(wrapper), "lake"]
    if args.lake != "lake":
        if not (shutil.which(args.lake) or Path(args.lake).is_file()):
            raise CheckError(f"lake executable not found: {args.lake}", EXIT_TOOLCHAIN)
        return [args.lake]
    found = shutil.which("lake")
    if found:
        return [found]
    if LEAN_ENV.is_file() and os.access(LEAN_ENV, os.X_OK):
        return [str(LEAN_ENV), "lake"]
    raise CheckError(
        "lake not found on PATH and project-local scripts/lean-env is unavailable; "
        "run scripts/verify.sh or install the pinned Lean toolchain",
        EXIT_TOOLCHAIN,
    )


def needs_build() -> bool:
    if not OLEAN_FILE.exists():
        return True
    olean_mtime = OLEAN_FILE.stat().st_mtime
    return any(
        source.exists() and source.stat().st_mtime > olean_mtime
        for source in (MVP_FILE, MODEL_FILE, ARITH_FILE, CORE_FILE)
    )


def ensure_olean(lake: List[str], args: argparse.Namespace) -> None:
    if args.no_build or not (args.force_build or needs_build()):
        if not OLEAN_FILE.exists():
            raise CheckError(
                f"--no-build was given but {OLEAN_FILE} does not exist; "
                f"build with `lake build {MVP_MODULE}`",
                EXIT_LEAN,
            )
        return
    proc = run_command([*lake, "build", MVP_MODULE], args.timeout, args.verbose)
    if proc.returncode != 0:
        raise CheckError(
            f"Lean build of {MVP_MODULE} failed (exit {proc.returncode}); "
            "the MVP modules may be mid-edit. This script never edits them.\n"
            f"{tail(proc.stderr or proc.stdout)}",
            EXIT_LEAN,
        )


def merge_check_lines(stdout: str) -> List[str]:
    lines: List[str] = []
    for line in stdout.splitlines():
        if line[:1].isspace() and lines:
            lines[-1] = lines[-1] + " " + line.strip()
        elif line.strip():
            lines.append(line.strip())
    return lines


def parse_theorem_checks(stdout: str) -> Dict[str, str]:
    """Map expected theorem name -> merged `#check` line (binders included)."""
    merged = merge_check_lines(stdout)
    found: Dict[str, str] = {}
    for name, _ in EXPECTED_THEOREMS:
        for line in merged:
            if not line.startswith(name):
                continue
            rest = line[len(name):]
            if rest == "" or rest[:1] in (" ", "(", ":"):
                found[name] = line
                break
    return found


def evaluate_probe(probe: Path, lake: List[str], args: argparse.Namespace) -> Tuple[Dict[str, Any], Dict[str, str]]:
    proc = run_command([*lake, "env", "lean", str(probe)], args.timeout, args.verbose)
    if proc.returncode != 0:
        raise CheckError(
            f"Lean probe failed (exit {proc.returncode}); the MVP model or lower-bound "
            f"API may have been renamed.\n{tail(proc.stderr or proc.stdout)}",
            EXIT_LEAN,
        )
    payloads = [
        line[len(MARKER):] for line in proc.stdout.splitlines() if line.startswith(MARKER)
    ]
    if not payloads:
        raise CheckError(
            f"Lean probe produced no payload line ({MARKER}...); stdout tail:\n"
            f"{tail(proc.stdout)}",
            EXIT_LEAN,
        )
    try:
        payload = json.loads(payloads[-1])
    except json.JSONDecodeError as exc:
        raise CheckError(f"probe payload is not valid JSON: {exc}", EXIT_LEAN) from exc
    return payload, parse_theorem_checks(proc.stdout)


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

    def add_many(self, prefix: str, expected: Dict[str, Any], actual: Dict[str, Any]) -> None:
        for key, value in expected.items():
            self.add(f"{prefix}.{key}", value, actual.get(key))

    @property
    def failures(self) -> List[Dict[str, Any]]:
        return [c for c in self.checks if not c["ok"]]

    @property
    def ok(self) -> bool:
        return not self.failures


def python_step_fields(mvp_mod: Any, theta: Any, state: Sequence[int],
                       action: Tuple[int, Optional[int], str]) -> Optional[Dict[str, Any]]:
    info = mvp_mod.explain_step(theta, mvp_mod.State(*state), mvp_mod.Action(*action))
    if info is None:
        return None
    return {
        "F": info.food_yield,
        "P": info.prod_base,
        "Pused": info.prod_used,
        "d": info.surplus,
        "e": info.growth,
        "grew": info.grew,
        "q": info.q,
        "credited": info.credited,
        "completed": info.completed,
        "extraProd": info.extra_prod,
        "post": state_id(info.state),
    }


def lean_row_fields(row: Dict[str, Any]) -> Dict[str, Any]:
    return {field: row[field] for field in PY_TRACE_FIELDS}


def compare_witness_trace(report: Report, label: str, fixture_rows: Sequence[Dict[str, Any]],
                          lean_rows: Sequence[Dict[str, Any]], mvp_mod: Any, theta: Any) -> None:
    report.add(f"trace.{label}.length", len(fixture_rows), len(lean_rows))
    for index, (fixture_row, lean_row) in enumerate(zip(fixture_rows, lean_rows)):
        prefix = f"trace.{label}[{index}]"
        for field in TRACE_FIELDS:
            if field == "pre":
                expected = state_id(fixture_state(fixture_row["pre"]))
            elif field == "post":
                expected = state_id(fixture_state(fixture_row["post"]))
            elif field == "action":
                expected = fixture_action_id(fixture_row)
            else:
                expected = fixture_row[field]
            report.add(f"{prefix}.{field}", expected, lean_row[field])
        # Python executable vs the same frozen row.
        action = parse_action(fixture_action_id(fixture_row))
        py = python_step_fields(mvp_mod, theta, fixture_state(fixture_row["pre"]), action)
        if py is None:
            report.add(f"{prefix}.python.legal", True, False)
            continue
        report.add(f"{prefix}.python.post", state_id(fixture_state(fixture_row["post"])), py["post"])
        for field in ("F", "P", "d", "e", "grew", "q", "credited", "completed", "extraProd"):
            report.add(f"{prefix}.python.{field}", fixture_row[field], py[field])


def compare_contract_trace(report: Report, label: str, lean_rows: Sequence[Dict[str, Any]],
                           path: Sequence[Tuple[int, Any, Any, Any]], mvp_mod: Any,
                           theta: Any) -> None:
    report.add(f"contract.{label}.length", len(path), len(lean_rows))
    for index, ((t, pre, action, post), lean_row) in enumerate(zip(path, lean_rows)):
        prefix = f"contract.{label}[{index}]"
        report.add(f"{prefix}.t", t, lean_row["t"])
        report.add(f"{prefix}.pre", state_id(pre), lean_row["pre"])
        report.add(f"{prefix}.action", action_id(action.work, action.extra, action.build),
                   lean_row["action"])
        report.add(f"{prefix}.post", state_id(post), lean_row["post"])
        py = python_step_fields(mvp_mod, theta, pre, (action.work, action.extra, action.build))
        if py is None:
            report.add(f"{prefix}.python.legal", True, False)
            continue
        report.add_many(f"{prefix}.python", lean_row_fields(lean_row), py)


def compare_legal_sets(report: Report, label: str, lean_legal: Dict[str, List[str]],
                       python_legal: Dict[str, List[str]]) -> None:
    report.add(f"legal.{label}.states", sorted(lean_legal), sorted(python_legal))
    for key in sorted(set(lean_legal) & set(python_legal)):
        lean_ids = lean_legal[key]
        py_ids = python_legal[key]
        report.add(f"legal.{label}.{key}.count", len(py_ids), len(lean_ids))
        report.add(f"legal.{label}.{key}.set", sorted(py_ids), sorted(lean_ids))
        report.add(f"legal.{label}.{key}.noDuplicates", len(lean_ids), len(set(lean_ids)))
        report.add(f"legal.{label}.{key}.withinBox", True, len(lean_ids) <= 160)


def compare_cases(report: Report, label: str, lean_cases: Sequence[Dict[str, Any]],
                  mvp_mod: Any, theta: Any) -> None:
    by_name = {case.get("name"): case for case in lean_cases}
    for name, state, action in STEP_CASES:
        case = by_name.get(name)
        if case is None:
            report.add(f"cases.{label}.{name}.present", True, False)
            continue
        prefix = f"cases.{label}.{name}"
        report.add(f"{prefix}.state", state_id(state), case["state"])
        report.add(f"{prefix}.action", action_id(*action), case["action"])
        parts = python_guard_parts(mvp_mod, state, *action)
        for field, expected in parts.items():
            report.add(f"{prefix}.guard.{field}", expected, case.get(field))
        py = python_step_fields(mvp_mod, theta, state, action)
        report.add(f"{prefix}.legal", py is not None, case["legal"])
        report.add(f"{prefix}.guard.conjunction", py is not None, case["guard"])
        if py is None:
            report.add(f"{prefix}.row", None, case["row"])
        else:
            report.add(f"{prefix}.row.present", True, case["row"] is not None)
            if case["row"] is not None:
                report.add_many(f"{prefix}.row.python", lean_row_fields(case["row"]), py)


def build_report(doc: Dict[str, Any], payload: Dict[str, Any],
                 theorems: Dict[str, str], mvp_mod: Any) -> Report:
    report = Report()

    # -- fixture anchors ----------------------------------------------------
    scenario = doc["scenario"]
    report.add("anchor.initialState", state_id(fixture_state(scenario["initialState"])),
               payload.get("init"))
    report.add("anchor.modelInit.baseline", payload.get("init"),
               payload.get("initBaselineModel"))
    report.add("anchor.modelInit.cost110", payload.get("init"),
               payload.get("initCost110Model"))
    report.add("anchor.tileFood", list(scenario["tileFood"]), payload.get("tileFood"))
    report.add("anchor.tileProd", list(scenario["tileProduction"]), payload.get("tileProd"))
    report.add("anchor.centerFood", int(scenario["centerFood"]), payload.get("baseFoodEmpty"))
    report.add("anchor.baseProduction", int(scenario["baseProduction"]), payload.get("baseProdEmpty"))
    thresholds = scenario["thresholds"]
    report.add(
        "anchor.thresholds",
        [thresholds["1"], thresholds["2"], thresholds["3Exact"], thresholds["4"]],
        payload.get("thresholds"),
    )
    report.add("anchor.witnessLength", int(doc["baseline"]["n"]), payload.get("witnessLength"))
    report.add("anchor.witness110Length", int(doc["cost110"]["n"]), payload.get("witness110Length"))
    report.add("anchor.witnessLegal", True, payload.get("witnessLegal"))
    report.add("anchor.witness110Legal", True, payload.get("witness110Legal"))
    report.add("anchor.contractStyleWitness.n", int(doc["contractStyleWitness"]["n"]),
               payload.get("witnessLength"))
    report.add(
        "anchor.contractStyleWitness.finalState",
        state_id(fixture_state(doc["contractStyleWitness"]["finalState"])),
        payload.get("witnessRun"),
    )
    report.add("anchor.baseline.goalState", state_id(fixture_state(doc["baseline"]["goalState"])),
               state_id(fixture_state(doc["baseline"]["witness"][-1]["post"])))
    report.add("anchor.cost110.goalState", state_id(fixture_state(doc["cost110"]["goalState"])),
               state_id(fixture_state(doc["cost110"]["witness"][-1]["post"])))

    # -- per-step fixture witnesses ----------------------------------------
    traces = payload.get("traces", {})
    compare_witness_trace(
        report, "baselineWitness", doc["baseline"]["witness"],
        traces.get("baselineWitness", []), mvp_mod, fixture_theta(doc["baseline"]["theta"]),
    )
    compare_witness_trace(
        report, "cost110Witness", doc["cost110"]["witness"],
        traces.get("cost110Witness", []), mvp_mod, fixture_theta(doc["cost110"]["theta"]),
    )

    # -- contract-style witness (GH x7 IDLE, then GH+PH SETTLER) -----------
    baseline_theta = fixture_theta(doc["baseline"]["theta"])
    cost110_theta = fixture_theta(doc["cost110"]["theta"])
    baseline_path = mvp_mod.contract_style_path(baseline_theta)
    cost110_path = mvp_mod.contract_style_path(cost110_theta)
    compare_contract_trace(report, "baseline", traces.get("contractStyle", []),
                           baseline_path, mvp_mod, baseline_theta)
    compare_contract_trace(report, "cost110", traces.get("contractStyle110", []),
                           cost110_path, mvp_mod, cost110_theta)
    report.add("contract.baseline.finalState", state_id(baseline_path[-1][3]),
               payload.get("witnessRun"))
    report.add("contract.cost110.finalState", state_id(cost110_path[-1][3]),
               payload.get("witness110Run"))
    contract_rows = traces.get("contractStyle", [])
    growth_rows = [row for row in contract_rows if row.get("grew")]
    growth_q = growth_rows[0]["q"] if growth_rows else None
    report.add("contract.baseline.pop1QComputed",
               int(doc["contractStyleWitness"]["pop1QComputed"]), growth_q)

    # -- finite legal action sets -----------------------------------------
    lean_legal_baseline = payload.get("legalBaseline", {})
    lean_legal_cost110 = payload.get("legalCost110", {})
    checked = sorted(set(lean_legal_baseline) & set(lean_legal_cost110))
    python_baseline = {
        key: python_legal_actions(mvp_mod, baseline_theta, parse_state(key)) for key in checked
    }
    python_cost110 = {
        key: python_legal_actions(mvp_mod, cost110_theta, parse_state(key)) for key in checked
    }
    compare_legal_sets(report, "baseline", {k: lean_legal_baseline[k] for k in checked},
                       python_baseline)
    compare_legal_sets(report, "cost110", {k: lean_legal_cost110[k] for k in checked},
                       python_cost110)
    report.add(
        "legal.costIndependence",
        {k: sorted(lean_legal_baseline[k]) for k in checked},
        {k: sorted(lean_legal_cost110[k]) for k in checked},
    )

    # -- case list: invalid assignments + positive controls ----------------
    compare_cases(report, "baseline", payload.get("casesBaseline", []), mvp_mod, baseline_theta)
    compare_cases(report, "cost110", payload.get("casesCost110", []), mvp_mod, cost110_theta)
    report.add(
        "cases.legalFlagsCostIndependent",
        {c["name"]: c["legal"] for c in payload.get("casesBaseline", [])},
        {c["name"]: c["legal"] for c in payload.get("casesCost110", [])},
    )

    # -- #check availability (availability only, not a proof) --------------
    for name, expected_substring in EXPECTED_THEOREMS:
        kind = theorems.get(name)
        report.add(f"theorem.{name}.present", True, kind is not None)
        report.add(f"theorem.{name}.type", True,
                   kind is not None and expected_substring in kind)
    return report


# ---------------------------------------------------------------------------
# negative self-test
# ---------------------------------------------------------------------------


def negative_mutations(payload: Dict[str, Any], theorems: Dict[str, str]) -> List[Tuple[str, Any, Any]]:
    """(label, mutated_payload, mutated_theorems) cases the report must reject."""

    def mutate(fn: Any) -> Dict[str, Any]:
        clone = copy.deepcopy(payload)
        fn(clone)
        return clone

    cases: List[Tuple[str, Any, Any]] = []

    def bump_q(data: Dict[str, Any]) -> None:
        data["traces"]["baselineWitness"][0]["q"] += 1

    cases.append(("trace q off by one", mutate(bump_q), theorems))

    def change_init(data: Dict[str, Any]) -> None:
        data["init"] = "1,1,0,0"

    cases.append(("initial state changed", mutate(change_init), theorems))

    def drop_legal(data: Dict[str, Any]) -> None:
        key = sorted(data["legalBaseline"])[0]
        data["legalBaseline"][key] = data["legalBaseline"][key][1:]

    cases.append(("legal action dropped", mutate(drop_legal), theorems))

    def wrong_final(data: Dict[str, Any]) -> None:
        data["traces"]["contractStyle"][-1]["post"] = "1,1430,190,0"

    cases.append(("contract final state changed", mutate(wrong_final), theorems))

    def flip_case(data: Dict[str, Any]) -> None:
        for case in data["casesBaseline"]:
            if case["name"].startswith("invalid_"):
                case["legal"] = not case["legal"]

    cases.append(("invalid case marked legal", mutate(flip_case), theorems))

    def change_threshold(data: Dict[str, Any]) -> None:
        data["thresholds"][2] += 1

    cases.append(("T3 exact threshold changed", mutate(change_threshold), theorems))

    missing = dict(theorems)
    missing.pop("Civ6Verify.Bounds.MvpOptimality.optimalAt_cost110", None)
    cases.append(("theorem check missing", payload, missing))
    return cases


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def summarize(report: Report, label: str) -> None:
    total = len(report.checks)
    failures = report.failures
    print(f"{label}: {total - len(failures)}/{total} checks passed")
    if failures:
        shown = 0
        for failure in failures:
            print(
                f"  FAIL {failure['check']}: expected {failure['expected']!r} "
                f"got {failure['actual']!r}",
                file=sys.stderr,
            )
            shown += 1
            if shown >= 25 and len(failures) > shown:
                print(f"  ... {len(failures) - shown} more failures (use --json)",
                      file=sys.stderr)
                break


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Cross-check the MVP Lean model against search/mvp.py and the fixture.",
    )
    parser.add_argument("--fixture", default=str(FIXTURE_DEFAULT),
                        help="fixture path (default: fixtures/mvp-baseline.json)")
    parser.add_argument("--lean-env", metavar="PATH",
                        help="Lean wrapper to run (e.g. scripts/lean-env); default: lake on PATH")
    parser.add_argument("--lake", default="lake", help="lake executable (default: lake)")
    parser.add_argument("--no-build", action="store_true", help="use existing .olean files")
    parser.add_argument("--force-build", action="store_true", help="rebuild MvpOptimality")
    parser.add_argument("--self-test", action="store_true",
                        help="run the real checks plus negative mismatch-detection tests")
    parser.add_argument("--json", action="store_true", help="machine-readable report")
    parser.add_argument("--verbose", action="store_true", help="echo Lean output")
    parser.add_argument("--keep-probe", metavar="PATH", help="keep the generated probe")
    parser.add_argument("--timeout", type=float, default=600.0,
                        help="per-command timeout in seconds (default: 600)")
    args = parser.parse_args(list(argv) if argv is not None else None)

    start = time.time()
    try:
        sys.path.insert(0, str(REPO_ROOT / "search"))
        import mvp as mvp_mod  # noqa: WPS433 (deliberate local import)

        doc = load_fixture(Path(args.fixture))
        validate_fixture(doc)
        lake = resolve_lake(args)
        ensure_olean(lake, args)
        probe_source = build_probe(doc, mvp_mod)

        with tempfile.TemporaryDirectory(prefix="civ6-mvp-check-") as tmp:
            probe = Path(tmp) / "MvpCheckProbe.lean"
            probe.write_text(probe_source, encoding="utf-8")
            if args.keep_probe:
                Path(args.keep_probe).write_text(probe_source, encoding="utf-8")
            payload, theorems = evaluate_probe(probe, lake, args)

        report = build_report(doc, payload, theorems, mvp_mod)

        negative_results: List[Dict[str, Any]] = []
        negative_ok = True
        if args.self_test:
            for label, mutated_payload, mutated_theorems in negative_mutations(payload, theorems):
                mutated_report = build_report(doc, mutated_payload, mutated_theorems, mvp_mod)
                caught = mutated_report.failures[0]["check"] if mutated_report.failures else None
                negative_results.append(
                    {"mutation": label, "detected": caught is not None, "caughtBy": caught}
                )
                if caught is None:
                    negative_ok = False
                    print(f"NEGATIVE TEST FAILED: mutation not detected: {label}",
                          file=sys.stderr)

        elapsed = time.time() - start
        if args.json:
            print(json.dumps(
                {
                    "ok": report.ok and negative_ok,
                    "checks": len(report.checks),
                    "failures": report.failures,
                    "negativeTests": negative_results,
                    "elapsedSeconds": round(elapsed, 3),
                },
                indent=2,
            ))
        else:
            summarize(report, "MVP cross-check")
            for result in negative_results:
                state = "detected" if result["detected"] else "MISSED"
                print(f"  negative test: {result['mutation']}: {state} "
                      f"({result['caughtBy']})")
            if report.ok and negative_ok:
                print(f"PASS: Lean model agrees with search/mvp.py and the fixture "
                      f"({round(elapsed, 2)}s)")
                print("  note: this is drift detection, not a proof; the Lean theorems "
                      "and the axiom audit are the authority.")
                return EXIT_OK
            print("FAIL: MVP cross-check found semantic drift", file=sys.stderr)
        return EXIT_OK if (report.ok and negative_ok) else EXIT_MISMATCH
    except CheckError as exc:
        print(f"MVP CHECK ERROR: {exc}", file=sys.stderr)
        return exc.code
    except subprocess.TimeoutExpired as exc:
        print(f"MVP CHECK ERROR: timed out after {exc.timeout}s: {' '.join(exc.cmd)}",
              file=sys.stderr)
        return EXIT_LEAN
    except OSError as exc:
        print(f"MVP CHECK ERROR: {exc}", file=sys.stderr)
        return EXIT_FIXTURE


if __name__ == "__main__":
    sys.exit(main())
