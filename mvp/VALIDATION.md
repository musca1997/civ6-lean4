# VALIDATION.md — MVP executable verification

> **Status: integration/drift verification of a conditional model.**
> This document describes how the *conditional* MVP model `M_MVP(θ*, σ)` of
> `mvp/RULE-CONTRACT.md` v2.1 is checked end to end. It is not a Civilization VI
> claim, not a new proof, and not a certificate about the real game. The
> kernel-checked Lean theorems remain the authority; the Python executable and
> `fixtures/mvp-baseline.json` are untrusted candidates.
>
> Owned here: `scripts/check-mvp.py`, `scripts/verify.sh`, `mvp/VALIDATION.md`.
> No model file, Python model, fixture, root module, or other document was
> changed to make this pass.

---

## 1. What is verified

`scripts/verify.sh` is the single entry point. It runs:

| # | step | command | measured here |
|---|---|---|---|
| 1 | Lean build (core + root) | `lake build` | ~0 s incremental |
| 2 | MVP lower bound built explicitly | `lake build Civ6Verify.Bounds.MvpOptimality` | ~0 s incremental |
| 3 | synthetic Python tests | `search/synthetic.py --self-test` | <1 s |
| 4 | synthetic fixture self-check | `search/synthetic.py --check-fixture` | <1 s |
| 5 | synthetic Lean-vs-fixture | `scripts/check-synthetic.py` | <1 s (temporary `lean-env` shim in PATH mode) |
| 6 | MVP Python tests | `search/mvp.py --self-test` | **24 s** (28 tests) |
| 7 | MVP fixture replay | `search/mvp.py --check-fixture` | **2 s** |
| 8 | **MVP Lean-vs-Python/fixture cross-check** | `scripts/check-mvp.py --no-build --self-test` | **~1 s** (2239 checks + 7 negative tests) |
| 9 | axiom audit (all `Civ6Verify` theorems) | `scripts/audit-axioms.py --no-build` | **7 s** |

Measured wall clock for a full `scripts/verify.sh` on the project machine
(NixOS 25.11, Ryzen 7 8700G, Lean 4.25.0): **34 s**, in both toolchain modes
(project-local `.tools` and a PATH toolchain via `VERIFY_TOOLCHAIN=path`).
The `--all` 128-θ search is **not** run by verification; the frozen fixture
records that its one-off generation took 242 s, of which 212 s was `--all`.

Step 2 is deliberately explicit even though `Civ6Verify.lean` (owned
elsewhere) may also import `Civ6Verify.Bounds.MvpOptimality`: the build step
must work in both wiring layouts, and `check-mvp.py`'s `#check` probe imports
that module.

---

## 2. The MVP cross-check (`scripts/check-mvp.py`)

The script reads every expectation from `fixtures/mvp-baseline.json` or computes
it with `search/mvp.py`; no expected number is retyped in the script. It writes
a temporary Lean probe (outside the repository) importing
`Civ6Verify.Model.Mvp` and `Civ6Verify.Bounds.MvpOptimality`, evaluates it with
`lake env lean`, and compares the JSON payload against the fixture and Python.

### 2.1 Anchors and rule constants

* `init` and `(model baselineParams).init` / `(model cost110Params).init` vs
  `scenario.initialState = [1,0,0,0]` (baseline **and** cost-110 initial state).
* Lean `tileFood`/`tileProd`/`baseFood`/`baseProd`/`threshold 1..4` vs the
  fixture `scenario` (including `T3` exact `3383` and `T4 = 4420`).
* `witness.length = 20` and `witness110.length = 25` vs `baseline.n` /
  `cost110.n`.
* `contractStyleWitness.finalState = [1,1430,190,1]` vs the Lean evaluation of
  `run (model baselineParams) init witness`.
* `goalState` vs the final row of each frozen witness (fixture self-consistency).

### 2.2 Per-step transitions

Both frozen witnesses (`baseline.witness` 20 rows, `cost110.witness` 25 rows)
are replayed through Lean. For every row the script compares `t`, pre-state,
action, `F`, `P`, `d`, `e`, `grew`, `q`, `credited`, `completed`, `extraProd`,
and post-state:

* Lean-vs-fixture (the model against the frozen candidate), and
* Python-vs-fixture (the executable against the same row).

The contract-style witness (`GH ×7 IDLE`, then `GH+PH SETTLER`; 20 rows
baseline, 25 rows cost-110) has no per-row fixture copy, so it is compared
**Lean-vs-Python** field by field, including the extra `prod_used` value, and
its final states are pinned to the fixture (`[1,1430,190,1]` for baseline).
`contractStyleWitness.pop1QComputed = 420` is checked against the Lean growth
step, which is the v2.1 `extraGain(⊥) = 0` reading.

### 2.3 Finite legal actions and step outputs

For **31 distinct reachable/sample states** (11 at pop 1, 19 at pop 2, 1 at
pop 3, including the growth step, the completion step, post-growth state and
the goal states) the script compares the **full sorted legal action-id set**:

* Lean `legalActionsFor` over all 160 candidate actions vs Python `legal` over
  the same 160-candidate box, for baseline and cost-110 θ;
* Lean baseline vs Lean cost-110 (the guard is cost-independent);
* duplicate-freedom and the 160-action box bound.

Observed set sizes: pop 1 → **5**, pop 2 → **34**, pop 3 → **16** (the pop-3
count drops because the starvation guard `600 ≤ baseFood` is active).

The case table adds targeted step outputs and legality components
(`capacity`, `extraOk`, `settlerOk`, `idleOk`, `starveOk`, `guard`):

| case | expected |
|---|---|
| `invalid_settler_at_pop1` | illegal (SETTLER needs pre-turn pop ≥ 2) |
| `invalid_capacity_exceeded` | illegal (2 worked citizens at pop 1) |
| `invalid_extra_already_worked` | illegal (extra tile already in the mask) |
| `invalid_idle_with_extra` | illegal (`IDLE ⇒ extra = none`) |
| `invalid_starving_work_set` | illegal (`200·pop ≤ F` fails) |
| `growth_with_extra` | legal; grows 2→3, `extraProd = 100`, `q = 735` |
| `growth_idle_no_extra` | legal; the contract-style growth step, `q = 420` |
| `completion_step` | legal; completes, post `[1,0,190,1]` |

### 2.4 Theorem availability (`#check`) — availability only

The probe contains `#check` for:

```
Civ6Verify.Bounds.MvpOptimality.optimalAt_baseline   -- OptimalAt ... goal 20
Civ6Verify.Bounds.MvpOptimality.optimalAt_cost110    -- OptimalAt ... goal 25
Civ6Verify.Bounds.MvpOptimality.noEarlier_20
Civ6Verify.Bounds.MvpOptimality.noEarlier_25
Civ6Verify.Model.Mvp.witness_run                      -- final (1, 1430, 190, 1)
Civ6Verify.Model.Mvp.witness110_run                   -- final (1, 1980, 340, 1)
```

The script asserts the printed type contains the expected `OptimalAt`/`NoEarlier`
shape and the expected witness constants. This only shows that the constant
exists with that type and was successfully built. **Numeric `#eval` agreement is
not a proof substitute**: `#eval` runs compiled code, while the lower bound is
established by the kernel-checked proof in `Civ6Verify/Bounds/MvpOptimality.lean`
and the trust boundary is confirmed by the axiom audit in step 9.

### 2.5 Negative mismatch detection (`--self-test`)

`--self-test` reuses the real Lean payload, mutates it in memory (never the
repository), and requires every mutation to be caught:

1. a trace `q` off by one;
2. a changed initial state;
3. a dropped legal action;
4. a changed contract-witness final state;
5. an invalid case marked legal;
6. a changed `T3` exact threshold;
7. a missing `#check` theorem.

All seven are detected, so "everything matches" cannot be produced by a broken
comparator.

---

## 3. Toolchain selection

`check-mvp.py` follows the same selection rules as `scripts/verify.sh`:

* `--lean-env PATH` forces a wrapper (for example `scripts/lean-env`, or the
  temporary shim `verify.sh` creates for the rigid synthetic checker);
* otherwise `--lake PATH` / `lake` on `PATH` is used, and the project-local
  `scripts/lean-env` is only a fallback (never the sole hardcoded path).
  `verify.sh` prepends the resolved toolchain `bin` directory to `PATH`, so the
  same command works in both `VERIFY_TOOLCHAIN=project` and
  `VERIFY_TOOLCHAIN=path` modes; both were exercised.
* `LEAN_PATH` / `LEAN_SRC_PATH` are unset for every subprocess, so a stale
  ambient search path cannot leak into the probe.
* The probe's imports are built on demand (unless `--no-build`) when the
  `MvpOptimality.olean` is missing or older than the model/arithmetic/core
  sources. `verify.sh` builds the module explicitly and then uses
  `--no-build`.

Exit codes: `0` pass, `1` semantic mismatch, `2` fixture/setup problem, `3`
toolchain unavailable, `4` Lean build/probe failure.

---

## 4. Trust boundary and limitations

* **Conditional model.** Everything verified here is about `M_MVP(θ*, σ)` in
  `mvp/RULE-CONTRACT.md` v2.1 under A1–A8. There is no claim that Civilization VI
  implements these rules, no build id, and no `[V]` claim.
* **No `sorry` / `native_decide` / custom axioms.** `scripts/audit-axioms.py`
  audits every `Civ6Verify` theorem constant discovered by Lean and reports
  **686 public theorem constants** (`#print axioms`) plus **21 private
  generated theorem constants** (`collectAxioms`), with only `propext` and
  `Quot.sound` approved. This includes the MVP model and lower bound after the
  parent's `step_trained` Or-branch fix (which removed a `Classical.choice`
  dependency).
* **Sample, not exhaustive search.** The cross-check replays the frozen
  witnesses and a 31-state sample; it does not re-run a BFS or the 128-θ search.
  The optimality claim comes from `optimalAt_baseline` / `optimalAt_cost110`,
  not from this script.
* **`#check` is not a proof.** See §2.4. A successful probe would still be
  consistent with a broken proof if `lake build` were skipped; the build step
  (and the axiom audit) are what make the theorems trustworthy.
* **Horizon.** The executable horizon is H = 27; the contract's H = 34
  guard/sensitivity envelope is outside this validation (limitation
  `L-HORIZON` in the fixture). Baseline/cost-110 optima are 20/25, below 27.
* **Witness shape.** `M_MVP` fixes the other θ axes at the baseline values;
  `Params` parameterises only `cost` (80 vs 110). The cost-110 witness uses the
  same `GH ×7` prefix and 18 SETTLER steps.

---

## 5. Reproduction

```bash
# everything (build + synthetic + MVP + audit)
scripts/verify.sh

# only the MVP cross-check (builds MvpOptimality on demand)
python3 scripts/check-mvp.py --self-test

# explicit wrapper / existing olean
python3 scripts/check-mvp.py --lean-env scripts/lean-env
python3 scripts/check-mvp.py --no-build --json

# inspect the generated probe
python3 scripts/check-mvp.py --keep-probe /tmp/mvp-probe.lean
```

`--self-test` is the routine invocation used by `verify.sh`; it takes about one
second because the fixture (242 s to generate once) is frozen and no `--all`
search is performed.
