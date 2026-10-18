# MVP validation (reproducible, independent of real Civ6 rules)

Status: local verification **PASS** (2026-10-17 22:52 CST). The GitHub Actions
workflow has been added but **has not run** (no remote push was made).

## One command

```bash
scripts/verify.sh
```

Runs, in order, and stops at the first failure:

1. `lake build` — plain Lean/Std project (no Mathlib, no dependencies);
2. `python3 search/synthetic.py --self-test` — 28 Python model tests;
3. `python3 search/synthetic.py --check-fixture` — fixture semantic self-check;
4. `python3 scripts/check-synthetic.py` — actual Lean scenario vs frozen fixture
   (47 checks);
5. `python3 scripts/audit-axioms.py --no-build` — generated `#print axioms`
   probe over every theorem constant under `Civ6Verify`.

The only validation artifact is `synthetic-v0`, a deliberately fake benchmark.
Nothing here validates a Civilization VI rule or optimum.

## Toolchain resolution

`scripts/verify.sh` reads the pin from `lean-toolchain`
(`leanprover/lean4:v4.25.0`) and requires Lean **and** Lake to report `4.25.0`:

1. project-local `scripts/lean-env` (`.tools/lean-4.25.0-linux`) if it works;
2. otherwise `lean`/`lake` on `PATH` (for example elan).

It never downloads a toolchain. Forcing one source is possible with
`VERIFY_TOOLCHAIN=project|path` (used to test the fallback locally).

The local project toolchain and NixOS loader details are in
`research/TOOLCHAIN.md`; that file is intentionally not committed.

## Rigid checker wrapper and requested fix

`scripts/check-synthetic.py` hardcodes `REPO_ROOT/scripts/lean-env` and has no
override flag. It is **not edited here**. In PATH mode `verify.sh` therefore:

- writes a throwaway `lean-env` shim that runs `lake` from `PATH`;
- runs the unmodified checker through a short Python launcher that sets the
  module global `LEAN_ENV` to that shim for this process only.

Requested upstream fix (small, owned by the checker author): add
`--lean-env PATH` (default `scripts/lean-env`) and use it in the initial
existence/execute check, `ensure_olean`, and `evaluate_probe`. Once present,
`verify.sh` can drop the temporary shim/launcher.

## Axiom audit

`scripts/audit-axioms.py` (runnable standalone; it builds unless `--no-build`
is given, and falls back to `scripts/lean-env` when `lake` is not on `PATH`):

- statically rejects `sorry`/`admit`, `axiom`/`constant`,
  `native_decide`/`Lean.ofReduceBool`, `implemented_by`/`extern`, and
  `debug.skipKernelTC` in `Civ6Verify.lean` and `Civ6Verify/**/*.lean`
  (comments and strings stripped);
- discovers theorem constants with a generated Lean probe using
  `Lean.wasOriginallyTheorem`, so the list is not hardcoded;
- emits a second generated probe with one `#print axioms` line per public
  theorem;
- checks private compiler-generated match-equation lemmas (mangled names cannot
  be written in source syntax) with `Lean.collectAxioms`;
- allows **only** `propext` and `Quot.sound`. `sorryAx`, `Lean.ofReduceBool`,
  `Classical.choice`, project axioms, or any other axiom fail the command.

Current result: **268 public theorem constants** plus **19 private generated
theorem constants**; dependency histogram: none 105, `propext` 27,
`Quot.sound` 1, `propext + Quot.sound` 135. No forbidden token or axiom.

Negative check: temporarily injecting a `sorry` theorem, a custom axiom, and a
`native_decide` theorem each made the audit exit 1 (source was restored
afterwards). The passing run above is from the restored tree.

## CI

`.github/workflows/verify.yml` checks out the repo and uses
`leanprover/lean-action@v1` only to install elan; the Lean version remains pinned
by `lean-toolchain`. Build, test, lint, Mathlib cache, and Lake cache are
disabled, then `scripts/verify.sh` is the single verify step. No Mathlib is
downloaded because the project has no Mathlib dependency and no Mathlib cache is
requested.

## Blocked / not claimed

- Real Civ6 rules, scenarios, and game-rule edits are out of scope and absent;
  this infrastructure only guards the current core/synthetic development.
- The workflow is statically reviewed, not executed (no remote push).
- elan itself is not installed locally; PATH mode was exercised by putting the
  local Lean 4.25.0 `bin` directory on `PATH`, including the checker shim path.
