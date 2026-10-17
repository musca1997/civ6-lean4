# REVIEW.md — independent adversarial review (2026-10-17)

Reviewer role: independent review only. No source file outside this file was
modified. All experiments ran from `<project-root>`; scratch files
lived in `/tmp`.

This review is **pinned to snapshots**, because `Civ6Verify/Scenarios/Synthetic.lean`
was being edited continuously while the review ran (it changed at least eight
times between 21:57 and 22:07). Results below apply to these exact hashes:

| artefact | md5 | mtime |
|---|---|---|
| `Civ6Verify/Reachability/Finite.lean` | `e6f68ffa530704547d4500ed453f8840` | 21:58:48 |
| `Civ6Verify/Scenarios/Synthetic.lean` | `e50ce93bec680f8a27919bb21a699b63` | 22:07:04 |
| `search/synthetic.py` | `8ec52a2c7cc68284a632a1c6b485921e` | 21:52:12 |
| `fixtures/synthetic-v0.json` | `ce6a2fc523f93a374845ae6d3d800f61` | 21:52:12 |

Environment: Lean 4.25.0 from `.tools/lean-4.25.0-linux`, Python 3.13.12,
no Mathlib, `[V] = 0` (no Civ6 installation).

Addendum (same session, 22:08–22:09): the scenario kept moving after the pin
(`4a2e69b9` → `e50ce93b` → `fee3b2a3` → `c3f2fbfd`, and later). At `fee3b2a3`
and again at `c3f2fbfd` I rebuilt the **whole project** (`scripts/lean-env lake
build`): exit 0, 0 errors. The `#eval` results below are unchanged at both (33
sequences, 1 goal, `[1,2,4,6,7,7]`, `all`-not-goal `= true`), the axioms are
still only `propext`/`Quot.sound`, and findings S3-1 and S4-1 persist (at
`fee3b2a3` they are at lines 665 and 840; line numbers shift a few lines per
revision). This remains an in-progress file: the checks in this review are
snapshot checks, not an approval of a final artefact. Line numbers elsewhere
in this file refer to the `e50ce93b` pin.

---

## 0. Verdict

| artefact | verdict |
|---|---|
| generic core `Civ6Verify.Reachability.Finite` | **PASS** (builds, axioms clean, lower bound sound, no circularity inside the stated scope) |
| Python BMK (`search/synthetic.py` + fixture) | **PASS with findings** (22/22 tests, fixture check; one latent duplicated-constant bug, several low-severity hygiene issues) |
| Lean BMK scenario `Civ6Verify.Scenarios.Synthetic` | **PASS at the pinned hash** (builds, `OptimalAt 5` verified, frontiers match an independent recomputation); **not approved as final** — file is in-progress and moved after the pin; one headline sub-lemma is mis-stated (see S3-1) |
| `M0(θ,σ)` (the actual v0 contract model) | **ABSENT — cannot be reviewed or approved** (see S1-1) |

**No v0 acceptance claim is supported.** The only machine-checked optimality
results in the repository are for the four-state `Toy` smoke test inside the
generic core (`OptimalAt ... 3`) and for BMK-v0 (`OptimalAt model goal 5`,
a deliberately non-Civ6 benchmark, per `SCOPE.md §4.4`), not for `M0`.
`SCOPE.md` S2–S8 are unmet: there is no `Civ6Verify/Rules/`, no θ, no
envelope, no `reports/`, and no M0 `playout`/`reach`/`OptimalAt`. On the
documentation side, S1 (evidence tags in `RULES.md`), S9 (X1–X20) and S10
(fixture plan) are largely present and are not the bottleneck; the gap is
executable M0.

---

## 1. Verified commands (exact)

```bash
# 1. generic core  -> exit 0, 0 errors, only propext/Quot.sound in #print axioms
scripts/lean-env lake build Civ6Verify.Reachability.Finite

# 2. full project at the pinned hashes -> exit 0, 0 errors
scripts/lean-env lake build

# 3. scenario at the pinned hash -> exit 0, 0 errors (1.3–3 s)
scripts/lean-env lake build Civ6Verify.Scenarios.Synthetic

# 4. Python suite -> Ran 22 tests ... OK
python3 search/synthetic.py --self-test

# 5. fixture drift check -> OK
python3 search/synthetic.py --check-fixture
```

Additional independent checks (scratch files only):

```lean
-- /tmp/eval2.lean against the pinned scenario olean
#eval (actionSequences 5).length                                    -- 33
#eval ((actionSequences 5).filter (fun as => goalB (run model init as))).length
                                                                     -- 1
#eval (List.range 6).map (fun t => (distLayer t).length)
                                                                     -- [1,2,4,6,7,7]
#eval (List.range 6).map (fun t => (Frontier model t).length)
                                                                     -- [1,2,4,7,9,10]
#eval checkCertificate model goalB 5                                 -- true
#eval checkCertificate model goalB 4                                 -- false
#eval earliestGoalTick? model goalB 8                                -- some 5
#print axioms optimalAt_five      -- [propext, Quot.sound]
#print axioms reachable_goal_state -- [propext, Quot.sound] (at pin)
```

A scripted `#print axioms` over **all 42 theorems** in `Finite.lean` found **no**
`Classical.choice`, `sorryAx` or `Lean.ofReduceBool`; the only axioms are
`propext` / `Quot.sound`. The same audit over the scenario at the pin is clean
(an earlier revision had `Classical.choice` in `reachable_goal_state`,
`mem_sequencesFrom`, `unique_optimal_sequence` via `step_pop_bounds`; that was
fixed before the pin — keep the audit in CI, it did catch something real).

I also recomputed the BMK exact-step frontiers and BFS distance layers with an
independent Python replica of the *documented* round order and compared them to
Lean's `#eval` output. All 6 exact frontiers and all 6 distance layers agree,
**including element order**; the goal is unique at `t = 5`; the 33 legal
5-step sequences contain exactly one goal sequence (the fixture witness).

---

## 2. Findings (most severe first)

### S1-1 — BLOCKER: M0 is absent, so no v0 claim can be checked

`SCOPE.md §2` (S2/S3/S4/S5/S6/S8) and `RULES.md §2/§10` define the v0
deliverable as `M0(θ,σ)` with `step/legal/Goal`, `reach/NoEarlier/OptimalAt`,
θ, envelope, and an exclusion-aware certificate. None of it exists in the tree:
`Civ6Verify/Rules/` is missing, there is no `playout`, no `reach`, no `N(θ)`,
no `reports/`. The only non-toy machine-checked optimality result is
`Civ6Verify/Scenarios/Synthetic.lean` `OptimalAt model goal 5` (the core's
four-state `Toy` also proves `OptimalAt ... 3`, but it is an API smoke test,
not a scenario), which `SCOPE.md §4.4` explicitly forbids treating as `M0` or
as a game result. The
same is true for the `Finset.powerset` enumeration requirement of `SCOPE.md:44`
and `RULES.md:381`: the BMK uses `List.range`, which is fine for the BMK but
does not satisfy S3 for M0.

Consequence: the repo currently proves "the pipeline works on a toy", not "the
v0 model has an optimum". The documentation is largely honest about this
(`SCOPE.md §3`, `RULES.md §16`, the BMK header), but the acceptance checklist in
`SCOPE.md §9` must stay unchecked, and any summary must not present the BMK's
`5` as the v0 result.

### S3-1 — MEDIUM: `distLayer_no_goal_below_five` does not state its name

`Civ6Verify/Scenarios/Synthetic.lean:655-658` (pin `e50ce93b`):

```lean
/-- The BFS distance layers contain no goal state below tick 5. -/
theorem distLayer_no_goal_below_five :
    (List.range 5).all (fun t => (distLayer t).any goalB) = false := by
  decide +kernel
```

`List.all` is the conjunction of the predicate over the five layers, so this
says **"not every layer 0..4 contains a goal"** — which is true as soon as
layer 0 is goal-free and would remain true if a goal appeared at `t = 3`. It is
therefore (nearly) vacuous and does not express the docstring. Verified with
`#eval` on the pinned olean: per-layer `any goalB` is
`[false, false, false, false, false]`, the stated `all` is `false`, while
`(List.range 5).all (fun t => !((distLayer t).any goalB))` is `true`.

The real property is proven separately and correctly by `no_goal_below_five`
and `optimalAt_five`, so **no false optimality claim follows**; but this lemma
is misleading and should be restated as
`(List.range 5).all (fun t => !((distLayer t).any goalB)) = true` or
`∀ t, t < 5 → (distLayer t).any goalB = false`.

### S3-2 — MEDIUM (latent): two sources of truth for the production cap in Python

`search/synthetic.py` keeps `Rules.progress_cap` (line 135, from fixture
`settler.productionProgressCap`, line 172) and uses it in `step` (line 316:
`min(raw_prod, r.progress_cap)`), but `check_state` (lines 233–234) enforces
`prod ≤ Rules.max_progress()` where `max_progress()` is
`settler_cost - 1` (lines 149–150), ignoring `progress_cap`.

For the frozen rules both are `7`, so all current runs are consistent. But
`Rules.from_spec` accepts a spec where they differ; then `step` can produce a
state that `check_state` rejects. Reproduced:

```python
r2 = replace(r, progress_cap=9)
step(r2, (1, 0, 7, 0), (0, 1))
# -> IllegalState: production 9 outside [0,7]
```

This matters exactly when θ/envelope variants are generated by perturbing the
cap rather than the cost. Use one derived quantity (e.g. always compute the cap
as `cost-1`, or make the invariant mention `progress_cap`) and assert the two
agree in `from_spec`.

### S4-1 — LOW: the scenario docstring's "32 legal 5-step sequences" is wrong

`Civ6Verify/Scenarios/Synthetic.lean:830-832` says "Exhaustive check over the
(32) legal 5-step sequences". The true count is **33**: 15 four-step prefixes
with `pop = 1` (2 actions each) plus the single all-farm prefix with `pop = 2`
(3 actions): `15*2 + 3 = 33`. Confirmed by Lean `#eval` on the pinned olean
(`(actionSequences 5).length = 33`) and independently by Python
`brute_force_sequences(..., 5)` (33 sequences, 1 goal). The theorem itself is
correct; only the comment is wrong.

### S4-2 — LOW: `Rules.to_spec()` ignores the instance

`search/synthetic.py:177` returns the module-global `RULES_SPEC` regardless of
the `Rules` fields. It is documented, and `rules_digest` does hash the fields,
so the frozen fixture is fine. But `fixture_document()` would silently emit the
default rules for a perturbed `Rules`, which is a trap as soon as θ variants are
emitted. Either derive `to_spec` from `asdict(self)` (and keep a separate
"canonical fixture text" function) or assert `self == default_rules()`.

### S4-3 — LOW: the fixture-presence and fixture-check checks are weaker than documented

- `load_fixture()` raises `unittest.SkipTest` when the file is missing
  (`search/synthetic.py:1048`), so `--self-test` reports OK (one skip) with no
  frozen fixture at all. A missing fixture should be a failure in a release
  check.
- `SYNTHETIC.md:65` says `--check-fixture` verifies "逐字节一致"; it actually
  compares a fixed list of parsed top-level keys (`fixture_mismatches`, lines
  702–716) and ignores `fixtureId`, `version`, `timeModel`, `purpose`,
  `disclaimer`, etc. Tampering with those keys is not detected. Either say
  "selected fields" or compare canonical bytes.
- `test_fixture_checker_detects_tampering` is good (it tampers with `expected`
  and `rules`), but the above two gaps remain.

### S4-4 — LOW: dangling reference and stale ownership notes

- `Civ6Verify/Scenarios/Synthetic.lean:8` points to
  `research/SYNTHETIC-LEAN.md`, which does not exist (only `ENVIRONMENT.md`,
  `REACHABILITY.md`, `RULES-RESEARCH.md`, `SYNTHETIC.md`, `TOOLCHAIN.md` are in
  `research/`).
- `research/SYNTHETIC.md:461` ("不建立 Lean 定理（本轮没有 Lean 文件权限）") is
  stale: the scenario module now exists and proves `OptimalAt` for the BMK
  (owned by a different task). Cross-owner bookkeeping needs updating.
- `research/REACHABILITY.md:61` ("根模块没有 import 本文件 …… 单独跑 lake build
  不会检查本文件") and line 4 ("未修改根模块") are stale: `Civ6Verify.lean:21`
  now imports `Civ6Verify.Reachability.Finite`, and plain `lake build` checks
  every module (8 jobs, verified). This is a doc fix only; the build behaviour
  is actually better than documented.

### S4-5 — LOW/INFO: no automated Lean↔fixture cross-check

The Lean scenario re-declares the constants and the frontier literals by hand.
At the pin they agree with the fixture/Python (I checked independently), but
nothing in the tree parses `fixtures/synthetic-v0.json`, hashes it, or compares
it to Lean output. A future fixture edit will not invalidate the Lean module.
Recommended: generate the constant block + expected layer data from the fixture
(or add a `#eval`-based checker with a hard-coded digest) so drift is a build
failure, not a review exercise.

### S4-6 — LOW/INFO: `decide +kernel` is the fragile part

While the file was being edited, intermediate revisions failed to build with
`Tactic split failed` (`step_done_ge`/`step_done_le_succ` when `unfold step`
left `have` bindings), `rewrite` failures in `foodPhase_one`, and deterministic
heartbeat timeouts at 200 000 — and still at 2 000 000 — for the frontier
`decide` proofs. The pinned revision builds in ~1–3 s with `decide +kernel`,
and `#print axioms` confirms it adds no `Lean.ofReduceBool`. This is not a
defect at the pin, but the numeric proofs are brittle against changes to
`step`'s shape; keep them (and the audit) in CI.

### S4-7 — INFO: core will not scale to M0 as-is

`Frontier` is exact-step with per-level `flatMap` + quadratic `dedup`, and
`checkNoGoalBelow`/`earliestGoalTick?` recompute frontiers from scratch for
each tick. Ten states are trivial; `RULES.md §10.4` expects 10^3–10^5 states
per layer and itself suggests a certificate importer for Python-produced
layers. The core has no such importer. Correctness is fine; plan the importer
before M0, and do not reach for `native_decide` without the disclosure required
by `RULES.md §10.4/§10.5`.

---

## 3. Answers to the specific review questions

### 3.1 Does the lower bound quantify all declared legal actions?

**Yes.** `NoEarlier` (`Finite.lean:272`) is

```lean
∀ t, t < N → ∀ s, Reachable M t s → ¬ goal s
```

and `Reachable` (`Finite.lean:64`) is built from `M.legal`, **not** from
`legalActions`. `noEarlier_iff_all_legalPaths` (`Finite.lean:337`) proves it is
equivalent to "every legal action sequence of length `< N` fails", using
`reachableFrom_exists_legalPath` / `legalPath_run_reachableFrom`. The
frontier-based checker is tied back to `legal` by `mem_frontier_iff`
(`Finite.lean:228`), whose backward direction consumes
`legalActions_complete`. So dropping a legal action from the enumeration makes
the completeness field (a theorem field, not an axiom) unprovable; it does not
silently weaken the bound. This is exactly the right design.

The one thing the core **cannot** check is whether a scenario's `legal`
predicate matches the declared game rules. For BMK, `legal` is independent
arithmetic (`done = 0 ∧ farm + mine = pop`) and both enumeration directions are
proven (`legalActions_sound`, `legalActions_complete`, `mem_legalActions_iff`).
For M0, that predicate does not exist yet. This is the explicit scope boundary
in `SCOPE.md §4.3`, not a hole in the core.

### 3.2 Soundness/completeness: circular beyond explicit scope?

No circularity in the core or the BMK:

- `legal`, `legalActions`, `_sound`, `_complete` are separate class fields;
  `Frontier` uses the enumeration, but `mem_frontier_iff` links it to the
  independent predicate. `goalB`/`goal` are bridged only by the explicit
  `hspec` hypothesis of the certificate theorems.
- BMK's `legal` is not defined as list membership; `mem_legalActions_iff`
  proves the equivalence in both directions.
- The scenario's `sequencesFrom` completeness uses `legalActions_complete` and
  its soundness uses `legalActions_sound`; `mem_sequencesFrom` is proven by
  induction, so `unique_optimal_sequence` really quantifies all legal 5-step
  sequences.

Two honest qualifications:

1. Python's `_validate_action` checks membership in `legal_actions` itself, so
   Python's notion of legality is not independent of the enumeration (the
   arithmetic checks around it are). This is normal for a search prototype.
2. `search/synthetic.py §3` is titled "Independent oracle", but
   `brute_force_sequences` reuses the same `step` and `legal_actions`. It is
   independent of the BFS **dedupe/layer bookkeeping**, not of the transition
   semantics. `SYNTHETIC.md §9.2` says this; the heading overstates it slightly.

### 3.3 Exact-step vs shortest-distance

Correctly handled. `Frontier M t` is exactly-`t` reachability; `NoEarlier`
checks every `t < N`, so the certificate is "first exact tick", not a distance
claim. The two notions are distinguished in `REACHABILITY.md §5`, and the BMK
now formalizes both: exact-step counts `[1,2,4,7,9,10]` vs distance-layer counts
`[1,2,4,6,7,7]`, `distLayer_subset_frontier`, and
`exact_step_not_distance` (`(1,0,4,0)` is exactly-3 reachable but distance 2).
I reproduced both layer families independently. The only blemish is S3-1: the
goal-freeness of the distance layers below 5 is not the statement that
`distLayer_no_goal_below_five` makes (the exact-frontier version is correct).

### 3.4 State/history invariants

Present and proven for the BMK: `step_done_ge` (monotone completion counter),
`reachable_done_le_one`, `legal_not_goal` (goal states are terminal),
`reachable_pop_bounds`, `reachable_goal_state` (every reachable goal state is
`(1,0,0,1)`), plus `frontier_invariants_upto_five` for food/production within
the used horizon. `completion_state_only_from_five` restates the lower bound as
a property of the unique completion state. This is adequate for the BMK
theorem. It is **not** a general invariant story for M0 (food/production bounds
and the growth/amenity composition are unimplemented).

### 3.5 Python/Lean transition drift

At the pin, **no drift was found**: I independently reproduced the documented
round order in Python and compared every exact-step frontier (contents and
order), both layer-size sequences, the witness trace, the 33 legal 5-step
sequences, and the unique goal sequence to Lean `#eval`. All agree. The
risk is procedural, not present: the comparison is not automated (S4-5), so the
next fixture/Lean edit can diverge silently. The `step` functions are
line-for-line equivalent on legal actions (pre-growth yields, `Nat`-truncated
food floor, fuel-bounded growth with cap at `popMax`, prerequisite gate,
completion reset); illegal-action behaviour differs (Python raises, Lean is
total), which is harmless because all theorems quantify over `legal`.

### 3.6 Potential false game claims

I found **no** claim of a real-game optimum in the reviewed docs. `[V] = 0` is
stated in `SCOPE.md`, `RULES.md §1`, and the BMK docs; the BMK is labelled
"NOT Civilization VI" in the Lean header, the fixture (`synthetic: true`,
`civ6Model: false`), and `SYNTHETIC.md`. `SCOPE.md §3` and `§8` forbid the
dangerous phrasings and no `reports/` exist that could violate them. Unverified
game numbers in `RULES.md` (80/110, A=2/1, threshold 15, amenity modifiers) are
tagged `[D*]/[U]` and are not presented as measured. The residual risks are
(i) a reader conflating BMK `OptimalAt 5` with the v0 result (the docs warn,
but the repo currently has no M0 result to compare against), and (ii) the
`RULES.md §16` sentence that BMK can be "近似表示" by θ values, which is
immediately qualified but is the kind of sentence that gets quoted out of
context. Keep the BMK numbers out of any M0/civ6 report; use the mandatory
sentence from `SCOPE.md §3` verbatim when reports start.

---

## 4. Assumptions and limits of this review

- No Civ6 installation, no build hash, no `[V]` observations: I cannot assess
  model-to-game fidelity at all. This review is about executables and claims,
  not about whether the constants are the real game's.
- The BMK/Lean comparison is semantic (documented order re-implemented in
  Python), not a proof that the two implementations are extensionally equal.
  It covers the reachable states/sequences within the pinned horizon.
- The scenario file was in progress during the review. Intermediate revisions
  `b9fa3325`, `c99fd450` and `655059a9` failed to build (tactic/heartbeat
  errors); `b5fa19f3`/`4a2e69b9` had `Classical.choice` in three audited
  theorems; the pinned `e50ce93b` (and the later `fee3b2a3`/`c3f2fbfd`)
  builds and audits clean. Re-run the audit after any further edit — this file
  is not a substitute for CI.
- I did not modify any source file; `research/REVIEW.md` is the only write.
- `#print axioms` results were produced from the olean built at the pinned
  hash, not from a later dirty tree.

---

## 5. Recommended order of work

1. **Do not ship v0 claims.** Finish `Civ6Verify/Rules/` (M0), the θ/hash
   plumbing, `reach`/`NoEarlier` for M0, and the envelope; keep BMK clearly
   separated (`SCOPE.md §4.4`).
2. Fix S3-1 (`distLayer_no_goal_below_five` statement) and S3-2 (single
   production-cap source of truth) before adding θ variants.
3. Automate the Lean↔fixture check (S4-5) and make a missing/stale fixture a
   hard failure (S4-3).
4. Fix the S4-1 count, the dangling `SYNTHETIC-LEAN.md` reference, and the
   stale statements in `REACHABILITY.md`/`SYNTHETIC.md` (S4-2/4).
5. Keep `lake build` + scripted `#print axioms` in CI (it caught the
   `Classical.choice` regression during this review), and plan the frontier
   certificate importer before scaling to M0 (S4-7).
