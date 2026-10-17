# SCENARIO-REVIEW-NOTES.md — actionable follow-up on the BMK scenario

Scenario-review task only: **no file outside this one was modified**; experiments
ran read-only from `<project-root>`, scratch files in `/tmp`. The
scenario moved twice while I worked, so everything below is pinned (the generic
core `Finite.lean` is unchanged since `REVIEW.md`, `e6f68ffa…`, audit stands):

| artefact | md5 | verdict at this hash |
|---|---|---|
| `Civ6Verify/Scenarios/Synthetic.lean` | `9510cf77bff2376ff234ea5c93adcdba` | builds clean, 84/84 theorems axiom-clean |
| `search/synthetic.py` | `daf41059d1b7d970bc0a1343ad92ce54` | 28/28 tests OK, `--check-fixture` OK |
| `fixtures/synthetic-v0.json` | `d70c4dc0777f44bc32dcc38633874ab1` | agrees with Lean on every number checked |

**Scope honesty.** This is the *synthetic benchmark* (`synthetic: true`,
`civ6Model: false`): `OptimalAt model goal 5` is a proof-engineering fact about
invented rules, not a Civ6 fact and not the v0 result. `M0(θ,σ)`, the real-rules
model, is **absent** (no `Civ6Verify/Rules/`), so no v0 acceptance claim is
possible (`REVIEW.md §S1-1`).

## 1. The two review items are closed (verified, not just landed)

Both were open at `c3f2fbfd` (the `REVIEW.md` pin), fixed at `9510cf77`; I
re-elaborated the landed text verbatim in `/tmp/check_fixes.lean`.

**S3-1 — fixed and now states its name** (`Synthetic.lean:672-680`):

```lean
theorem distLayer_no_goal_below_five :
    (List.range 5).all (fun t => !((distLayer t).any goalB)) = true := by decide +kernel
theorem distLayer_no_goal_below_five' (t : Nat) (ht : t < 5) :
    (distLayer t).any goalB = false := by
  have h := (List.all_eq_true.mp distLayer_no_goal_below_five) t (List.mem_range.mpr ht)
  exact (not_eq_true_iff_eq_false _).mp h
```

plus `distLayer_goal_flags : (List.range 6).map (fun t => (distLayer t).any goalB)
= [false,false,false,false,false,true]` (`F,F,F,F,F,T`). The old weak
`all … = false` evaluates to `false` while the new negated `all` is `true`; both
audit clean, and the weak version was used by no proof. **Nothing left to do.**

**S4-1 — fixed, count = 33 confirmed three ways.** New
`legalSequences_five_count : (actionSequences 5).length = 33` (`decide +kernel`)
and a docstring with the `15*2+3` decomposition. Independently: Lean `#eval` of
`(actionSequences 4).map pop` = 15×`pop=1` + 1×`pop=2`; Python
`brute_force_sequences(...,5)` = 33 and a hand recursion = 33.

## 2. Remaining actionable items

**A. The axiom audit covers 31 of 84 theorems — automate it.** The hand list is
what let the bad S3-1 statement survive. Unaudited (selection):
`frontier_{zero..five}_eq`, `distLayer_{zero..five}_eq` (the fixture-content
claims), `frontier_invariants_upto_five`, `distLayer_five_goal`,
`earliestGoalTick_five`, `no_goal_below_five`, `mem_actionSequences`,
`achievable_at_five`, `{cartesian,completionReachable}*Bound`, `witnessAt_five`,
`step_goal_shape`, `foodPhase_*`, `semantics_*`. Generated full audit
(`/tmp/audit_all.lean`): **84 theorems — 70 `[propext, Quot.sound]`, 14
axiom-free, 0 `sorryAx`/`Classical.choice`/`Lean.ofReduceBool`** (no defect now,
only missing coverage). Gate to commit as `scripts/audit-axioms.py`:

```python
names = re.findall(r'^theorem\s+(\w+)', re.sub(r'/-.*?-/', '', src, flags=re.S), re.M)  # one #print each
bad = [l for l in out.splitlines() if re.search(r'sorryAx|Classical\.choice|Lean\.ofReduceBool', l)]
sys.exit("AUDIT FAIL\n" + "\n".join(bad) if bad or not names else 0)
```

**B. Lean still has two independent literals for one quantity.** `settleCost := 8`
and `progressCap := 7` are unrelated constants; only a docstring says
`cap = cost-1`. Python now derives the cap and rejects a disagreeing spec (S3-2
fix), so Lean is the last two-sources-of-truth spot. Verified, axiom-free:

```lean
theorem progressCap_eq_cost_sub_one : progressCap = settleCost - 1 := by decide +kernel
```

**C. Distance-layer goal-freeness at state level (recommended, 1 line).** The
docstrings speak about *states*, the theorem about layers. Verified:

```lean
theorem distLayer_no_goal_below_five_states (t : Nat) (ht : t < 5) {s : State}
    (hs : s ∈ distLayer t) : goalB s = false    -- List.any_eq_false + simpa
```

(or free via `no_goal_below_five t ht s (distLayer_subset_frontier t s hs)`).

**D. `distLayer`'s docstring semantics is unproven (real, small gap).** The
docstring claims "states whose *earliest* reachable tick is exactly `t`" (and
`distLayer_five_eq`'s prose rests on it); proved is only
`distLayer_subset_frontier` plus counts. Computationally it holds: no member of
`distLayer t`, `t ≤ 5`, occurs in any `Frontier u`, `u < t`. Horizon form
(verified, `decide +kernel`):

```lean
theorem distLayer_minimal_upto_five :
    (List.range 6).all (fun t => (distLayer t).all (fun s =>
      (List.range t).all (fun u => !(Frontier model u).contains s))) = true
```

The general `s ∈ distLayer t → u < t → s ∉ Frontier model u` needs an induction
("every `Frontier u` member lies in some `distLayer k`, `k ≤ u`"; `distAux`'s
`seen`), ~60–100 lines; otherwise soften the docstrings to "t-step reachable and
absent from all lower layers (kernel-checked to `t=5`)". The lower bound does not
depend on this: it comes from exact-step `no_goal_below_five`/`checkCertificate`,
and layer goal-freeness below 5 already follows from item C.

**E. Lean↔fixture drift is not automated (S4-5).** Constants and layer literals
are re-declared by hand; the fixture changed twice today (`ce6a2fc5` → `d70c4dc0`)
and nothing notices. I wrote a read-only checker (`/tmp/lean_fixture_check.py`:
parses the Lean source, compares with the fixture, non-zero exit on mismatch):
**OK** on 12 layer contents, 12 layer sizes, both count lists, `witness`,
`witnessStates`, `distinctStatesTotal`, `expandedTransitions`, both scale bounds,
`legalSequences_five_count = 33`, `optimalSequenceCount = 1`. Commit as
`scripts/check-lean-fixture.py`, run with `--check-fixture` in CI (drift check,
not a source generator).

**F. `distinctStatesTotal` matches the fixture by a different definition.** Lean:
`dedup (flatMap Frontier 0..5) = 27`, fixture/Python: `sum(layer_counts)` — equal
because layers partition the reachable set, but no theorem links the forms.
Optional, verified: `(List.range 6).foldl (fun acc t => acc + (distLayer t).length)
0 = 27`.

**G. `pop = 0` is outside the common domain (informational).** `growthLoop`'s
unrolling equals Python's `while` for `pop ∈ {1,2}` (the reachable set per
`reachable_pop_bounds`); at `pop=0` Lean returns `(0,·)` where Python's loop would
grow to `1`, but Python's `check_state` rejects `pop=0` (`IllegalState`) — Lean is
just total where Python raises. Optional docstring sentence on `growthLoop`.

**H. Deferred / not defects.** `decide +kernel` on numeric literals is the fragile
part (it broke on intermediate revisions of this file) — keep it plus the audit.
The core will not scale to M0 (`flatMap` + quadratic `dedup`, frontiers recomputed
per tick): plan the Python-layer certificate importer before `Civ6Verify/Rules/`
(S4-7); no `native_decide` without the `RULES.md §10.4/§10.5` disclosure. S4-4
doc issues are gone (`SYNTHETIC-LEAN.md` exists, `Civ6Verify.lean:21` imports the
core, so `lake build` checks it).

## 3. Reproduce (read-only, ~3 s; re-run — both files were then still being edited)

```bash
scripts/lean-env lake build                                # exit 0, 0 errors/warnings
scripts/lean-env lake env lean /tmp/audit_all.lean         # 84 theorems, all clean
scripts/lean-env lake env lean /tmp/check_fixes.lean       # landed S3-1/S4-1 text + C
scripts/lean-env lake env lean /tmp/check_rec.lean         # items B, C, D
python3 /tmp/lean_fixture_check.py                         # OK (item E)
python3 search/synthetic.py --self-test && python3 search/synthetic.py --check-fixture
```

Bottom line: **S3-1 and S4-1 are closed and verified; the scenario is internally
consistent with the fixture at the pinned hashes.** Open items: (A) automate the
axiom audit, (B) tie `progressCap` to `settleCost`, (D) prove or soften the
distance-layer "earliest tick" claim. Nothing here — and no fixture number — is
a Civ6 or `M0` result.
