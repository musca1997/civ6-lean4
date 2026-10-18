# POLICY.md — Urban Planning policy variant: a conditional-model breakthrough

Owner: policy-breakthrough task. Machine-readable twin: `fixtures/policy-breakthrough.json`.
Lean module: `Civ6Verify/Scenarios/UrbanPlanning.lean`. Executable: `search/policy.py`.
Baseline model (unmodified): `Civ6Verify/Model/Mvp.lean`, `Civ6Verify/Bounds/MvpOptimality.lean`, `mvp/RULE-CONTRACT.md` v2.1.

> **Claim discipline.** Every number below lives inside a *conditional model*.
> The baseline is `M_MVP(θ*, σ)` of `mvp/RULE-CONTRACT.md` v2.1. The variant is
> `M_MVP` plus **one** explicit assumption: Urban Planning contributes +1 base
> city production. This is **not** a Civilization VI fact: `[V] = 0`, no build is
> pinned, no in-game fixture was run, and no full-game comparison is made.

## 1. The one new assumption

```
[POLICY-ASSUME]  Urban Planning is in effect from t = 0 and adds +1 base city
                 production (+100 in the model's 1/100 units):
                     baseProd = 300 + workProd   ->   400 + workProd
                 applied BEFORE the Happy production multiplier:
                     q = (400 + workProd + growthExtra) * prodMult(popAfter) / 100
```

The unlock cost, the civics/culture tree, the policy-slot opportunity cost and
every other policy are **not modelled**. The variant does not claim the policy is
free; it is an explicit conditional assumption, exactly like the inherited
`M_MVP` assumptions.

## 2. Semantic inheritance (no hidden change)

The variant is implemented as a one-parameter family `bonusStep bonus` that
differs from `Mvp.step` only in the additive production term. Everything else is
the *same code path*:

- legality: `legalGuard` is reused verbatim — pre-turn `pop ≥ 2` for SETTLER
  (A8), `workCount ≤ pop`, `extra` unworked, `IDLE ⇒ extra = none`, and the
  starvation guard `200·pop ≤ baseFood`;
- growth: `surplus`, `growthAmount`, `wouldGrow`, `popAfter`, `foodAfter`,
  thresholds and amenity/multiplier tiers are reused verbatim;
- credit/banking: `credit` credits only SETTLER and never IDLE;
- `trained` stays monotone (the goal is terminal).

Kernel-checked cross-checks:

| theorem | meaning |
|---|---|
| `bonusStep_zero` | `bonusStep 0 p s a = step p s a`: with no bonus the family *is* the baseline |
| `policyModel_legal_iff_guard` | the variant's legality is literally `legalGuard` |
| `policy_mem_legalActions` | variant enumeration is sound **and** complete |
| `policy_enumerates_same_actions` | variant and baseline accept exactly the same actions |
| `policy_settler_impossible_at_pop1` | the policy does not legalise a pre-turn Settler |
| `bonusStep_idle_prog`, `bonusStep_idle_trained` | IDLE accrues no progress (no banking) |
| `policy_growth_amount` | the pop-1 growth step still generates `e = 220` |
| `policy_legalActions_eq_baseline` (membership form above) | no free unlock, no new legal actions |

The Python executable re-derives the same facts independently
(`--self-test`, `--check-fixture`):

- `bonusZeroReproducesBaseline`: bonus 0 reproduces the baseline N and all 690
  sampled transitions;
- `growthUnchanged`: 482 sampled transitions agree on `F`, `d`, `e`, `grew`;
- `productionDelta`: the only observed `q` delta is `105 = 100 · 105 / 100`, and
  every `q_raw` is divisible by 100 (exactness preserved);
- `banking`: 51491 legal IDLE steps, zero progress/trained changes;
- `illegalActions`: pre-turn SETTLER, IDLE-with-extra, extra-already-worked and
  starving work sets are all rejected.

## 3. Result: strict breakthrough in the model

Witness (identical shape for both costs): `GH × 7 IDLE`, then `(GH+PH) × k SETTLER`.
The seven growth steps are forced by `T(1) = 1500` (max `e = 220`); the policy
settler step credits `q = 700 · 105 / 100 = 735` (baseline: `630`).

| cost | baseline N (no policy) | policy N | witness final state |
|---|---|---|---|
| 80 | 20 (`noEarlier_20`) | **18** | `pop 1, food 1210, prog 85, trained 1` |
| 110 | 25 (`noEarlier_25`) | **22** | `pop 1, food 1650, prog 25, trained 1` |

Kernel-checked Lean theorems:

```lean
theorem urbanPlanning_breakthrough :
    ¬ AchievableAt (model baselineParams) goal 18 ∧
      AchievableAt (policyModel baselineParams) goal 18
theorem urbanPlanning_breakthrough_cost110 :
    ¬ AchievableAt (model cost110Params) goal 22 ∧
      AchievableAt (policyModel cost110Params) goal 22
```

The negative half is **not re-proved**: it is the existing baseline lower bound
`MvpOptimality.noEarlier_20` / `noEarlier_25` restricted to `18 < 20` / `22 < 25`.
The positive half is a legal 18-/22-step witness replayed through the variant
model (`policyWitness_legal`, `policyWitness_run`). This is a *strict* model
comparison: the baseline cannot do it, the variant can.

**Not claimed:** that `18`/`22` is *optimal* for the variant. The Lean
development proves achievability only, paired with the baseline lower bound; a
variant optimality theorem would need a new lower bound and is deliberately out
of scope for this milestone.

## 4. Conditional assumptions (all inherited + one new)

Inherited verbatim from `M_MVP` v2.1: A1 (palace +2 P), A2/A8 (pre-turn settler
selection at `pop ≥ 2`), `turnOrder = growth_first`, `newCitizen = best`,
`amenityStock = 2` (Happy 110 % growth / 105 % non-food for `pop ≤ 4`),
`basketOnGrowth = zero`, `productionRounding = exact`, `thresholdRounding = exact`
(`T(3) = 3383`), `extraGain(none) = 0`, extra never feeds food, starvation
illegal, no progress on IDLE or before `pop 2`, housing inert (`×1.00`), `pop ≤ 3`
on the proved paths, and all of the exclusion set X1–X20 of `SCOPE.md §4.2`.

New: `[POLICY-ASSUME]` above. `[V] = 0` for every number in this document.

## 5. Verification status

| check | command | status |
|---|---|---|
| Lean builds | `scripts/lean-env lake build Civ6Verify.Scenarios.UrbanPlanning` | PASS |
| axiom footprint | `#print axioms` (see module §8) | only `propext`, `Quot.sound` |
| no forbidden tokens | static scan of the module | none (`sorry`/`axiom`/`native_decide`/…) |
| Python tests | `python3 search/policy.py --self-test` | 12/12 PASS |
| fixture replay | `python3 search/policy.py --check-fixture` | PASS |
| Lean ↔ Python | `python3 search/policy.py --lean-probe` | `#eval` final state matches fixture |
| baseline untouched | `git status` | no model/bridge/arithmetic/root/search file edited |

The repository-wide `scripts/audit-axioms.py` cannot run while an unrelated
concurrent module (`Civ6Verify/Robustness/Candidates.lean`, not owned here) is
not yet built; the module's own `#print axioms` output was checked directly and
is clean. This document does not weaken any threshold of `SCOPE.md §8`: no
upgrade from "conditional model theorem" to "Civ6 assertion" is made.

## 6. Reproduce

```sh
scripts/lean-env lake build Civ6Verify.Scenarios.UrbanPlanning
python3 search/policy.py --self-test
python3 search/policy.py --write-fixture   # refreshes fixtures/policy-breakthrough.json
python3 search/policy.py --check-fixture
python3 search/policy.py --lean-probe
```
