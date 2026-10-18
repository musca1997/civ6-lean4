# LEAN-MODEL.md — `M_MVP(θ*, σ)` v2.1 baseline Lean model

Status: **conditional model, upper bounds only, no real-game claim.**
File: `Civ6Verify/Model/Mvp.lean` (module `Civ6Verify.Model.Mvp`).
Contract: `mvp/RULE-CONTRACT.md` **v2.1**, θ* = (settlerCost 80, `growth_first`,
`newCitizen = best`, amenityStock 2, basket zero, exact production, threshold
3383). The only parameterised axis is cost (80 → `8000`, 110 → `11000`).
No Civ6 build/fixture was run; this module does not assert that Civ6 implements
these rules.

What is **not** in this file:

* no `OptimalAt` at 20, no `NoEarlier` at 20, no full-horizon certificate;
* no exact-step frontier at all (no `Frontier` call, no layer enumeration);
* no G1/G4 re-derivation (max population / max food by enumeration) and no
  `horizonOk : ∀ θ ∈ Θ, N(θ) ≤ H = 34`;
* no 128-θ box, no interval/envelope proof, no inertness lemmas for C2–C7;
* no `[V]` claim, no build hash, no real-game turn count.

The two known-good facts are: (i) the `Model` instance is sound and complete
for v2.1's Option step, and (ii) the contract's baseline witness is legal and
reaches `trained = 1` at step 20 by kernel reduction. The second is an
**achievability/upper-bound** result, not a minimality result. The cost-110
variant is the analogous upper bound at 25.

> **v2.1 alignment.** Both `RULE-CONTRACT.md` and
> `fixtures/mvp-rule-candidates.json` now report v2.1. The fixture's growth row
> is `extra: None`, `q = 420` (not the v2 `525`), with `F = P = 400`. This
> module reproduces exactly that row; see §3. The v2 `q = 525` reading is
> superseded and is not implemented.

---

## 1. Contract → Lean cross-walk

| Contract §0/§3/§4 element | Lean name |
|---|---|
| `S = (pop, food, prog, trained)` | `State`, `init` |
| `A = (work, extra, build)` | `Action` (`work : Fin 16` bitmask, `extra : Option (Fin 4)`, `build : Build`) |
| tiles G/GH/PH/P | `tileFood`, `tileProd`; ids `tileG/tileGH/tilePH/tileP`; `workTiles` |
| `F = 200 + Σ_work food` | `baseFood` |
| `P = 300 + Σ_work prod` | `baseProd` |
| `d = F − 200·pop` | `surplus` |
| `e = d·growthMult/100` | `growthAmount` |
| `T(1..3)` | `threshold` (`1500`, `2400`, `3383`) |
| `grow(b,p)` one growth, basket zero | `wouldGrow`, `popAfter`, `foodAfter` |
| `extraGain(⊥) = 0` | `extraGain` |
| `P += extraGain(extra)` on growth | `production` |
| `q = P·prodMult(tier(pop1))/100` | `qOf` |
| `CREDIT(q)` only for SETTLER | `credit`, `progAfter` |
| completion / `trained+1` | `completes`, total core `step` |
| `step : State → Action → Option State` | `step?` |
| `legal s a := (step s a).isSome` | `Model.legal` = `(step? p s a).isSome = true`; readable `legal`/`legalGuard` |
| `step_total` | `step_total`, `step_total_of_legal`, `step?_eq_some` |
| `allActions` | `allActions` (List), `legalActionsFor`, `mem_legalActionsFor` |
| goal `trained ≥ 1` | `goal`, `goalB`, `goalB_spec` |
| θ* | `baselineParams`, `baseline = model baselineParams` |
| θ cost 110 | `cost110Params`, `cost110 = model cost110Params` |
| witness | `witness`, `witness110` |

All numeric values are integers in 1/100 units; `Int` is used only for the
signed amenity balance. There is no `Float`, no `Rat`, no Mathlib. `allActions`
is a duplicate-free `List` rather than a `Finset` (no Mathlib); it is the full
product `16 masks × 5 extra values × 2 builds = 160` candidates, which is the
same set as the powerset product.

### Legality (v2.1)

`legalGuard s a` is the readable conjunction:

1. `workCount a ≤ s.pop` — tile capacity 1 is structural (a bitmask cannot
   repeat a tile), and no more citizens are assigned than exist;
2. `extraUnworked a = true` — a present extra tile is not already worked;
3. `a.build = SETTLER → 2 ≤ s.pop` — **pre-turn** population only (A8);
4. `a.build = IDLE → a.extra = none` — frozen v2.1 rule (no extra under IDLE);
5. `200 * s.pop ≤ baseFood a` — no negative pre-modifier surplus (starvation is
   not an action).

The extra tile is **optional** on a growth step: `extraGain(none) = 0`, so a
growth with no extra is legal and contributes no extra production. The v2.1
baseline growth step is IDLE with `extra = none`; its `q` is 420 and is
discarded by IDLE. The v2-only reading (`P += prod(extra)` with an extra tile,
`q = 525`) is not used.

### Option step and the total core

The frozen interface is `step : State → Action → Option State` with
`legal s a := (step s a).isSome`. The generic `Civ6Verify.Reachability.Model`
class requires a total `step`, so this module provides both:

* `step p s a` — the total core, exactly §4's arithmetic;
* `step? p s a` — `if legalGuard s a then some (step p s a) else none`;
* `Model.legal` for parameter `p` is literally
  `fun s a => (step? p s a).isSome = true`;
* `step?_eq_some`, `step_total`, `step_total_of_legal` prove O2b.

The readable external predicate `legal s a` uses `step? baselineParams`; since
the guard does not depend on cost, `legal_iff_guard` and `step?_isSome` connect
it to the guard for every parameter. `Reachable` composes only legal actions,
so the total core is meaningful on every path.

### Step order (`growth_first`, baseline)

1. `F = 200 + Σ_work food` (extra never feeds `F`);
2. `d = F − 200·pop` (legality guarantees no truncation);
3. `e = d·110/100` for the baseline (Happy, amenityStock 2, pop ≤ 3);
4. one growth iff `food + e ≥ threshold pop`; on growth `pop+1`, basket `0`;
5. `P = 300 + Σ_work prod + (grown ? extraGain(extra) : 0)`;
6. `q = P·105/100` with `tier(popAfter)`, exact rounding;
7. `prog += q` only for SETTLER (IDLE adds zero);
8. completion iff SETTLER and `progAfter ≥ cost`: `pop := popAfter − 1`,
   `prog := progAfter − cost`, `trained += 1`.

`step` is total. Illegal actions are not composed by `Reachable`, so their
truncated `Nat` subtraction is irrelevant to every theorem.

`growthAmount` and `qOf` use total floor division. On the witness every operand
is a multiple of 100, and the kernel-checked trace facts confirm the exact
values (220, 110, 420, 630). A general lemma that every reachable `d`/`P` is a
multiple of 100 is **not** proved here; the contract's G6 finite-yield-set
argument is the intended justification.

---

## 2. The `Model` instance

```lean
def model (p : Params) : Model State Action :=
  { init := init
    step := step p
    legal := fun s a => (step? p s a).isSome = true
    legalDec := ...
    legalActions := legalActionsFor p
    legalActions_sound := ...   -- from mem_legalActionsFor
    legalActions_complete := ... }
```

`baseline = model baselineParams` and `cost110 = model cost110Params`. `legal`
does not depend on cost; only completion does. The enumeration filters the
160-candidate list by `(step? p s a).isSome`, exactly the `Model.legal`
predicate, so completeness is proved rather than assumed.

Useful fields/lemmas:

* `mem_allActions : a ∈ allActions`
* `mem_legalActionsFor : a ∈ legalActionsFor p s ↔ legalGuard s a`
* `mem_legalActions : a ∈ legalActions s ↔ legal s a`
* `legal_iff_guard`, `step?_isSome`, `step?_eq_some`, `step_total`,
  `step_total_of_legal`, `model_legal_iff_guard`, `model_legal_iff`
* `legal_workCount`, `legal_extraUnworked`, `legal_settler_pop`,
  `legal_idle_extra_none`, `legal_surplus`
* `legal_extra_not_work`, `extraUnworked_spec`, `workCount_le_four`
* `extraGain_none`, `extraGain_some`
* `credit_zero_of_prePop_lt_two`, `step_prog` (progress accounting)
* `step_idle_prog`, `step_idle_trained`, `step_no_growth_production`,
  `popAfter_eq`
* `step_trained_ge`, `goal_step`, `goal_run`

The last three express the terminal/history requirement: `trained` never
decreases and the goal, once true, remains true along every run.

---

## 3. Baseline witness (kernel-checked, v2.1)

`witness` is the contract's v2.1 playout:

```
GH × 7 with IDLE, extra none (the t=7 step grows; q = 420 is discarded)
GH+PH × 13 with SETTLER, extra none
```

Kernel-reduced trace (`model baselineParams`, cost 8000):

| t | pre-pop | work | build | extra | e | q | food after | prog after | trained |
|---|---|---|---|---|---|---|---|---|---|
| 1–6 | 1 | GH | IDLE | none | 220 | 420 (discarded) | 220 … 1320 | 0 | 0 |
| 7 | 1 | GH | IDLE | none | 220 | 420 (discarded) | 0, pop 2 | 0 | 0 |
| 8–19 | 2 | GH,PH | SETTLER | none | 110 | 630 | 110 … 1320 | 630 … 7560 | 0 |
| 20 | 2 | GH,PH | SETTLER | none | 110 | 630 | 1430 | 8190 → 190 | 1 |

Final state `(pop 1, food 1430, prog 190, trained 1)`. The 13 settler steps
give `13·630 = 8190 ≥ 8000`, so completion happens at step 20. The growth
step is `1320 + 220 = 1540 ≥ 1500`, with the basket emptied (40 discarded).
`extraGain(none) = 0`, so `P = 400` and `q = 420` at t=7; IDLE credits zero.

Lean theorems:

* `witness_length = 20`, `witness_legal : LegalPath (model baselineParams) init witness`
* `witness_after_six`, `witness_growth`, `witness_growth_amount`,
  `witness_growth_q` (= 420), `witness_after_seven`, `witness_settler_q`,
  `witness_after_nineteen`
* `witness_run` (the final state above)
* `baseline_achievable : AchievableAt (model baselineParams) goal 20`
* `witness_first_mem`, `witness_growth_mem`, `witness_settler_mem` — the three
  action shapes are members of the *computed* `legalActions` at their states.

Cost 110 (`witness110`): same 7-step prefix, then 18 SETTLER steps. Final state
`(pop 1, food 1980, prog 340, trained 1)` at step 25; `cost110_achievable :
AchievableAt (model cost110Params) goal 25`, again an upper bound only.

The lower-bound side is only a smoke test: `noEarlier_one` and `noEarlier_two`
use the generic `NoEarlier` definition. `noEarlier_two` uses the pop-1
SETTLER guard plus IDLE zero-credit, not a frontier. No lower bound at 20 is
proved here.

---

## 4. Conditions, interpretations and discrepancies

**C1 — contract/fixture v2.1 agree; the v2 `q = 525` row is superseded.**
Contract and fixture both report v2.1, and the fixture's `selfCheckTrace` now
has `extra: None`, `F = P = 400`, `q = 420` on the growth row. This module
reproduces `420`, not the v2-only `525`. Because the growth step is IDLE and
credits zero, the step-20 final state is the same under either q value; the
difference is semantic, not an N difference.

**C2 — v2 §3/§4 conflict is resolved by v2.1, not by an extra requirement.**
v2 said both `IDLE ⇒ extra = ⊥` and "extra exists by legality" on growth, with
a witness `q = 525`. v2.1 totalises `extraGain(⊥) = 0`, so a growth with no
extra is legal and contributes zero. This module uses exactly that: no
"extra exists on growth" restriction, no `IDLE + extra` action. The v2-only
reading is not implemented.

**C3 — Option step vs total core.** The contract freezes
`step : State → Action → Option State`; the reusable `Model` class needs a
total `step`. Both are provided: `step?` is the normative Option step, and
`step` is its total core. `Model.legal` is literally `(step? p s a).isSome =
true`, and `step_total` proves O2b. `Reachable` only composes legal actions.

**C4 — T(3) and the C7 axis.** `threshold 3 = 3383` in 1/100 units. `T(3) =
33.8284` food; integer food `≥ 3383` is exactly `≥ 33.8284`. Contract v2.1
argues C7 is inert by G1; this module does not re-derive G1 and simply fixes
the exact reading. The C7 alternative `3300` (floor) is **not** modelled. `T(4)
= 4420` and the fallback are defined for totality; the baseline path does not
use them.

**C5 — cost scaling and the other axes.** Game cost 80 is `8000`; 110 is
`11000`. `Params.cost` is the only parameterised axis. `growth_first`,
`newCitizen = best`, `amenityStock = 2`, `basket = zero`,
`productionRounding = exact`, `thresholdRounding = exact` are fixed.
`amenityBalance` hardcodes stock 2 and implements the full Happy/Content/
Displeased tiers, but no reachable-population bound (G1/G4) is proved here. On
the witness path pop ≤ 2, so the multipliers used are 110/105. `newCitizen =
best` is represented by letting the action choose `extra`; the enumeration
contains every unworked tile, hence the best one. There is no automatic
maximisation inside `step`. `H = 34` and `horizonOk` are not modelled.

**C6 — no `Finset`.** The contract's `allActions s : Finset Action` is
represented by a duplicate-free `List` because the project is Mathlib-free.
The 16 masks are exactly the powerset of the four tiles; `mem_allActions` and
`mem_legalActionsFor` prove the enumeration complete. This is a representation
difference, not a missing completeness proof.

**C7 — "idle-free" in O5 is read as "no unworked citizen".** The witness has
`workCount = pop` at every step (1 at pop 1, 2 at pop 2), but the prefix uses
`build = IDLE` because SETTLER is illegal at pre-turn pop 1. If "idle-free"
were read as `build ≠ IDLE`, no pop-1 prefix could exist. The file's reading is
the one consistent with §10.

**C8 — `SEMANTIC-REVIEW.md` is v2, not v2.1.** It still discusses the v2
`q = 525` row and `H = 27`; it predates the v2.1 changelog. Do not use it as a
v2.1 acceptance oracle. Its v1 numbers are invalid and must not be reused.

**C9 — integration: root/lakefile were not edited.** Per the task boundary,
only `Civ6Verify/Model/Mvp.lean` and this document were added. Consequences:

* `scripts/lean-env lake env lean Civ6Verify/Model/Mvp.lean` compiles the
  module directly;
* `scripts/lean-env lake build Civ6Verify.Model.Mvp` builds the olean;
* a plain `lake build` still succeeds but does **not** build this module
  (the default target is the existing root/executable graph);
* `scripts/audit-axioms.py` discovers and imports every module under
  `Civ6Verify/**`, so it audits this module **once its olean exists**. On a
  clean tree, run the module target first, or the owner must add
  `import Civ6Verify.Model.Mvp` to `Civ6Verify.lean` or a Lake glob/target.
  This is an integration wiring gap, not a proof gap. The same applies to any
  parallel module under `Civ6Verify/Bounds/`.

**C10 — no real-game claim.** The 20/25 values are model-internal, conditional
on A1–A8, the restrictions X1–X17/X19/X20, the §8.1 restrictions, and the
model choices above. IDLE legitimacy depends on X4–X7. `[V] = 0`; no fixture
was run.

---

## 5. Build, audit and performance

```bash
# direct module check
scripts/lean-env lake env lean Civ6Verify/Model/Mvp.lean

# Lake target (writes the olean used by the audit probe)
scripts/lean-env lake build Civ6Verify.Model.Mvp

# project-wide axiom audit (module is discovered automatically once built)
python3 scripts/audit-axioms.py --no-build
```

Measured locally (Lean 4.25.0, project-local `.tools`):

* direct module compile: ~0.9 s, no warnings;
* `lake build Civ6Verify.Model.Mvp`: ~0.9 s;
* `audit-axioms.py --no-build`: ~4 s; in the current tree (which also contains
  a parallel `Civ6Verify/Bounds/MvpArithmetic.lean`) it reports 490 public
  theorem constants + 21 private generated constants; the exact count is not
  stable while parallel modules are being added. The dependency histogram
  contains only `propext` and `Quot.sound`; no `sorryAx`, no
  `Classical.choice`, no `Lean.ofReduceBool`, no custom axiom.

The only expensive kernel reductions are the witness replays (20 and 25 steps)
and a handful of ground trace facts. No frontier is computed, so the usual
layer-size blow-up does not apply yet.

---

## 6. What a full certificate still needs

1. **Lower bound at 20.** Either build exact-step frontiers `0…19` and use
   `checkNoGoalBelow`/`earliestGoalTick?`, or prove a semantic invariant
   (pre-turn pop < 2 through step 7, then `prog` cannot reach 8000 before step
   20). The latter avoids a large kernel reduction but needs a careful
   food/legality induction.
2. **G1/G4 by enumeration** for the certified θ: max pop, max pop-2 food, max
   pop-3 food, and confirm `T(4)` is never evaluated. Contract v2.1 claims C7
   inert by G1; that proof is not in this module.
3. **`OptimalAt (model baselineParams) goal 20`** once (1) is available.
4. For the argmax θ (cost 110): the analogous lower bound at 25,
   `OptimalAt`, and `horizonOk` for `H = 34`.
5. Only then consider the other 126 θ; without inertness lemmas for C2–C7 the
   interval stays a search estimate (O7).
6. Wire the module into the root import graph / Lake target so a clean
   `lake build && audit-axioms.py` covers it (C9).

Until 1–3 are done, the honest claim is exactly: **the baseline witness is
legal under the v2.1 Option step and completes at step 20; the model's action
enumeration is sound and complete; no minimality claim is made.**
