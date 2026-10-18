/-
  Civ6Verify/Robustness/Candidates.lean

  **Candidate-axis robustness for the conditional MVP model** `M_MVP(θ, σ)`
  (`mvp/RULE-CONTRACT.md` v2.1 §6). Owner: candidate-robustness milestone.
  Companion document: `mvp/ROBUSTNESS.md`.

  What this module does
  ---------------------
  The existing Lean development parameterises **only** the `settlerCost` axis
  (`Civ6Verify.Model.Mvp.Params.cost`): C2–C7 are hard-wired to the baseline
  θ* = (growth_first, best, amenityStock 2, basket zero, exact, exact 3383).
  `mvp/RESULTS.md` §1.1 records that limitation, and §10 of the contract
  records the untrusted Python search estimate that C2–C7 are inert.

  This module supplies an **explicit alternative semantics** in its own
  namespace and proves, inside the kernel, that the axis is inert on the
  reachable set of the model. It does **not** rebrand the baseline: the
  alternative semantics is a separate definitional pipeline and the
  equivalence is a theorem about it.

  Certified here
  --------------
  * **C7 `thresholdRounding`** (`exact 3383` vs `floor 3300`). The two readings
    of `T(3)` differ only at population 3, and the existing ladder invariant
    `Inv` bounds `food + e ≤ 1600 < 3300` at population 3 for every reachable
    state with `t ≤ 24`. Hence the floor semantics and the baseline semantics
    agree step-for-step on every reachable state in the certified horizon, so
    `OptimalAt` transfers: 20 (cost 80) and 25 (cost 110) are unchanged.
  * **C3 `newCitizen`** (`best` vs `none`) and **C6 `productionRounding`**
    (`exact` vs `trunc10`), by an explicit **coupling** argument: both only
    lower the credited production `q` pointwise, and `q` does not influence
    food, population or legality, so the baseline lower bound dominates every
    alternative run. This is proved in §4 (`coupled_*`).
  * **C1 `settlerCost`** is already parameterised and certified at both
    endpoints; this module adds the C7 alternative at *both* cost endpoints.

  Not certified (reported in `mvp/ROBUSTNESS.md`)
  ----------------------------------------------
  * **C2 `turnOrder`** (`growth_first` vs `production_first`): a genuinely
    different intra-step order; the alternative changes the growth/production
    interleaving, so no step-equivalence or pointwise-`q` dominance holds.
    Front-end and not discharged here.
  * **C4 `amenityStock`** (`2` vs `1`): differs at population 3, where
    `stock − req(3) = 1` (Happy) becomes `0` (Content), changing *both* the
    growth and the production multiplier. Neither equivalence nor the `q`
    coupling applies; the lower bound would have to be re-derived for the
    Content tier at population 3.
  * **C5 `basketOnGrowth`** (`zero` vs `subtract`): changes the stored food and
    hence future growth timing; no dominance lemma is available.

  Trust boundary
  --------------
  * No `sorry`, no `admit`, no custom axiom, no `native_decide`, no Mathlib.
  * Everything is kernel-checked; closed numeric facts use `decide +kernel`
    (kernel reduction, no compiler trust, no `Lean.ofReduceBool`).
  * `Civ6Verify/Model/Mvp.lean`, `Civ6Verify/Bounds/MvpOptimality.lean` and the
    root module are **not** modified; this file only imports them.
  * The claims are model-internal and conditional on A1/A2/A8 and the §8.1
    no-carry restriction, exactly as the baseline. `[V] = 0`, no build pinned.

  API summary
  -----------
  * `thresholdT3Floor` — the alternative `T(3) = 3300` reading.
  * `stepT Tm p s a` — the full §4 pipeline with threshold function `Tm` and
    its own `q`; `stepT threshold = step` definitionally on the baseline.
  * `stepT_threshold_eq`, `stepT_floor_eq_step_of_inv` — agreement lemmas.
  * `modelF p` — `Model` instance with the floor threshold semantics.
  * `inv_of_reachable_floor`, `floor_noEarlier_20/25` — lower bound.
  * `floor_optimalAt_baseline`, `floor_optimalAt_cost110` — headline.
  * `Dom`, `qOf_dom`, `stepQ`, `stepQ_dom` — the pointwise-`q` coupling used
    for C3/C6, with `modelQ_coupled_noEarlier_20`.
-/

import Civ6Verify.Bounds.MvpOptimality

namespace Civ6Verify.Robustness.Candidates

open Civ6Verify.Reachability
open Civ6Verify.Model.Mvp
open Civ6Verify.Bounds.MvpOptimality

/-! ## 1. C7: the alternative `T(3) = 3300` threshold

  `thresholdT3Floor` is `Civ6Verify.Model.Mvp.threshold` with the single entry
  `3 ↦ 3300` instead of `3383`. The contract's C7 axis is
  `thresholdRounding ∈ {exact, floor}` and `threshold` is the `exact` reading,
  so this is exactly the `floor` candidate. -/

/-- The `thresholdRounding = floor` reading of the growth thresholds:
`T(3) = 3300` (`33.00` food) instead of the exact comparison bound `3383`. -/
def thresholdT3Floor : Nat → Nat
  | 0 => 100000000
  | 1 => 1500
  | 2 => 2400
  | 3 => 3300
  | 4 => 4420
  | _ => 100000000

theorem thresholdT3Floor_three : thresholdT3Floor 3 = 3300 := rfl

/-- The two readings agree off population 3. -/
theorem thresholdT3Floor_eq_threshold_of_ne {p : Nat} (h : p ≠ 3) :
    thresholdT3Floor p = threshold p := by
  match p with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => exact absurd rfl h
  | 4 => rfl
  | _ + 5 => rfl

/-! ## 2. The alternative pipeline

  This is a verbatim re-instantiation of §4 of the contract, with the growth
  threshold supplied as a parameter `Tm`. Nothing about the baseline is
  assumed: `stepT threshold` is then proved definitionally equal to the
  baseline `step` (`stepT_threshold_eq`). -/

/-- Growth test under threshold function `Tm`. -/
def wg (Tm : Nat → Nat) (s : State) (a : Action) : Bool :=
  decide (s.food + growthAmount s a ≥ Tm s.pop)

/-- Population after the growth phase under `Tm`. -/
def popAfterT (Tm : Nat → Nat) (s : State) (a : Action) : Nat :=
  if wg Tm s a then s.pop + 1 else s.pop

/-- Food basket after the growth phase under `Tm` (baseline `basket zero`). -/
def foodAfterT (Tm : Nat → Nat) (s : State) (a : Action) : Nat :=
  if wg Tm s a then 0 else s.food + growthAmount s a

/-- Production `P` under `Tm` (extra tile only on an actual growth event). -/
def productionT (Tm : Nat → Nat) (s : State) (a : Action) : Nat :=
  baseProd a + (if wg Tm s a then extraGain a else 0)

/-- `q = P · prodMult(tier(popAfter)) / 100` under `Tm`, exact rounding. -/
def qOfT (Tm : Nat → Nat) (s : State) (a : Action) : Nat :=
  productionT Tm s a * prodMult (popAfterT Tm s a) / 100

/-- Settler progress after the production phase under `Tm`. -/
def progAfterT (Tm : Nat → Nat) (s : State) (a : Action) : Nat :=
  s.prog + credit a (qOfT Tm s a)

/-- Completion test under `Tm`. -/
def completesT (p : Params) (Tm : Nat → Nat) (s : State) (a : Action) : Prop :=
  a.build = Build.settler ∧ progAfterT Tm s a ≥ p.cost

instance (p : Params) (Tm : Nat → Nat) (s : State) (a : Action) :
    Decidable (completesT p Tm s a) := by
  unfold completesT
  infer_instance

/-- One settlement step with growth threshold `Tm`, otherwise exactly §4. -/
def stepT (Tm : Nat → Nat) (p : Params) (s : State) (a : Action) : State :=
  if completesT p Tm s a then
    { pop := popAfterT Tm s a - 1, food := foodAfterT Tm s a,
      prog := progAfterT Tm s a - p.cost, trained := s.trained + 1 }
  else
    { pop := popAfterT Tm s a, food := foodAfterT Tm s a,
      prog := progAfterT Tm s a, trained := s.trained }

/-- `wg` at the baseline threshold is the model's `wouldGrow`. -/
theorem wg_threshold_eq (s : State) (a : Action) :
    wg threshold s a = wouldGrow s a := rfl

/-- **Definitional sanity check:** the parameterised pipeline at the baseline
threshold is the baseline model's step. This is what makes the parameterisation
an extension, not a fork. -/
theorem stepT_threshold_eq (p : Params) (s : State) (a : Action) :
    stepT threshold p s a = step p s a := by
  have hpa : popAfterT threshold s a = popAfter s a := rfl
  have hfa : foodAfterT threshold s a = foodAfter s a := rfl
  have hpr : productionT threshold s a = production s a := rfl
  have hq : qOfT threshold s a = qOf s a := by
    simp only [qOfT, qOf, hpa, hpr]
  have hga : progAfterT threshold s a = progAfter s a := by
    simp only [progAfterT, progAfter, hq]
  have hciff : completesT p threshold s a ↔ completes p s a := by
    simp only [completesT, completes, hga]
  unfold stepT step
  by_cases hcb : completes p s a
  · rw [if_pos (hciff.mpr hcb), if_pos hcb]
    simp only [hpa, hfa, hga]
  · rw [if_neg (fun hh => hcb (hciff.mp hh)), if_neg hcb]
    simp only [hpa, hfa, hga]

/-! ## 3. C7 agreement on the reachable set

  The floor reading differs from the exact reading only through `wg`. We prove
  that on every state satisfying the existing ladder invariant `Inv` (which
  every reachable state with `t ≤ 24` satisfies), `wg` is unchanged. -/

/-- On `Inv`-bounded states up to the ladder horizon, the floor and exact
thresholds give the same growth test. At population 1–2 the thresholds are
literally equal; at population 3 the ladder keeps `food + e ≤ 1600`, far below
both `3300` and `3383`, so neither reading grows. -/
theorem wg_floor_eq_wg {n : Nat} {s : State} {a : Action}
    (hinv : Inv n s) (hn : n ≤ 24) (hleg : legal s a) :
    wg thresholdT3Floor s a = wg threshold s a := by
  unfold wg
  by_cases hp3 : s.pop = 3
  · -- population 3: both thresholds are not crossed
    have hladder : (s.food : Int) + floorI s.pop ≤ 220 * (n : Int) := hinv.1
    have hf3 : floorI s.pop = 3900 := by rw [hp3]; decide +kernel
    rw [hf3] at hladder
    have hnI : (n : Int) ≤ 24 := by exact_mod_cast hn
    have hfoodI : (s.food : Int) ≤ 1380 := by omega
    have he : growthAmount s a ≤ 220 := growthAmount_le_220 s a hleg hinv.2.1
    have hx : s.food + growthAmount s a < 3300 := by omega
    have h3300 : thresholdT3Floor s.pop = 3300 := by rw [hp3]; rfl
    have hexact : threshold s.pop = 3383 := by rw [hp3]; rfl
    rw [h3300, hexact]
    have h1 : decide (s.food + growthAmount s a ≥ 3300) = false := by
      rw [decide_eq_false_iff_not]; omega
    have h2 : decide (s.food + growthAmount s a ≥ 3383) = false := by
      rw [decide_eq_false_iff_not]; omega
    rw [h1, h2]
  · rw [thresholdT3Floor_eq_threshold_of_ne hp3]

/-- `qOfT` and `completesT` are determined by `wg`. -/
theorem qOfT_eq_of_wg {Tm : Nat → Nat} {s : State} {a : Action}
    (h : wg Tm s a = wouldGrow s a) : qOfT Tm s a = qOf s a := by
  have hpa : popAfterT Tm s a = popAfter s a := by simp [popAfterT, popAfter, h]
  have hpr : productionT Tm s a = production s a := by simp [productionT, production, h]
  simp only [qOfT, qOf, hpa, hpr]

theorem progAfterT_eq_of_wg {Tm : Nat → Nat} {s : State} {a : Action}
    (h : wg Tm s a = wouldGrow s a) : progAfterT Tm s a = progAfter s a := by
  simp only [progAfterT, progAfter, qOfT_eq_of_wg h]

/-- Threshold agreement is enough for full step agreement. -/
theorem stepT_eq_of_wg {Tm : Nat → Nat} {p : Params} {s : State} {a : Action}
    (h : wg Tm s a = wouldGrow s a) : stepT Tm p s a = step p s a := by
  have hpa : popAfterT Tm s a = popAfter s a := by simp [popAfterT, popAfter, h]
  have hfa : foodAfterT Tm s a = foodAfter s a := by simp [foodAfterT, foodAfter, h]
  have hga : progAfterT Tm s a = progAfter s a := progAfterT_eq_of_wg h
  have hciff : completesT p Tm s a ↔ completes p s a := by
    simp only [completesT, completes, hga]
  unfold stepT step
  by_cases hcb : completes p s a
  · rw [if_pos (hciff.mpr hcb), if_pos hcb]
    simp only [hpa, hfa, hga]
  · rw [if_neg (fun hh => hcb (hciff.mp hh)), if_neg hcb]
    simp only [hpa, hfa, hga]

/-- **C7 inertness, step form.** On every state reachable within the certified
horizon the floor semantics performs exactly the same settlement step as the
baseline. -/
theorem stepT_floor_eq_step {n : Nat} {p : Params} {s : State} {a : Action}
    (hinv : Inv n s) (hn : n ≤ 24) (hleg : legal s a) :
    stepT thresholdT3Floor p s a = step p s a :=
  stepT_eq_of_wg (wg_floor_eq_wg hinv hn hleg)

/-! ## 4. The alternative model instance -/

/-- The MVP `Model` with the `thresholdRounding = floor` semantics. Legality,
`init` and the action enumeration are the model's own (the guard does not
mention the threshold), so soundness/completeness transfer from
`mem_legalActions`. -/
def modelF (p : Params) : Model State Action where
  init := init
  step := stepT thresholdT3Floor p
  legal := fun s a => legal s a
  legalDec := fun s a => (inferInstance : Decidable (legal s a))
  legalActions := legalActions
  legalActions_sound := fun s a h => (mem_legalActions s a).mp h
  legalActions_complete := fun s a h => (mem_legalActions s a).mpr h

theorem modelF_legal_iff (p : Params) (s : State) (a : Action) :
    (modelF p).legal s a ↔ legal s a := Iff.rfl

/-! ## 5. Lower bound under the floor semantics

  The `Inv` invariant is carried over the *alternative* model by reusing
  `inv_step` at each step, because the step is equal to the baseline step on
  every `Inv` state. -/

theorem inv_of_reachable_floor (p : Params) (C T : Nat) (hcost : p.cost = C)
    (hT : T ≤ 24) (hC : 0 < C)
    (h2 : ∀ t, t ≤ T → 6930 * ((t : Int) - 7) < 11 * (C : Int))
    (h3 : ∀ t, t ≤ T → 9240 * (t : Int) - 111615 < 11 * (C : Int)) :
    ∀ t, t ≤ T → ∀ s, Reachable (modelF p) t s → Inv t s := by
  intro t
  induction t with
  | zero =>
      intro _ s hs
      cases hs with
      | zero => exact inv_init
  | succ n ih =>
      intro hTt s hs
      cases hs with
      | @succ n' s0 a hreach hlegal =>
          have hleg : legal s0 a := hlegal
          have hinv : Inv n s0 := ih (by omega) s0 hreach
          have hn : n ≤ 23 := by omega
          have hn24 : n ≤ 24 := by omega
          have hstep := stepT_floor_eq_step (n := n) (p := p) (s := s0) (a := a)
            hinv hn24 hleg
          have h2n : 6930 * ((n : Int) + 1 - 7) < 11 * (C : Int) := by
            have := h2 (n + 1) hTt
            have hcast : (((n + 1 : Nat)) : Int) = (n : Int) + 1 := by push_cast; rfl
            rw [hcast] at this
            exact this
          have h3n : 9240 * ((n : Int) + 1) - 111615 < 11 * (C : Int) := by
            have := h3 (n + 1) hTt
            have hcast : (((n + 1 : Nat)) : Int) = (n : Int) + 1 := by push_cast; rfl
            rw [hcast] at this
            exact this
          have hstep' : (modelF p).step s0 a = (model p).step s0 a := hstep
          rw [hstep']
          exact inv_step p C hC hcost hinv hleg hn h2n h3n

/-- **C7 lower bound at 20** for the floor semantics, cost 80. -/
theorem floor_noEarlier_20 (p : Params) (hcost : p.cost = 8000) :
    NoEarlier (modelF p) goal 20 := by
  have hT : 19 ≤ 24 := by decide
  have hC : 0 < 8000 := by decide
  have h2 : ∀ t : Nat, t ≤ 19 → 6930 * ((t : Int) - 7) < 11 * (8000 : Int) := by
    intro t ht
    have : (t : Int) ≤ 19 := by exact_mod_cast ht
    omega
  have h3 : ∀ t : Nat, t ≤ 19 → 9240 * (t : Int) - 111615 < 11 * (8000 : Int) := by
    intro t ht
    have : (t : Int) ≤ 19 := by exact_mod_cast ht
    omega
  intro t ht s hreach hgoal
  have ht19 : t ≤ 19 := by omega
  have hinv := inv_of_reachable_floor p 8000 19 hcost hT hC h2 h3 t ht19 s hreach
  have hzero : s.trained = 0 := hinv.2.2.1
  unfold goal at hgoal
  omega

/-- **C7 lower bound at 25** for the floor semantics, cost 110. -/
theorem floor_noEarlier_25 (p : Params) (hcost : p.cost = 11000) :
    NoEarlier (modelF p) goal 25 := by
  have hT : 24 ≤ 24 := by decide
  have hC : 0 < 11000 := by decide
  have h2 : ∀ t : Nat, t ≤ 24 → 6930 * ((t : Int) - 7) < 11 * (11000 : Int) := by
    intro t ht
    have : (t : Int) ≤ 24 := by exact_mod_cast ht
    omega
  have h3 : ∀ t : Nat, t ≤ 24 → 9240 * (t : Int) - 111615 < 11 * (11000 : Int) := by
    intro t ht
    have : (t : Int) ≤ 24 := by exact_mod_cast ht
    omega
  intro t ht s hreach hgoal
  have ht24 : t ≤ 24 := by omega
  have hinv := inv_of_reachable_floor p 11000 24 hcost hT hC h2 h3 t ht24 s hreach
  have hzero : s.trained = 0 := hinv.2.2.1
  unfold goal at hgoal
  omega

/-! ## 6. Upper bound under the floor semantics

  The baseline witness (GH × 7 IDLE, then GH+PH × 13/18 SETTLER) is replayed
  through the alternative `step`. Along it every state has `pop ≤ 2`, so the
  floor/exact threshold distinction is never consulted; the boolean device
  below ties the replay to `LegalPath` of `modelF`. -/

/-- Computable legality replay for the floor model. -/
def legalPathF (p : Params) : State → List Action → Bool
  | _, [] => true
  | s, a :: rest => decide (legal s a) && legalPathF p (stepT thresholdT3Floor p s a) rest

theorem legalPathF_sound (p : Params) :
    ∀ (s : State) (as : List Action), legalPathF p s as = true →
      LegalPath (modelF p) s as
  | s, [], _ => LegalPath.nil s
  | s, a :: rest, h => by
      rw [legalPathF, Bool.and_eq_true] at h
      exact LegalPath.cons (of_decide_eq_true h.1)
        (legalPathF_sound p (stepT thresholdT3Floor p s a) rest h.2)

theorem floor_witness_legal :
    LegalPath (modelF baselineParams) init witness :=
  legalPathF_sound baselineParams init witness (by decide +kernel)

/-- Replaying the baseline witness through the floor semantics reaches exactly
the baseline final state: the floor reading is invisible on the witness. -/
theorem floor_witness_run :
    run (modelF baselineParams) init witness =
      { pop := 1, food := 1430, prog := 190, trained := 1 } := by
  decide +kernel

theorem floor_witness110_legal :
    LegalPath (modelF cost110Params) init witness110 :=
  legalPathF_sound cost110Params init witness110 (by decide +kernel)

theorem floor_witness110_run :
    run (modelF cost110Params) init witness110 =
      { pop := 1, food := 1980, prog := 340, trained := 1 } := by
  decide +kernel

theorem floor_achievable : AchievableAt (modelF baselineParams) goal 20 :=
  AchievableAt.of_legalPath (M := modelF baselineParams) (goal := goal) (N := 20)
    witness_length floor_witness_legal (by
      change goal (run (modelF baselineParams) init witness)
      rw [floor_witness_run]; unfold goal; decide +kernel)

theorem floor_achievable110 : AchievableAt (modelF cost110Params) goal 25 :=
  AchievableAt.of_legalPath (M := modelF cost110Params) (goal := goal) (N := 25)
    witness110_length floor_witness110_legal (by
      change goal (run (modelF cost110Params) init witness110)
      rw [floor_witness110_run]; unfold goal; decide +kernel)

/-! ## 7. Headline: C7 is certified inert

  The first trained Settler still completes at step 20 (cost 80) and step 25
  (cost 110) when `thresholdRounding` is switched from the exact `3383` to the
  floor `3300`. Combined with §3, this means the reported optimum does not
  depend on the C7 reading anywhere in the certified box. -/

/-- **C7 inert for the certified argmin**: `OptimalAt` at 20 holds under the
floor threshold semantics too. -/
theorem floor_optimalAt_baseline : OptimalAt (modelF baselineParams) goal 20 :=
  ⟨floor_achievable, floor_noEarlier_20 baselineParams rfl⟩

/-- **C7 inert for the certified argmax**: `OptimalAt` at 25 holds under the
floor threshold semantics too. -/
theorem floor_optimalAt_cost110 : OptimalAt (modelF cost110Params) goal 25 :=
  ⟨floor_achievable110, floor_noEarlier_25 cost110Params rfl⟩

/-- Both certified endpoints, stated together: the C7 axis is inert at both. -/
theorem c7_inert_certified :
    OptimalAt (modelF baselineParams) goal 20 ∧
    OptimalAt (modelF cost110Params) goal 25 :=
  ⟨floor_optimalAt_baseline, floor_optimalAt_cost110⟩

/-! ## 8. C3/C6: the pointwise-`q` coupling

  `newCitizen = none` removes `extraGain` from `production`, and
  `productionRounding = trunc10` replaces `q` by `⌊q/10⌋·10`. Both only lower
  the credited production, and the credited production never feeds food,
  population or legality. We therefore prove the lower bound for an arbitrary
  step whose credited `q` is pointwise `≤ qOf`: the baseline run with the same
  actions dominates the alternative run in `prog` while agreeing on
  `pop`, `food`, `trained`. -/

/-- State coupling: the alternative state agrees with the baseline state on
`pop`, `food` and `trained`, and has no more settler progress. -/
def Dom (sb sa : State) : Prop :=
  sa.pop = sb.pop ∧ sa.food = sb.food ∧ sa.trained = sb.trained ∧ sa.prog ≤ sb.prog

theorem dom_refl (s : State) : Dom s s := ⟨rfl, rfl, rfl, Nat.le_refl _⟩

/-- Coupled states have the same growth amount and growth test. -/
theorem growthAmount_dom {sb sa : State} (a : Action) (h : Dom sb sa) :
    growthAmount sa a = growthAmount sb a := by
  obtain ⟨hp, -, -, -⟩ := h
  simp only [growthAmount, surplus, baseFood, hp]

theorem wouldGrow_dom {sb sa : State} (a : Action) (h : Dom sb sa) :
    wouldGrow sa a = wouldGrow sb a := by
  have hg := growthAmount_dom a h
  obtain ⟨hp, hf, -, -⟩ := h
  simp only [wouldGrow, hg, hp, hf]

theorem popAfter_dom {sb sa : State} (a : Action) (h : Dom sb sa) :
    popAfter sa a = popAfter sb a := by
  have hg := wouldGrow_dom a h
  obtain ⟨hp, -, -, -⟩ := h
  simp only [popAfter, hg, hp]

theorem foodAfter_dom {sb sa : State} (a : Action) (h : Dom sb sa) :
    foodAfter sa a = foodAfter sb a := by
  have hg := wouldGrow_dom a h
  have hm := growthAmount_dom a h
  obtain ⟨-, hf, -, -⟩ := h
  simp only [foodAfter, hg, hm, hf]

/-- Coupled states have the same `q`. -/
theorem qOf_dom {sb sa : State} (a : Action) (h : Dom sb sa) :
    qOf sa a = qOf sb a := by
  simp only [qOf, production, popAfter_dom a h, wouldGrow_dom a h]

/-- `credit` is monotone in its `q` argument. -/
theorem credit_mono (a : Action) {q q' : Nat} (h : q ≤ q') :
    credit a q ≤ credit a q' := by
  unfold credit
  split <;> omega

/-- The alternative step for an arbitrary credited-production function `qFn`.
Everything except the credited `q` is the baseline pipeline, so the coupling
argument isolates exactly what C3 and C6 change. -/
def stepQ (qFn : State → Action → Nat) (p : Params) (s : State) (a : Action) : State :=
  if a.build = Build.settler ∧ s.prog + credit a (qFn s a) ≥ p.cost then
    { pop := popAfter s a - 1, food := foodAfter s a,
      prog := s.prog + credit a (qFn s a) - p.cost, trained := s.trained + 1 }
  else
    { pop := popAfter s a, food := foodAfter s a,
      prog := s.prog + credit a (qFn s a), trained := s.trained }

/-- `stepQ` at the model's own `q` is the baseline step. -/
theorem stepQ_qOf_eq (p : Params) (s : State) (a : Action) :
    stepQ (fun s a => qOf s a) p s a = step p s a := by
  have hciff : (a.build = Build.settler ∧ s.prog + credit a (qOf s a) ≥ p.cost) ↔
      completes p s a := Iff.rfl
  unfold stepQ step
  by_cases hcb : completes p s a
  · rw [if_pos (hciff.mpr hcb), if_pos hcb]
    simp only [progAfter]
  · rw [if_neg (fun hh => hcb (hciff.mp hh)), if_neg hcb]
    simp only [progAfter]

/-- A completion raises `trained` by one. -/
theorem trained_of_completes (p : Params) (s : State) (a : Action)
    (h : completes p s a) : (step p s a).trained = s.trained + 1 := by
  unfold step
  rw [if_pos h]

/-- `stepQ` never completes earlier than the baseline, and preserves the
coupling: if the baseline step does not complete and `qFn ≤ qOf` pointwise,
then `Dom (step …) (stepQ …)`. -/
theorem stepQ_dom {qFn : State → Action → Nat} (hq : ∀ s a, qFn s a ≤ qOf s a)
    (p : Params) {sb sa : State} {a : Action}
    (hdom : Dom sb sa) (hnc : ¬ completes p sb a) :
    Dom (step p sb a) (stepQ qFn p sa a) := by
  have hqq : qFn sa a ≤ qOf sb a := by
    have h1 := hq sa a
    rwa [qOf_dom a hdom] at h1
  have hpa := popAfter_dom a hdom
  have hfa := foodAfter_dom a hdom
  obtain ⟨hp, hf, htr, hpr⟩ := hdom
  have hcred : credit a (qFn sa a) ≤ credit a (qOf sb a) := credit_mono a hqq
  have hpgr : sa.prog + credit a (qFn sa a) ≤ sb.prog + credit a (qOf sb a) := by
    have : sa.prog ≤ sb.prog := hpr
    omega
  have hncA : ¬ (a.build = Build.settler ∧ sa.prog + credit a (qFn sa a) ≥ p.cost) := by
    rintro ⟨hb, hge⟩
    refine hnc ⟨hb, ?_⟩
    simp only [progAfter]
    omega
  have hpopB : (step p sb a).pop = popAfter sb a := by
    unfold step; rw [if_neg hnc]
  have hfoodB : (step p sb a).food = foodAfter sb a := by
    unfold step; rw [if_neg hnc]
  have hprogB : (step p sb a).prog = progAfter sb a := by
    unfold step; rw [if_neg hnc]
  have htrB : (step p sb a).trained = sb.trained := by
    unfold step; rw [if_neg hnc]
  have hpopA : (stepQ qFn p sa a).pop = popAfter sa a := by
    unfold stepQ; rw [if_neg hncA]
  have hfoodA : (stepQ qFn p sa a).food = foodAfter sa a := by
    unfold stepQ; rw [if_neg hncA]
  have hprogA : (stepQ qFn p sa a).prog = sa.prog + credit a (qFn sa a) := by
    unfold stepQ; rw [if_neg hncA]
  have htrA : (stepQ qFn p sa a).trained = sa.trained := by
    unfold stepQ; rw [if_neg hncA]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpopA, hpopB, hpa]
  · rw [hfoodA, hfoodB, hfa]
  · rw [htrA, htrB, htr]
  · rw [hprogA, hprogB]
    simpa only [progAfter] using hpgr

/-- The `Model` for an alternative credited-production function. -/
def modelQ (qFn : State → Action → Nat) (p : Params) : Model State Action where
  init := init
  step := stepQ qFn p
  legal := fun s a => legal s a
  legalDec := fun s a => (inferInstance : Decidable (legal s a))
  legalActions := legalActions
  legalActions_sound := fun s a h => (mem_legalActions s a).mp h
  legalActions_complete := fun s a h => (mem_legalActions s a).mpr h

/-- **Coupling existence, generic horizon.** Every alternative run whose
length `t ≤ T` is dominated by a baseline run with the same actions, provided
the baseline cannot complete a Settler up to `T` (supplied by the caller from
`trained_zero_at_19` / `trained_zero_at_24`). -/
theorem coupled_exists_gen (qFn : State → Action → Nat)
    (hq : ∀ s a, qFn s a ≤ qOf s a) (p : Params) (T : Nat)
    (hz : ∀ t, t ≤ T → ∀ s, Reachable (model p) t s → s.trained = 0) :
    ∀ t, t ≤ T → ∀ sa, Reachable (modelQ qFn p) t sa →
      ∃ sb, Reachable (model p) t sb ∧ Dom sb sa := by
  intro t
  induction t with
  | zero =>
      intro _ sa hsa
      cases hsa with
      | zero => exact ⟨init, ReachableFrom.zero, dom_refl init⟩
  | succ n ih =>
      intro hTt sa hsa
      cases hsa with
      | @succ n' sa0 a hreach hlegal =>
          have hlegA : legal sa0 a := hlegal
          obtain ⟨sb0, hreachB, hdom⟩ := ih (by omega) sa0 hreach
          have hlegsb : legal sb0 a := by
            -- the legality guard only mentions the population, the work set and
            -- the build choice, all of which the coupling preserves
            rw [legal_iff_guard] at hlegA ⊢
            obtain ⟨h1, h2, h3, h4, h5⟩ := hlegA
            obtain ⟨hp, -, -, -⟩ := hdom
            refine ⟨?_, h2, ?_, h4, ?_⟩
            · omega
            · intro hb; have := h3 hb; omega
            · omega
          have hlegsbModel : (model p).legal sb0 a := (model_legal_iff p sb0 a).mpr hlegsb
          have hsbReach : Reachable (model p) (n + 1) (step p sb0 a) :=
            ReachableFrom.succ hreachB hlegsbModel
          have hzsucc : (step p sb0 a).trained = 0 :=
            hz (n + 1) hTt (step p sb0 a) hsbReach
          have hnc : ¬ completes p sb0 a := by
            intro hc
            have := trained_of_completes p sb0 a hc
            omega
          exact ⟨step p sb0 a, hsbReach, stepQ_dom hq p hdom hnc⟩

/-- **Coupling existence** at the certified cost-80 horizon (`t ≤ 19`). -/
theorem coupled_exists (qFn : State → Action → Nat)
    (hq : ∀ s a, qFn s a ≤ qOf s a) (p : Params) (hcost : p.cost = 8000) :
    ∀ t, t ≤ 19 → ∀ sa, Reachable (modelQ qFn p) t sa →
      ∃ sb, Reachable (model p) t sb ∧ Dom sb sa :=
  coupled_exists_gen qFn hq p 19 (trained_zero_at_19 p hcost)

/-- **Coupling existence** at the certified cost-110 horizon (`t ≤ 24`). -/
theorem coupled_exists_110 (qFn : State → Action → Nat)
    (hq : ∀ s a, qFn s a ≤ qOf s a) (p : Params) (hcost : p.cost = 11000) :
    ∀ t, t ≤ 24 → ∀ sa, Reachable (modelQ qFn p) t sa →
      ∃ sb, Reachable (model p) t sb ∧ Dom sb sa :=
  coupled_exists_gen qFn hq p 24 (trained_zero_at_24 p hcost)

/-- **C3/C6 lower bound**: any alternative semantics whose credited production
is pointwise `≤ qOf` cannot train a Settler before step 20 (cost 80). -/
theorem modelQ_coupled_noEarlier_20 (qFn : State → Action → Nat)
    (hq : ∀ s a, qFn s a ≤ qOf s a) (p : Params) (hcost : p.cost = 8000) :
    NoEarlier (modelQ qFn p) goal 20 := by
  intro t ht sa hreach hgoal
  have ht19 : t ≤ 19 := by omega
  obtain ⟨sb, hsbreach, hdom⟩ := coupled_exists qFn hq p hcost t ht19 sa hreach
  have hz : sb.trained = 0 := trained_zero_at_19 p hcost t ht19 sb hsbreach
  obtain ⟨-, -, htr, -⟩ := hdom
  unfold goal at hgoal
  omega

/-- Excluded-middle-free instantiation for C3 (`newCitizen = none`): the extra
tile never contributes, so `q` is `baseProd`-based and pointwise smaller. -/
def qNewCitizenNone (s : State) (a : Action) : Nat :=
  baseProd a * prodMult (popAfter s a) / 100

theorem qNewCitizenNone_le (s : State) (a : Action) :
    qNewCitizenNone s a ≤ qOf s a := by
  unfold qNewCitizenNone qOf production
  have hle : baseProd a ≤ baseProd a + (if wouldGrow s a then extraGain a else 0) :=
    Nat.le_add_right _ _
  have hmul : baseProd a * prodMult (popAfter s a) ≤
      (baseProd a + (if wouldGrow s a then extraGain a else 0)) * prodMult (popAfter s a) :=
    Nat.mul_le_mul_right _ hle
  exact Nat.div_le_div_right hmul

/-- Excluded-middle-free instantiation for C6 (`productionRounding = trunc10`). -/
def qTrunc10 (s : State) (a : Action) : Nat :=
  (qOf s a / 10) * 10

theorem qTrunc10_le (s : State) (a : Action) : qTrunc10 s a ≤ qOf s a := by
  unfold qTrunc10
  exact Nat.div_mul_le_self _ _

/-- **C3 certified for the lower bound**: `newCitizen = none` cannot complete a
Settler before step 20. -/
theorem newCitizenNone_noEarlier_20 (p : Params) (hcost : p.cost = 8000) :
    NoEarlier (modelQ qNewCitizenNone p) goal 20 :=
  modelQ_coupled_noEarlier_20 qNewCitizenNone qNewCitizenNone_le p hcost

/-- **C6 certified for the lower bound**: `productionRounding = trunc10`
cannot complete a Settler before step 20. -/
theorem trunc10_noEarlier_20 (p : Params) (hcost : p.cost = 8000) :
    NoEarlier (modelQ qTrunc10 p) goal 20 :=
  modelQ_coupled_noEarlier_20 qTrunc10 qTrunc10_le p hcost

/-- **C3/C6 lower bound at the cost-110 horizon**, generic form. -/
theorem modelQ_coupled_noEarlier_25 (qFn : State → Action → Nat)
    (hq : ∀ s a, qFn s a ≤ qOf s a) (p : Params) (hcost : p.cost = 11000) :
    NoEarlier (modelQ qFn p) goal 25 := by
  intro t ht sa hreach hgoal
  have ht24 : t ≤ 24 := by omega
  obtain ⟨sb, hsbreach, hdom⟩ := coupled_exists_110 qFn hq p hcost t ht24 sa hreach
  have hz : sb.trained = 0 := trained_zero_at_24 p hcost t ht24 sb hsbreach
  obtain ⟨-, -, htr, -⟩ := hdom
  unfold goal at hgoal
  omega

/-- **C3 certified at the cost-110 horizon**: `newCitizen = none` cannot
complete a Settler before step 25. -/
theorem newCitizenNone_noEarlier_25 (p : Params) (hcost : p.cost = 11000) :
    NoEarlier (modelQ qNewCitizenNone p) goal 25 :=
  modelQ_coupled_noEarlier_25 qNewCitizenNone qNewCitizenNone_le p hcost

/-- **C6 certified at the cost-110 horizon**: `productionRounding = trunc10`
cannot complete a Settler before step 25. -/
theorem trunc10_noEarlier_25 (p : Params) (hcost : p.cost = 11000) :
    NoEarlier (modelQ qTrunc10 p) goal 25 :=
  modelQ_coupled_noEarlier_25 qTrunc10 qTrunc10_le p hcost

/-! ## 8b. C3/C6: the witness is also unaffected

  The baseline witness never declares an `extra` tile (`extraGain = 0`) and its
  credited `q` values are `420` and `630`, both multiples of ten. Hence the
  same witness drives the C3 and C6 alternative semantics to the goal at the
  same step, and both axes are inert at the certified endpoints rather than
  merely bounded below. -/

/-- Computable legality replay for the pointwise-`q` alternative model. -/
def legalPathQ (qFn : State → Action → Nat) (p : Params) :
    State → List Action → Bool
  | _, [] => true
  | s, a :: rest => decide (legal s a) && legalPathQ qFn p (stepQ qFn p s a) rest

theorem legalPathQ_sound (qFn : State → Action → Nat) (p : Params) :
    ∀ (s : State) (as : List Action), legalPathQ qFn p s as = true →
      LegalPath (modelQ qFn p) s as
  | s, [], _ => LegalPath.nil s
  | s, a :: rest, h => by
      rw [legalPathQ, Bool.and_eq_true] at h
      exact LegalPath.cons (of_decide_eq_true h.1)
        (legalPathQ_sound qFn p (stepQ qFn p s a) rest h.2)

theorem c3_witness_legal :
    LegalPath (modelQ qNewCitizenNone baselineParams) init witness :=
  legalPathQ_sound qNewCitizenNone baselineParams init witness (by decide +kernel)

theorem c3_witness_run :
    run (modelQ qNewCitizenNone baselineParams) init witness =
      { pop := 1, food := 1430, prog := 190, trained := 1 } := by
  decide +kernel

theorem c6_witness_legal :
    LegalPath (modelQ qTrunc10 baselineParams) init witness :=
  legalPathQ_sound qTrunc10 baselineParams init witness (by decide +kernel)

theorem c6_witness_run :
    run (modelQ qTrunc10 baselineParams) init witness =
      { pop := 1, food := 1430, prog := 190, trained := 1 } := by
  decide +kernel

theorem c3_witness110_legal :
    LegalPath (modelQ qNewCitizenNone cost110Params) init witness110 :=
  legalPathQ_sound qNewCitizenNone cost110Params init witness110 (by decide +kernel)

theorem c3_witness110_run :
    run (modelQ qNewCitizenNone cost110Params) init witness110 =
      { pop := 1, food := 1980, prog := 340, trained := 1 } := by
  decide +kernel

theorem c6_witness110_legal :
    LegalPath (modelQ qTrunc10 cost110Params) init witness110 :=
  legalPathQ_sound qTrunc10 cost110Params init witness110 (by decide +kernel)

theorem c6_witness110_run :
    run (modelQ qTrunc10 cost110Params) init witness110 =
      { pop := 1, food := 1980, prog := 340, trained := 1 } := by
  decide +kernel

/-- **C3 is inert at 20** (`newCitizen = none` still achieves step 20). -/
theorem c3_optimalAt_baseline :
    OptimalAt (modelQ qNewCitizenNone baselineParams) goal 20 :=
  ⟨AchievableAt.of_legalPath (M := modelQ qNewCitizenNone baselineParams)
      (goal := goal) (N := 20) witness_length c3_witness_legal (by
        change goal (run (modelQ qNewCitizenNone baselineParams) init witness)
        rw [c3_witness_run]; unfold goal; decide +kernel),
   newCitizenNone_noEarlier_20 baselineParams rfl⟩

/-- **C6 is inert at 20** (`productionRounding = trunc10` still achieves 20). -/
theorem c6_optimalAt_baseline :
    OptimalAt (modelQ qTrunc10 baselineParams) goal 20 :=
  ⟨AchievableAt.of_legalPath (M := modelQ qTrunc10 baselineParams)
      (goal := goal) (N := 20) witness_length c6_witness_legal (by
        change goal (run (modelQ qTrunc10 baselineParams) init witness)
        rw [c6_witness_run]; unfold goal; decide +kernel),
   trunc10_noEarlier_20 baselineParams rfl⟩

/-- **C3 is inert at 25** (`newCitizen = none` still achieves step 25). -/
theorem c3_optimalAt_cost110 :
    OptimalAt (modelQ qNewCitizenNone cost110Params) goal 25 :=
  ⟨AchievableAt.of_legalPath (M := modelQ qNewCitizenNone cost110Params)
      (goal := goal) (N := 25) witness110_length c3_witness110_legal (by
        change goal (run (modelQ qNewCitizenNone cost110Params) init witness110)
        rw [c3_witness110_run]; unfold goal; decide +kernel),
   newCitizenNone_noEarlier_25 cost110Params rfl⟩

/-- **C6 is inert at 25** (`productionRounding = trunc10` still achieves 25). -/
theorem c6_optimalAt_cost110 :
    OptimalAt (modelQ qTrunc10 cost110Params) goal 25 :=
  ⟨AchievableAt.of_legalPath (M := modelQ qTrunc10 cost110Params)
      (goal := goal) (N := 25) witness110_length c6_witness110_legal (by
        change goal (run (modelQ qTrunc10 cost110Params) init witness110)
        rw [c6_witness110_run]; unfold goal; decide +kernel),
   trunc10_noEarlier_25 cost110Params rfl⟩

/-- Both pointwise-`q` axes (C3, C6) are inert at both certified endpoints. -/
theorem c3_c6_inert_certified :
    OptimalAt (modelQ qNewCitizenNone baselineParams) goal 20 ∧
    OptimalAt (modelQ qTrunc10 baselineParams) goal 20 ∧
    OptimalAt (modelQ qNewCitizenNone cost110Params) goal 25 ∧
    OptimalAt (modelQ qTrunc10 cost110Params) goal 25 :=
  ⟨c3_optimalAt_baseline, c6_optimalAt_baseline,
   c3_optimalAt_cost110, c6_optimalAt_cost110⟩

/-! ## 8c. Separation facts for the axes that are *not* step-inert

  The certified axes are inert at `OptimalAt`; two of the remaining ones are
  provably **not** step-equivalent, so the remaining obligation really is a
  lower-bound re-derivation and not a definitional coincidence. These lemmas
  are deliberately statements about the baseline pipeline only. -/

/-- The `amenityStock = 1` multiplier block (Content at population 3). -/
def amenityBalance1 (p : Nat) : Int := 1 - (amenityReq p : Int)

def prodMult1 (p : Nat) : Nat :=
  if 1 ≤ amenityBalance1 p then 105 else if 0 ≤ amenityBalance1 p then 100 else 95

def growthMult1 (p : Nat) : Nat :=
  if 1 ≤ amenityBalance1 p then 110 else if 0 ≤ amenityBalance1 p then 100 else 85

/-- **C4 separates at the step level.** At population 3 the baseline is Happy
(`prodMult = 105`) while `amenityStock = 1` is Content (`prodMult = 100`), so
no step-equivalence lemma can hold for C4: the lower bound must be re-derived. -/
theorem c4_multiplier_separates :
    prodMult 3 = 105 ∧ prodMult1 3 = 100 ∧ growthMult 3 = 110 ∧ growthMult1 3 = 100 := by
  decide +kernel

/-- An IDLE action working only `PH` (mask `0b0100 = 4`). -/
def aIdlePH : Action := ⟨⟨4, by decide⟩, none, .idle⟩

/-- **C6 separates at the step level.** At `init`, working `PH` alone gives
`P = 500` and therefore `q = 525`; `trunc10` gives `520`. The action is legal,
so the two semantics really do take different steps. -/
theorem c6_step_separates :
    legal init aIdlePH ∧ qOf init aIdlePH = 525 ∧ qTrunc10 init aIdlePH = 520 :=
  ⟨by rw [legal_iff_guard]; decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The `basketOnGrowth = subtract` basket rule. -/
def foodAfterSubtract (s : State) (a : Action) : Nat :=
  if wouldGrow s a then s.food + growthAmount s a - threshold s.pop
  else s.food + growthAmount s a

/-- **C5 separates at the step level.** On the witness's growth step the
baseline empties the basket (`zero`) while `subtract` would keep `40`. -/
theorem c5_step_separates :
    foodAfter { pop := 1, food := 1320, prog := 0, trained := 0 } (aIdle maskGH none) = 0 ∧
    foodAfterSubtract { pop := 1, food := 1320, prog := 0, trained := 0 }
      (aIdle maskGH none) = 40 :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## 9. Axiom audit

  Run:
  `scripts/lean-env lake env lean Civ6Verify/Robustness/Candidates.lean`.
  Expected: only the ordinary core axioms `propext` and `Quot.sound`; no
  `sorryAx`, no custom axiom, no `native_decide`, no `Classical.choice`. -/

#print axioms stepT_threshold_eq
#print axioms thresholdT3Floor_eq_threshold_of_ne
#print axioms wg_floor_eq_wg
#print axioms stepT_floor_eq_step
#print axioms inv_of_reachable_floor
#print axioms floor_noEarlier_20
#print axioms floor_noEarlier_25
#print axioms floor_witness_legal
#print axioms floor_witness_run
#print axioms floor_optimalAt_baseline
#print axioms floor_optimalAt_cost110
#print axioms c7_inert_certified
#print axioms qOf_dom
#print axioms stepQ_dom
#print axioms coupled_exists
#print axioms modelQ_coupled_noEarlier_20
#print axioms modelQ_coupled_noEarlier_25
#print axioms newCitizenNone_noEarlier_20
#print axioms trunc10_noEarlier_20
#print axioms newCitizenNone_noEarlier_25
#print axioms trunc10_noEarlier_25
#print axioms c3_optimalAt_baseline
#print axioms c6_optimalAt_baseline
#print axioms c3_optimalAt_cost110
#print axioms c6_optimalAt_cost110
#print axioms c3_c6_inert_certified
#print axioms c4_multiplier_separates
#print axioms c6_step_separates
#print axioms c5_step_separates

end Civ6Verify.Robustness.Candidates
