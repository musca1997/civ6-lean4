/-
  Civ6Verify/Scenarios/UrbanPlanning.lean

  **Conditional policy-variant breakthrough for the MVP model.**

  This module adds exactly one modelling assumption on top of
  `Civ6Verify.Model.Mvp` (the conditional MVP v2.1 baseline `M_MVP(θ*, σ)`):

    [POLICY-ASSUME] the Urban Planning policy is in effect from `t = 0` and
                    contributes **+1 base city production** -- `+100` in the
                    1/100 fixed-point units used by `M_MVP` -- so that
                    `baseProd = 300 + workProd` becomes `400 + workProd`
                    *before* the Happy production multiplier is applied.

  What is claimed (all kernel-checked; no `sorry`, no `native_decide`, no
  custom axiom, no Mathlib):

  * a family `bonusStep bonus` of step functions that differs from
    `Mvp.step` only in the additive production term, together with the proof
    `bonusStep_zero : bonusStep 0 p s a = step p s a`. This is the semantic
    cross-check that the variant introduces **no other** change;
  * a `Reachability.Model` instance `policyModel p` whose legality predicate is
    *literally* `Mvp.legalGuard` (so the settler pre-turn-population rule, the
    starvation guard, IDLE/no-extra, worked-tile capacity and the extra-tile
    rule are reused verbatim) and whose legal-action enumeration is sound and
    complete (`policy_mem_legalActions`);
  * a legal witness at `18` steps for cost `80` and at `22` steps for cost
    `110`, each replaying `GH × 7 IDLE` then `(GH+PH) × k SETTLER`;
  * the strict breakthrough `urbanPlanning_breakthrough`:
    the baseline **cannot** reach the goal at step `18` -- inherited from
    `MvpOptimality.noEarlier_20` -- while the policy variant **can**;
    analogously at `22`/`25` for cost `110`.

  What is *not* claimed:
  * this is **not** a Civilization VI statement: `[V] = 0`, no build is pinned
    and no game fixture was run;
  * the unlock cost, the civics/culture tree and the policy-slot opportunity
    cost are **not** modelled -- Urban Planning is a conditional assumption, not
    a free unlock;
  * no optimality of `18`/`22` for the policy variant is proved; only
    achievability is proved, and it is paired with the *baseline* lower bound;
  * no full-game comparison and no claim about the other θ axes (only the cost
    axis is instantiated at `80`/`110`).

  Trust boundary: no model, bridge, arithmetic, root or search file is edited;
  this module imports `Civ6Verify.Model.Mvp` and
  `Civ6Verify.Bounds.MvpOptimality` read-only.
-/

import Civ6Verify.Model.Mvp
import Civ6Verify.Bounds.MvpOptimality

namespace Civ6Verify.Scenarios.UrbanPlanning

open Civ6Verify.Reachability
open Civ6Verify.Model.Mvp

/-! ## 1. The one new assumption: +1 base city production -/

/-- The policy bonus in 1/100 units: `+1` base city production. -/
def policyBonus : Nat := 100

/-- Production with a uniform additive base-production bonus. `bonus = 0` is
the baseline. The bonus is added to `production` (which itself is
`baseProd + growth extra`) and is therefore inside the Happy/non-food
multiplier applied by `bonusQOf`. -/
def bonusProduction (bonus : Nat) (s : State) (a : Action) : Nat :=
  production s a + bonus

/-- Modified production `q = (P + bonus) · prodMult(popAfter) / 100`, i.e. the
bonus is applied **before** the multiplier. -/
def bonusQOf (bonus : Nat) (s : State) (a : Action) : Nat :=
  bonusProduction bonus s a * prodMult (popAfter s a) / 100

/-- Settler credit with the policy production. -/
def bonusProgAfter (bonus : Nat) (s : State) (a : Action) : Nat :=
  s.prog + credit a (bonusQOf bonus s a)

/-- Completion test with the policy production. -/
def bonusCompletes (bonus : Nat) (p : Params) (s : State) (a : Action) : Prop :=
  a.build = Build.settler ∧ bonusProgAfter bonus s a ≥ p.cost

instance (bonus : Nat) (p : Params) (s : State) (a : Action) :
    Decidable (bonusCompletes bonus p s a) := by
  unfold bonusCompletes
  infer_instance

/-- One settlement step with a uniform base-production bonus. Identical to
`Mvp.step` in the growth, food, credit and legality pipelines; only the
production term used for `q` is shifted. -/
def bonusStep (bonus : Nat) (p : Params) (s : State) (a : Action) : State :=
  if bonusCompletes bonus p s a then
    { pop := popAfter s a - 1, food := foodAfter s a,
      prog := bonusProgAfter bonus s a - p.cost, trained := s.trained + 1 }
  else
    { pop := popAfter s a, food := foodAfter s a,
      prog := bonusProgAfter bonus s a, trained := s.trained }

/-! ## 2. Semantic cross-check: the family collapses to the baseline at `0` -/

theorem bonusProduction_eq (bonus : Nat) (s : State) (a : Action) :
    bonusProduction bonus s a = production s a + bonus := rfl

theorem bonusQOf_eq (bonus : Nat) (s : State) (a : Action) :
    bonusQOf bonus s a = (production s a + bonus) * prodMult (popAfter s a) / 100 := rfl

theorem bonusProgAfter_zero (s : State) (a : Action) :
    bonusProgAfter 0 s a = progAfter s a := by
  simp [bonusProgAfter, progAfter, bonusQOf, qOf, bonusProduction]

theorem bonusCompletes_zero_iff (p : Params) (s : State) (a : Action) :
    bonusCompletes 0 p s a ↔ completes p s a := by
  unfold bonusCompletes completes
  rw [bonusProgAfter_zero]

/-- **No hidden semantic change.** With bonus `0` the family is the baseline
`Mvp.step`, definitionally after the documented unfoldings. -/
theorem bonusStep_zero (p : Params) (s : State) (a : Action) :
    bonusStep 0 p s a = step p s a := by
  unfold bonusStep step
  by_cases h : completes p s a
  · rw [if_pos ((bonusCompletes_zero_iff p s a).mpr h), if_pos h, bonusProgAfter_zero]
  · rw [if_neg (fun hc => h ((bonusCompletes_zero_iff p s a).mp hc)), if_neg h,
        bonusProgAfter_zero]

/-- The policy variant is the family instance at `policyBonus = 100`. -/
theorem policy_bonus_is_hundred : policyBonus = 100 := rfl

/-- The policy `q` applies the `+100` before the multiplier. -/
theorem policyQOf_eq (s : State) (a : Action) :
    bonusQOf policyBonus s a = (production s a + 100) * prodMult (popAfter s a) / 100 := rfl

/-- The policy non-food multiplier is the baseline one: growth must not change. -/
theorem policy_growth_reused (s : State) (a : Action) :
    growthAmount s a = growthAmount s a ∧ wouldGrow s a = wouldGrow s a :=
  ⟨rfl, rfl⟩

/-! ## 3. The policy model: same legality, sound and complete enumeration

  `policyModel p` keeps `legalGuard` unchanged. `legalActionsFor p` is the
  baseline enumeration; because the guard does not mention the cost, the same
  list is complete for every parameter, and this is proved rather than assumed. -/

/-- The Option-valued normative step for the variant. -/
def policyStep? (p : Params) (s : State) (a : Action) : Option State :=
  if legalGuard s a then some (bonusStep policyBonus p s a) else none

/-- `policyStep?` is `some` exactly on the unchanged legality guard. -/
theorem policyStep?_isSome (p : Params) (s : State) (a : Action) :
    (policyStep? p s a).isSome = true ↔ legalGuard s a := by
  unfold policyStep?
  by_cases h : legalGuard s a <;> simp [h]

/-- The policy model for a cost parameter. Legality is the baseline guard and
the enumeration is the same `legalActionsFor`, so soundness/completeness are
inherited from `Mvp.mem_legalActionsFor`. -/
def policyModel (p : Params) : Model State Action where
  init := init
  step := bonusStep policyBonus p
  legal := fun s a => legalGuard s a
  legalDec := fun s a => inferInstance
  legalActions := legalActionsFor p
  legalActions_sound := by
    intro s a h
    exact (mem_legalActionsFor p s a).mp h
  legalActions_complete := by
    intro s a h
    exact (mem_legalActionsFor p s a).mpr h

/-- The policy model's legality is *literally* the baseline guard. -/
theorem policyModel_legal_iff_guard (p : Params) (s : State) (a : Action) :
    (policyModel p).legal s a ↔ legalGuard s a :=
  Iff.rfl

/-- The policy model's legality is the baseline `legal`. -/
theorem policyModel_legal_iff (p : Params) (s : State) (a : Action) :
    (policyModel p).legal s a ↔ legal s a :=
  (legal_iff_guard s a).symm

/-- **Completeness and soundness of the variant enumeration.** -/
theorem policy_mem_legalActions (p : Params) (s : State) (a : Action) :
    a ∈ (policyModel p).legalActions s ↔ (policyModel p).legal s a :=
  mem_legalActionsFor p s a

/-- Legality is cost-independent, so the variant and the baseline accept
*exactly the same* legal actions (the enumeration lists differ only in the
proof-irrelevant filter predicate). -/
theorem policy_enumerates_same_actions (p : Params) (s : State) (a : Action) :
    a ∈ (policyModel p).legalActions s ↔ a ∈ legalActions s := by
  rw [policy_mem_legalActions, mem_legalActions]
  exact policyModel_legal_iff p s a

/-- The bonus does not legalise a pre-turn Settler (the A8 rule is reused). -/
theorem policy_settler_impossible_at_pop1 (p : Params) (a : Action)
    (h : (policyModel p).legal init a) : a.build ≠ Build.settler := by
  intro hb
  have hl : legal init a := (legal_iff_guard init a).mpr h
  have hp := legal_settler_pop hl hb
  simp [init] at hp

/-! ## 4. The witness: `GH × 7 IDLE` then `(GH+PH) × k SETTLER` -/

/-- Policy witness for cost `80`: 7 growth steps then 11 settler steps. The
settler steps yield `q = 735`, so `11 · 735 = 8085 ≥ 8000`. -/
def policyWitness : List Action :=
  List.replicate 7 (aIdle maskGH none) ++ List.replicate 11 (aSettler maskGHPH)

/-- Policy witness for cost `110`: 7 growth steps then 15 settler steps;
`15 · 735 = 11025 ≥ 11000`. -/
def policyWitness110 : List Action :=
  List.replicate 7 (aIdle maskGH none) ++ List.replicate 15 (aSettler maskGHPH)

/-- Computable legality check for the variant. -/
def policyLegalPathB (p : Params) : State → List Action → Bool
  | _, [] => true
  | s, a :: rest =>
      decide ((policyStep? p s a).isSome) &&
        policyLegalPathB p (bonusStep policyBonus p s a) rest

/-- A successful boolean legality run yields a `LegalPath` for the variant. -/
theorem policyLegalPathB_sound (p : Params) :
    ∀ (s : State) (as : List Action), policyLegalPathB p s as = true →
      LegalPath (policyModel p) s as
  | s, [], _ => LegalPath.nil s
  | s, a :: rest, h => by
      rw [policyLegalPathB, Bool.and_eq_true] at h
      exact LegalPath.cons ((policyStep?_isSome p s a).mp (of_decide_eq_true h.1))
        (policyLegalPathB_sound p (bonusStep policyBonus p s a) rest h.2)

theorem policyWitness_length : policyWitness.length = 18 := by decide +kernel

theorem policyWitness110_length : policyWitness110.length = 22 := by decide +kernel

theorem policyWitness_legal :
    LegalPath (policyModel baselineParams) init policyWitness :=
  policyLegalPathB_sound baselineParams init policyWitness (by decide +kernel)

theorem policyWitness110_legal :
    LegalPath (policyModel cost110Params) init policyWitness110 :=
  policyLegalPathB_sound cost110Params init policyWitness110 (by decide +kernel)

/-- Final state of the cost-80 policy witness: `11 · 735 − 8000 = 85`. -/
theorem policyWitness_run :
    run (policyModel baselineParams) init policyWitness =
      { pop := 1, food := 1210, prog := 85, trained := 1 } := by
  decide +kernel

/-- Final state of the cost-110 policy witness: `15 · 735 − 11000 = 25`. -/
theorem policyWitness110_run :
    run (policyModel cost110Params) init policyWitness110 =
      { pop := 1, food := 1650, prog := 25, trained := 1 } := by
  decide +kernel

theorem policyWitness_achieves :
    goal (run (policyModel baselineParams) init policyWitness) := by
  rw [policyWitness_run]
  unfold goal
  decide +kernel

theorem policyWitness110_achieves :
    goal (run (policyModel cost110Params) init policyWitness110) := by
  rw [policyWitness110_run]
  unfold goal
  decide +kernel

/-- Achievability at step 18 for the cost-80 policy variant (`< 20`). -/
theorem policy_achievable_18 : AchievableAt (policyModel baselineParams) goal 18 :=
  AchievableAt.of_legalPath (M := policyModel baselineParams) (goal := goal) (N := 18)
    (as := policyWitness) policyWitness_length policyWitness_legal policyWitness_achieves

/-- Achievability at step 22 for the cost-110 policy variant (`< 25`). -/
theorem policy_achievable_22 : AchievableAt (policyModel cost110Params) goal 22 :=
  AchievableAt.of_legalPath (M := policyModel cost110Params) (goal := goal) (N := 22)
    (as := policyWitness110) policyWitness110_length policyWitness110_legal
    policyWitness110_achieves

/-! ## 5. Banking and incrementality sanity lemmas -/

/-- IDLE credits no settler progress in the variant (no banking). -/
theorem bonusStep_idle_prog (bonus : Nat) (p : Params) (s : State) (a : Action)
    (h : a.build = Build.idle) : (bonusStep bonus p s a).prog = s.prog := by
  unfold bonusStep
  by_cases hc : bonusCompletes bonus p s a
  · unfold bonusCompletes at hc
    rw [h] at hc
    exact absurd hc.1 (by simp)
  · rw [if_neg hc]
    simp [bonusProgAfter, credit, h]

/-- IDLE never completes and never changes the trained-settler history. -/
theorem bonusStep_idle_trained (bonus : Nat) (p : Params) (s : State) (a : Action)
    (h : a.build = Build.idle) : (bonusStep bonus p s a).trained = s.trained := by
  unfold bonusStep
  by_cases hc : bonusCompletes bonus p s a
  · unfold bonusCompletes at hc
    rw [h] at hc
    exact absurd hc.1 (by simp)
  · rw [if_neg hc]

/-- `trained` is monotone in the variant, so the goal is terminal. -/
theorem bonusStep_trained_ge (bonus : Nat) (p : Params) (s : State) (a : Action) :
    s.trained ≤ (bonusStep bonus p s a).trained := by
  unfold bonusStep
  split <;> simp

theorem policy_goal_step {p : Params} {s : State} {a : Action} (h : goal s) :
    goal (bonusStep policyBonus p s a) :=
  Nat.le_trans h (bonusStep_trained_ge policyBonus p s a)

/-! ## 6. Concrete numeric cross-checks -/

/-- At pop 2 working `GH+PH`, the baseline credits `q = 600 · 105 / 100 = 630`. -/
theorem baseline_settler_q :
    qOf { pop := 2, food := 0, prog := 0, trained := 0 } (aSettler maskGHPH) = 630 := by
  decide +kernel

/-- The policy credits `q = 700 · 105 / 100 = 735` on the same step: the `+100`
base production is applied before the Happy multiplier. -/
theorem policy_settler_q :
    bonusQOf policyBonus { pop := 2, food := 0, prog := 0, trained := 0 }
      (aSettler maskGHPH) = 735 := by
  decide +kernel

/-- Growth is untouched: the seventh baseline step still generates `e = 220`. -/
theorem policy_growth_amount :
    growthAmount { pop := 1, food := 1320, prog := 0, trained := 0 } (aIdle maskGH none) = 220 := by
  decide +kernel

/-- The settler prerequisite is read on the pre-turn population (reused A8). -/
theorem policy_witness_seventh_grows :
    wouldGrow { pop := 1, food := 1320, prog := 0, trained := 0 } (aIdle maskGH none) = true := by
  decide +kernel

/-- The first witness action is in the variant's *computed* enumeration. -/
theorem policy_witness_first_mem :
    aIdle maskGH none ∈ (policyModel baselineParams).legalActions init := by
  rw [policy_mem_legalActions]
  unfold policyModel
  decide +kernel

/-! ## 7. The breakthrough: baseline cannot at 18, policy can -/

/-- Baseline (no policy) cannot train a Settler at step 18. This is the
baseline lower bound `noEarlier_20` restricted to `18 < 20`; it is *not*
re-proved here. -/
theorem baseline_not_achievable_18 :
    ¬ AchievableAt (model baselineParams) goal 18 := by
  rintro ⟨s, hreach, hgoal⟩
  exact Civ6Verify.Bounds.MvpOptimality.noEarlier_20 baselineParams rfl 18
    (by decide) s hreach hgoal

/-- Baseline cost-110 cannot train a Settler at step 22 (from `noEarlier_25`). -/
theorem baseline_not_achievable_22 :
    ¬ AchievableAt (model cost110Params) goal 22 := by
  rintro ⟨s, hreach, hgoal⟩
  exact Civ6Verify.Bounds.MvpOptimality.noEarlier_25 cost110Params rfl 22
    (by decide) s hreach hgoal

/-- **Strict breakthrough (cost 80).** In the conditional model, the baseline
cannot achieve the goal at step 18 while the Urban Planning variant can. The
conjunction is a strict comparison of *two models*; neither number is a
Civilization VI claim. -/
theorem urbanPlanning_breakthrough :
    ¬ AchievableAt (model baselineParams) goal 18 ∧
      AchievableAt (policyModel baselineParams) goal 18 :=
  ⟨baseline_not_achievable_18, policy_achievable_18⟩

/-- **Strict breakthrough (cost 110).** Baseline cannot at 22; policy can. -/
theorem urbanPlanning_breakthrough_cost110 :
    ¬ AchievableAt (model cost110Params) goal 22 ∧
      AchievableAt (policyModel cost110Params) goal 22 :=
  ⟨baseline_not_achievable_22, policy_achievable_22⟩

/-- The policy variant is strictly faster than the baseline in the model. -/
theorem policy_strictly_faster :
    (¬ AchievableAt (model baselineParams) goal 18) ∧
      AchievableAt (policyModel baselineParams) goal 18 ∧
      ¬ AchievableAt (model cost110Params) goal 22 ∧
      AchievableAt (policyModel cost110Params) goal 22 :=
  ⟨baseline_not_achievable_18, policy_achievable_18,
    baseline_not_achievable_22, policy_achievable_22⟩

/-! ## 8. Axiom audit

  Expected: only the ordinary core axioms `propext` and `Quot.sound`; no
  `sorryAx`, no `Classical.choice`, no `Lean.ofReduceBool`, no custom axiom. -/
#print axioms bonusStep_zero
#print axioms bonusProgAfter_zero
#print axioms bonusCompletes_zero_iff
#print axioms policyStep?_isSome
#print axioms policyModel_legal_iff_guard
#print axioms policy_mem_legalActions
#print axioms policy_enumerates_same_actions
#print axioms policy_settler_impossible_at_pop1
#print axioms policyLegalPathB_sound
#print axioms bonusStep_idle_prog
#print axioms bonusStep_idle_trained
#print axioms bonusStep_trained_ge
#print axioms policyWitness_legal
#print axioms policyWitness_run
#print axioms policyWitness110_legal
#print axioms policyWitness110_run
#print axioms policy_achievable_18
#print axioms policy_achievable_22
#print axioms baseline_settler_q
#print axioms policy_settler_q
#print axioms policy_growth_amount
#print axioms baseline_not_achievable_18
#print axioms baseline_not_achievable_22
#print axioms urbanPlanning_breakthrough
#print axioms urbanPlanning_breakthrough_cost110
#print axioms policy_strictly_faster

end Civ6Verify.Scenarios.UrbanPlanning
