/-
  Civ6Verify/Bounds/MvpOptimality.lean

  **Model-side lower bound for the conditional MVP model** (`mvp/LOWER-BOUND.md`
  §4, bridge obligations B-1..B-6), integrating the pure arithmetic core
  `Civ6Verify.Bounds.MvpArithmetic` with the actual step semantics of
  `Civ6Verify.Model.Mvp`.

  What is proved here (all kernel-checked; no `sorry`, no custom axiom, no
  `native_decide`, no Mathlib):

  * the mask-level yield facts of σ = `sigma-capital-4tiles-v1` for the *model's*
    `Action.work : Fin 16` bitmask (`workFood`, `workProd`, `workCount`), i.e.
    the concrete instances of `MvpArithmetic.Assign`;
  * the per-step caps on every legal model step: `e = growthAmount ≤ 220`,
    `q = qOf ≤ 735`, `q ≤ 630` at pop 2 without growth, and the food/production
    dual `11·q + 21·e ≤ 9240` (LOWER-BOUND §3 Lemma 3 / C1–C4);
  * the food ladder `food + [pop≥2]·1500 + [pop≥3]·2400 + [pop≥4]·3383 ≤ 220·t`
    (LOWER-BOUND §3 Lemma 4, lifted to a state invariant) and the derived
    bounds `pop ≤ 3` for `t ≤ 24`;
  * the progress accounting invariant of LOWER-BOUND §4/§8, carried over
    `Reachable`:
      pop 1: `prog = 0`;
      pop 2: `11·prog ≤ 6930·(t−7)`  and  `11·prog + 21·food ≤ 9240·(t−7)`;
      pop 3: `11·prog ≤ 9240·t − 111615`;
  * the resulting lower bounds **on the actual model**: no Settler can complete
    before step 20 (cost 80) and before step 25 (cost 110), hence
    `OptimalAt (model baselineParams) goal 20` and
    `OptimalAt (model cost110Params) goal 25` when combined with the model's
    own `baseline_achievable` / `cost110_achievable` witnesses.

  Claim discipline. This is a statement about the conditional model
  `M_MVP(θ*, σ)` of `mvp/RULE-CONTRACT.md` v2.1, not about Civilization VI:
  `[V] = 0`, no build is pinned, and every constant is the contract's
  `[C]/[D*]/[A]/[SCENARIO]` value. The lower bound is θ-uniform in the
  arithmetic (`mvp/LOWER-BOUND.md` §4.5); the model side fixes C2–C7 at the
  baseline values because `Params` only parameterises `cost`.

  Relation to `mvp/LOWER-BOUND.md`. The document's case-B accounting sums the
  dual over the pop-2 "middle" steps and charges `Emid ≥ 3680 − 220·n`
  (its equation (F)). The Lean proof here uses an equivalent but stronger
  state-local form: at the pop 2 → 3 growth step the basket satisfies
  `food ≥ 2400 − e ≥ 2180`, which is charged against the pop-2 dual invariant
  `11·prog + 21·food ≤ 9240·(t−7)` directly. This removes the need to track the
  pop-2 arrival index `n` inside the invariant, and it yields the slightly
  sharper endpoints
    `11·prog ≤ 9240·19 − 111615 = 63945` (`prog ≤ 5813`, doc: `5889`),
    `11·prog ≤ 9240·24 − 111615 = 110145` (`prog ≤ 10013`, doc: `10089`).
  Case A is used verbatim through `MvpArithmetic.caseA_19` / `caseA_24`.

  Trust boundary: no model file, no arithmetic file, no root module and no
  lakefile was edited; this module only imports them.
-/

import Civ6Verify.Model.Mvp
import Civ6Verify.Bounds.MvpArithmetic

namespace Civ6Verify.Bounds.MvpOptimality

open Civ6Verify.Reachability
open Civ6Verify.Model.Mvp

/-! ## 1. Mask-level yield facts

  `Action.work : Fin 16` is a bitmask, so `workTiles a` is a duplicate-free
  sublist of the four tiles: one citizen per tile and no duplicates are
  structural. The facts below are the concrete instances of
  `MvpArithmetic.Assign` for this representation. They are proved by kernel
  evaluation over the 16 masks (`decide +kernel`, i.e. kernel reduction of a
  closed decidable proposition; no compiler trust). -/

/-- The mask-canonical action, used to state mask-only facts. -/
def maskAct (w : Fin 16) : Action := ⟨w, none, .idle⟩

/-- Food and production of a legal work set in the contract's point unit
(1 point = 100 in the model's fixed point). -/
def fpts (a : Action) : Nat := workFood a / 100

/-- Production points of a legal work set. -/
def ppts (a : Action) : Nat := workProd a / 100

theorem workFood_dvd (a : Action) : 100 ∣ workFood a := by
  have h : ∀ w : Fin 16, 100 ∣ workFood (maskAct w) := by decide +kernel
  exact h a.work

theorem workProd_dvd (a : Action) : 100 ∣ workProd a := by
  have h : ∀ w : Fin 16, 100 ∣ workProd (maskAct w) := by decide +kernel
  exact h a.work

theorem workFood_eq (a : Action) : workFood a = 100 * fpts a := by
  have h := workFood_dvd a
  unfold fpts
  rw [Nat.mul_comm]
  exact (Nat.div_mul_cancel h).symm

theorem workProd_eq (a : Action) : workProd a = 100 * ppts a := by
  have h := workProd_dvd a
  unfold ppts
  rw [Nat.mul_comm]
  exact (Nat.div_mul_cancel h).symm

/-- Food of a work set, sharp per assigned-citizen count: `2/4/5/6` points.
These are the maxima over subsets of the four tiles of size `≤ k`. -/
theorem workFood_le_one (a : Action) (h : workCount a ≤ 1) : workFood a ≤ 200 := by
  have hm : ∀ w : Fin 16, workCount (maskAct w) ≤ 1 → workFood (maskAct w) ≤ 200 := by
    decide +kernel
  exact hm a.work h

theorem workFood_le_two (a : Action) (h : workCount a ≤ 2) : workFood a ≤ 400 := by
  have hm : ∀ w : Fin 16, workCount (maskAct w) ≤ 2 → workFood (maskAct w) ≤ 400 := by
    decide +kernel
  exact hm a.work h

theorem workFood_le_three (a : Action) (h : workCount a ≤ 3) : workFood a ≤ 500 := by
  have hm : ∀ w : Fin 16, workCount (maskAct w) ≤ 3 → workFood (maskAct w) ≤ 500 := by
    decide +kernel
  exact hm a.work h

theorem workFood_le_four (a : Action) : workFood a ≤ 600 := by
  have hm : ∀ w : Fin 16, workFood (maskAct w) ≤ 600 := by decide +kernel
  exact hm a.work

/-- A worked set never feeds more than `200` per worked citizen. -/
theorem workFood_le_count_mul (a : Action) : workFood a ≤ 200 * workCount a := by
  have hm : ∀ w : Fin 16, workFood (maskAct w) ≤ 200 * workCount (maskAct w) := by
    decide +kernel
  exact hm a.work

/-- Production of a work set, sharp per count: `2/3/4/4` points. -/
theorem workProd_le_one (a : Action) (h : workCount a ≤ 1) : workProd a ≤ 200 := by
  have hm : ∀ w : Fin 16, workCount (maskAct w) ≤ 1 → workProd (maskAct w) ≤ 200 := by
    decide +kernel
  exact hm a.work h

theorem workProd_le_two (a : Action) (h : workCount a ≤ 2) : workProd a ≤ 300 := by
  have hm : ∀ w : Fin 16, workCount (maskAct w) ≤ 2 → workProd (maskAct w) ≤ 300 := by
    decide +kernel
  exact hm a.work h

theorem workProd_le_three (a : Action) (h : workCount a ≤ 3) : workProd a ≤ 400 := by
  have hm : ∀ w : Fin 16, workCount (maskAct w) ≤ 3 → workProd (maskAct w) ≤ 400 := by
    decide +kernel
  exact hm a.work h

theorem workProd_le_four (a : Action) : workProd a ≤ 400 := by
  have hm : ∀ w : Fin 16, workProd (maskAct w) ≤ 400 := by decide +kernel
  exact hm a.work

/-- **Per-assignment budget** `2·food + prod ≤ 4·count + 1` in points
(`MvpArithmetic.Assign.budget`). `GH` is the only tile above the uniform
budget `2·food + prod ≤ 4`. -/
theorem budget_pts (a : Action) : 2 * fpts a + ppts a ≤ 4 * workCount a + 1 := by
  have hm : ∀ w : Fin 16, 2 * fpts (maskAct w) + ppts (maskAct w) ≤
      4 * workCount (maskAct w) + 1 := by decide +kernel
  exact hm a.work

/-- The new citizen's tile is unworked, so `work ∪ {extra}` is still a set of
distinct tiles with total production `≤ 400` points. -/
theorem workProd_add_extra (a : Action) (t : Fin 4)
    (h : a.work.val.testBit t.val = false) : workProd a + tileProd t ≤ 400 := by
  have hm : ∀ (w : Fin 16) (t : Fin 4), (maskAct w).work.val.testBit t.val = false →
      workProd (maskAct w) + tileProd t ≤ 400 := by decide +kernel
  exact hm a.work t h

/-- Any single tile yields at most `200` production. -/
theorem tileProd_le (t : Fin 4) : tileProd t ≤ 200 := by
  have hm : ∀ t : Fin 4, tileProd t ≤ 200 := by decide +kernel
  exact hm t

/-- `baseFood = 100·(2 + food points)`; the centre contributes `200` and the
palace does not feed. -/
theorem baseFood_eq (a : Action) : baseFood a = 100 * (2 + fpts a) := by
  unfold baseFood
  rw [workFood_eq]
  omega

/-- `baseProd = 100·(3 + production points)`: centre `100` + palace `200`. -/
theorem baseProd_eq (a : Action) : baseProd a = 100 * (3 + ppts a) := by
  unfold baseProd
  rw [workProd_eq]
  omega

/-- Exact surplus in points, on legal actions (`200·pop ≤ F`). -/
theorem surplus_eq (s : State) (a : Action) (h : 200 * s.pop ≤ baseFood a) :
    surplus s a = 100 * (2 + fpts a - 2 * s.pop) := by
  unfold surplus
  rw [baseFood_eq] at h
  rw [baseFood_eq]
  have h2 : 2 * s.pop ≤ 2 + fpts a := by omega
  omega

theorem surplus_le_200 (s : State) (a : Action) (h : legal s a) (hpop : 1 ≤ s.pop) :
    surplus s a ≤ 200 := by
  have hw := legal_workCount h
  have hbase : baseFood a = 200 + workFood a := rfl
  have hfc : workFood a ≤ 200 * s.pop :=
    Nat.le_trans (workFood_le_count_mul a) (Nat.mul_le_mul_left 200 hw)
  unfold surplus
  rw [hbase]
  omega

/-! ## 2. Multipliers

  `amenityStock = 2` (baseline θ*), so populations `≤ 4` are Happy:
  growth `110 %`, non-food `105 %`. The caps used in the lower bound only need
  `≤`, which holds in every amenity tier. -/

theorem prodMult_le (p : Nat) : prodMult p ≤ 105 := by
  unfold prodMult amenityBalance amenityReq
  split
  · omega
  · split <;> omega

theorem growthMult_le (p : Nat) : growthMult p ≤ 110 := by
  unfold growthMult amenityBalance amenityReq
  split
  · omega
  · split <;> omega

theorem prodMult_eq_happy {p : Nat} (hp : p ≤ 4) : prodMult p = 105 := by
  unfold prodMult amenityBalance amenityReq
  split
  · rfl
  · omega

theorem growthMult_eq_happy {p : Nat} (hp : p ≤ 3) : growthMult p = 110 := by
  unfold growthMult amenityBalance amenityReq
  split
  · rfl
  · omega

/-! ## 3. Per-step caps (bridge B-3)

  These are the model-side instances of `MvpArithmetic.q_le_735`, `q_le_630`,
  `e_le_220` and `dual_pop2/3`. -/

/-- **`e ≤ 220`** on every legal step: the surplus is at most `200` points and
the growth multiplier at most `110`. -/
theorem growthAmount_le_220 (s : State) (a : Action) (h : legal s a) (hpop : 1 ≤ s.pop) :
    growthAmount s a ≤ 220 := by
  unfold growthAmount
  have hs := surplus_le_200 s a h hpop
  have hm := growthMult_le s.pop
  have h1 : surplus s a * growthMult s.pop ≤ 200 * 110 := Nat.mul_le_mul hs hm
  have h2 : surplus s a * growthMult s.pop / 100 ≤ (200 * 110) / 100 :=
    Nat.div_le_div_right h1
  have h3 : (200 * 110) / 100 = 220 := by decide +kernel
  omega

/-- The production used by the model step is at most `700` (1/100 units):
`300` base + at most `400` from the worked tiles, and the extra citizen only
adds the production of an *unworked* tile. -/
theorem production_le_700 (s : State) (a : Action) (h : legal s a) :
    production s a ≤ 700 := by
  unfold production
  by_cases hg : wouldGrow s a = true
  · rw [if_pos hg]
    have hb : baseProd a = 300 + workProd a := rfl
    cases he : a.extra with
    | none =>
        simp only [extraGain, he]
        have := workProd_le_four a
        omega
    | some t =>
        have hbits : a.work.val.testBit t.val = false := legal_extra_not_work h he
        have hc : workProd a + tileProd t ≤ 400 := workProd_add_extra a t hbits
        have ht := tileProd_le t
        simp only [extraGain, he]
        omega
  · rw [if_neg hg]
    have hb : baseProd a = 300 + workProd a := rfl
    have := workProd_le_four a
    omega

/-- **`q ≤ 735`** on every legal step, including a growth step with the extra
citizen (`MvpArithmetic.q_le_735`). -/
theorem qOf_le_735 (s : State) (a : Action) (h : legal s a) : qOf s a ≤ 735 := by
  unfold qOf
  have hp := production_le_700 s a h
  have hm := prodMult_le (popAfter s a)
  have h1 : production s a * prodMult (popAfter s a) ≤ 700 * 105 := Nat.mul_le_mul hp hm
  have h2 : production s a * prodMult (popAfter s a) / 100 ≤ (700 * 105) / 100 :=
    Nat.div_le_div_right h1
  have h3 : (700 * 105) / 100 = 735 := by decide +kernel
  omega

/-- **`q ≤ 630`** at pop 2 without a growth event (`MvpArithmetic.q_le_630`):
two tiles produce at most `300` points. -/
theorem qOf_le_630 (s : State) (a : Action) (h : legal s a) (hpop : s.pop = 2)
    (hg : wouldGrow s a = false) : qOf s a ≤ 630 := by
  unfold qOf production
  rw [if_neg (by simp [hg])]
  simp only [Nat.add_zero]
  have hw := legal_workCount h
  have hb : baseProd a = 300 + workProd a := rfl
  have hp : baseProd a ≤ 600 := by
    have := workProd_le_two a (by omega)
    omega
  have hm := prodMult_le (popAfter s a)
  have h1 : baseProd a * prodMult (popAfter s a) ≤ 600 * 105 := Nat.mul_le_mul hp hm
  have h2 : baseProd a * prodMult (popAfter s a) / 100 ≤ (600 * 105) / 100 :=
    Nat.div_le_div_right h1
  have h3 : (600 * 105) / 100 = 630 := by decide +kernel
  omega

/-! ## 4. The food ladder and the potential

  `floorI p` is the food that must already have been generated to reach
  population `p`: `T(1) = 1500`, `T(1)+T(2) = 3900`, `T(1)+T(2)+T(3) = 7283`.
  Because the basket is emptied on growth, generated food always covers the
  consumed thresholds plus the current basket, which gives LOWER-BOUND §3
  Lemma 4 as an inductive invariant. -/

/-- Food committed to growth at population `p`, as a function of `p`. -/
def floorI (p : Nat) : Int :=
  1500 * (if 2 ≤ p then 1 else 0) + 2400 * (if 3 ≤ p then 1 else 0) +
    3383 * (if 4 ≤ p then 1 else 0)

theorem floorI_ge_four {p : Nat} (h : 4 ≤ p) : floorI p = 7283 := by
  have h2 : 2 ≤ p := by omega
  have h3 : 3 ≤ p := by omega
  unfold floorI
  rw [if_pos h2, if_pos h3, if_pos h]
  decide +kernel

theorem floorI_mono : ∀ p q : Nat, p ≤ q → floorI p ≤ floorI q := by
  intro p q h
  unfold floorI
  have h2 : (if 2 ≤ p then (1 : Int) else 0) ≤ (if 2 ≤ q then 1 else 0) := by
    by_cases hp : 2 ≤ p
    · rw [if_pos hp, if_pos (Nat.le_trans hp h)]; omega
    · rw [if_neg hp]; split <;> omega
  have h3 : (if 3 ≤ p then (1 : Int) else 0) ≤ (if 3 ≤ q then 1 else 0) := by
    by_cases hp : 3 ≤ p
    · rw [if_pos hp, if_pos (Nat.le_trans hp h)]; omega
    · rw [if_neg hp]; split <;> omega
  have h4 : (if 4 ≤ p then (1 : Int) else 0) ≤ (if 4 ≤ q then 1 else 0) := by
    by_cases hp : 4 ≤ p
    · rw [if_pos hp, if_pos (Nat.le_trans hp h)]; omega
    · rw [if_neg hp]; split <;> omega
  omega

/-- One growth step consumes at most the next threshold: the potential
increment is dominated by the generated food. -/
theorem floorI_succ : ∀ p : Nat, floorI (p + 1) ≤ floorI p + (threshold p : Int)
  | 0 => by decide +kernel
  | 1 => by decide +kernel
  | 2 => by decide +kernel
  | 3 => by decide +kernel
  | n + 4 => by
      have h1 : 2 ≤ n + 4 := by omega
      have h2 : 3 ≤ n + 4 := by omega
      have h3 : 4 ≤ n + 4 := by omega
      have h4 : 2 ≤ n + 5 := by omega
      have h5 : 3 ≤ n + 5 := by omega
      have h6 : 4 ≤ n + 5 := by omega
      unfold floorI
      rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6]
      have hthr : (0 : Int) ≤ (threshold (n + 4) : Int) := Int.ofNat_zero_le _
      omega

/-- Thresholds used by the ladder. -/
theorem threshold_one : threshold 1 = 1500 := rfl
theorem threshold_two : threshold 2 = 2400 := rfl
theorem threshold_three : threshold 3 = 3383 := rfl

/-! ## 5. Step projections and progress accounting (bridge B-1/B-5) -/

theorem step_food (p : Params) (s : State) (a : Action) :
    (step p s a).food = foodAfter s a := by
  unfold step
  split <;> rfl

theorem step_pop (p : Params) (s : State) (a : Action) :
    (step p s a).pop = popAfter s a ∨ (step p s a).pop = popAfter s a - 1 := by
  unfold step
  split <;> simp

/-- `trained` increases exactly on the completion branch. -/
theorem step_trained (p : Params) (s : State) (a : Action) :
    (step p s a).trained = s.trained ∨ (step p s a).trained = s.trained + 1 := by
  unfold step
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Progress accounting: `prog` grows by the credited `q`, minus the cost on a
completion (`Mvp.step_prog`, reproduced here with the exact branch shape). -/
theorem step_prog' (p : Params) (s : State) (a : Action) :
    (step p s a).prog = progAfter s a ∨
      (step p s a).prog + p.cost = progAfter s a := by
  unfold step
  split
  · rename_i hc
    right
    unfold completes at hc
    exact Nat.sub_add_cancel hc.2
  · left
    rfl

/-- A step whose cumulative credit stays below the cost cannot complete. -/
theorem not_completes_of_progAfter_lt (p : Params) (s : State) (a : Action)
    (h : s.prog + credit a (qOf s a) < p.cost) : ¬ completes p s a := by
  intro hc
  have h2 : progAfter s a ≥ p.cost := hc.2
  have h3 : progAfter s a = s.prog + credit a (qOf s a) := rfl
  omega

theorem credit_le (a : Action) (q : Nat) : credit a q ≤ q := by
  unfold credit
  split <;> omega

/-- On a legal step with pre-turn population below 2 the credit is zero
(`Mvp.credit_zero_of_prePop_lt_two`, re-exported for the model instance). -/
theorem credit_zero_of_pop_lt_two (s : State) (a : Action) (h : legal s a)
    (hpop : s.pop < 2) : credit a (qOf s a) = 0 :=
  credit_zero_of_prePop_lt_two s a h hpop

/-! ## 6. The dual inequalities (LOWER-BOUND §3 Lemma 3)

  At pre-turn population `p` with `count ≤ p` and surplus `d ≥ 0`, a
  non-growth step satisfies `11·q + 21·e ≤ 9240`: the exact Happy-tier forms
  `q = (3 + prod)·105`, `e = (2 + food − 2p)·110` and the budget
  `2·food + prod ≤ 4·count + 1` give
  `11q + 21e = 1155·(2·food + prod + 7 − 4p) ≤ 9240`. -/

theorem qOf_eq_dual (s : State) (a : Action) (h : legal s a) (hpop4 : s.pop ≤ 3)
    (hg : wouldGrow s a = false) : qOf s a = (3 + ppts a) * 105 := by
  have hpm : popAfter s a ≤ 4 := by
    rw [popAfter_eq s a hg]; omega
  have h := prodMult_eq_happy hpm
  unfold qOf production
  rw [if_neg (by simp [hg]), baseProd_eq, h]
  simp only [Nat.add_zero]
  rw [Nat.mul_assoc]
  exact Nat.mul_div_right _ (by decide)

theorem growthAmount_eq_dual (s : State) (a : Action) (h : legal s a) (hpop4 : s.pop ≤ 3)
    (hg : wouldGrow s a = false) :
    growthAmount s a = (2 + fpts a - 2 * s.pop) * 110 := by
  have hgm : growthMult s.pop = 110 := growthMult_eq_happy (by omega)
  unfold growthAmount
  rw [surplus_eq s a (legal_surplus h), hgm]
  rw [Nat.mul_assoc]
  exact Nat.mul_div_right _ (by decide)

/-- **Dual inequality.** For a non-growth legal step at population `p ≤ 3`
with a non-negative surplus, `11·q + 21·e ≤ 9240`. This is the model-side
instance of `MvpArithmetic.Assign.dual_pop2` and `dual_pop3` for both
`p = 2` and `p = 3`. -/
theorem dual_of_noGrowth (s : State) (a : Action) (h : legal s a) (hpop1 : 1 ≤ s.pop)
    (hpop3 : s.pop ≤ 3) (hg : wouldGrow s a = false) :
    11 * qOf s a + 21 * growthAmount s a ≤ 9240 := by
  have hw := legal_workCount h
  have hq := qOf_eq_dual s a h hpop3 hg
  have he := growthAmount_eq_dual s a h hpop3 hg
  have hb := budget_pts a
  have hsur : 2 * s.pop ≤ 2 + fpts a := by
    have := legal_surplus h
    rw [baseFood_eq] at this
    omega
  rw [hq, he]
  omega

/-- Non-growth steps also satisfy the same dual when the credit is replaced by
its upper bound `q` (the credit is `q` on SETTLER steps and `0` on IDLE). -/
theorem dual_credit (s : State) (a : Action) (h : legal s a) (hpop1 : 1 ≤ s.pop)
    (hpop3 : s.pop ≤ 3) (hg : wouldGrow s a = false) :
    11 * credit a (qOf s a) + 21 * growthAmount s a ≤ 9240 := by
  have h1 := dual_of_noGrowth s a h hpop1 hpop3 hg
  have h2 := credit_le a (qOf s a)
  omega

/-! ## 7. The invariant (LOWER-BOUND §4 and §8)

`Inv t s` is a disjunctive invariant over the exact-step relation, stated on
the model state. Since `Reachable` composes legal actions only, every state in
the induction satisfies the legality guard, which is where the per-step caps
come from. -/

/-- Quantitative invariant for prefixes of length `t`. -/
def Inv (t : Nat) (s : State) : Prop :=
  -- food ladder: generated food covers the committed thresholds and the basket
  (s.food : Int) + floorI s.pop ≤ 220 * (t : Int) ∧
  1 ≤ s.pop ∧
  s.trained = 0 ∧
  -- case A: no credited step before population 2, and `q ≤ 630` afterwards
  (s.pop = 1 → (s.prog : Int) = 0) ∧
  (s.pop = 2 → 11 * (s.prog : Int) ≤ 6930 * ((t : Int) - 7) ∧
                11 * (s.prog : Int) + 21 * (s.food : Int) ≤ 9240 * ((t : Int) - 7)) ∧
  -- case B: at population 3 only the high-value cap `q ≤ 735` and the ladder
  (s.pop = 3 → 11 * (s.prog : Int) ≤ 9240 * (t : Int) - 111615)

/-- The ladder alone bounds the population by 3 for `t ≤ 23` (hence `t+1 ≤ 24`):
reaching population 4 requires `1500 + 2400 + 3383 = 7283` generated food, but
`220·23 = 5060`. -/
theorem pop_le_three_of_ladder {t : Nat} {s : State}
    (h : (s.food : Int) + floorI s.pop ≤ 220 * (t : Int)) (ht : t ≤ 23) : s.pop ≤ 3 := by
  rcases Nat.lt_or_ge s.pop 4 with hlt | hge
  · omega
  · exfalso
    have hf : floorI s.pop = 7283 := floorI_ge_four hge
    have hcast : (220 : Int) * (t : Int) ≤ 220 * 23 := by
      have : (t : Int) ≤ 23 := by exact_mod_cast ht
      omega
    have hfood : (0 : Int) ≤ (s.food : Int) := by exact Int.ofNat_zero_le _
    omega

/-- `Inv` holds at the founding snapshot. -/
theorem inv_init : Inv 0 init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- `wouldGrow` is exactly the threshold test of step 4 of the step semantics. -/
theorem wouldGrow_iff (s : State) (a : Action) :
    wouldGrow s a = true ↔ s.food + growthAmount s a ≥ threshold s.pop := by
  unfold wouldGrow
  simp

/-! ## 8. The inductive step

This is the model-side content of bridge obligations B-1..B-6: from the
invariant at step `n`, one legal model step either completes a Settler (shown
impossible because the credited progress stays below `cost`) or preserves the
invariant at `n+1`. -/

theorem inv_step (p : Params) (C : Nat) (hC : 0 < C) (hcost : p.cost = C)
    {n : Nat} {s0 : State} {a : Action}
    (hinv : Inv n s0) (hleg : legal s0 a) (hn : n ≤ 23)
    (h2 : 6930 * (((n : Int) + 1) - 7) < 11 * (C : Int))
    (h3 : 9240 * ((n : Int) + 1) - 111615 < 11 * (C : Int)) :
    Inv (n + 1) (step p s0 a) := by
  obtain ⟨hladder, hpos, htrained, hd1, hd2, hd3⟩ := hinv
  -- per-step caps
  have he220 : growthAmount s0 a ≤ 220 := growthAmount_le_220 s0 a hleg hpos
  have hq735 : qOf s0 a ≤ 735 := qOf_le_735 s0 a hleg
  have hcrle : credit a (qOf s0 a) ≤ qOf s0 a := credit_le a (qOf s0 a)
  have hp0le3 : s0.pop ≤ 3 := pop_le_three_of_ladder hladder hn
  have hpa : s0.pop ≤ popAfter s0 a := by
    unfold popAfter
    split <;> omega
  -- step projections
  have hfood_step : (step p s0 a).food = foodAfter s0 a := step_food p s0 a
  have hpop_step : (step p s0 a).pop = popAfter s0 a ∨
      (step p s0 a).pop = popAfter s0 a - 1 := step_pop p s0 a
  have hfloor : floorI (step p s0 a).pop ≤ floorI (popAfter s0 a) := by
    rcases hpop_step with h | h
    · rw [h]; exact Int.le_refl _
    · rw [h]; exact floorI_mono _ _ (Nat.sub_le _ _)
  -- the population after the growth phase is at most 4, and 4 is impossible
  have hp1le3 : popAfter s0 a ≤ 3 := by
    by_cases hg : wouldGrow s0 a = true
    · have hp1 : popAfter s0 a = s0.pop + 1 := by simp [popAfter, hg]
      rw [hp1]
      rcases Nat.lt_or_ge (s0.pop + 1) 4 with hlt | hge
      · omega
      · exfalso
        have hp3 : s0.pop = 3 := by omega
        -- growth at population 3 needs `3383` food, but the ladder caps it at
        -- `220·23 − 3900 = 1160`
        have hthr : s0.food + growthAmount s0 a ≥ threshold s0.pop :=
          (wouldGrow_iff s0 a).mp hg
        rw [hp3, threshold_three] at hthr
        have hf3 : floorI s0.pop = 3900 := by
          rw [hp3]; decide +kernel
        have hcast : (220 : Int) * (n : Int) ≤ 220 * 23 := by
          have : (n : Int) ≤ 23 := by exact_mod_cast hn
          omega
        rw [hp3] at hd1 hd2 hd3
        omega
    · have hg' : wouldGrow s0 a = false := by simpa using hg
      rw [popAfter_eq s0 a hg']
      omega
  -- LADDER at `n+1`
  have hladder' : ((step p s0 a).food : Int) + floorI (step p s0 a).pop ≤
      220 * (((n : Int) + 1)) := by
    rw [hfood_step]
    by_cases hg : wouldGrow s0 a = true
    · have hfa : foodAfter s0 a = 0 := by simp [foodAfter, hg]
      rw [hfa]
      have hp1 : popAfter s0 a = s0.pop + 1 := by simp [popAfter, hg]
      rw [hp1] at hfloor
      have hthr : s0.food + growthAmount s0 a ≥ threshold s0.pop :=
        (wouldGrow_iff s0 a).mp hg
      have hthrI : (threshold s0.pop : Int) ≤ (s0.food : Int) + (growthAmount s0 a : Int) := by
        exact_mod_cast hthr
      have hsucc : floorI (s0.pop + 1) ≤ floorI s0.pop + (threshold s0.pop : Int) :=
        floorI_succ s0.pop
      have heI : (growthAmount s0 a : Int) ≤ 220 := by omega
      omega
    · have hg' : wouldGrow s0 a = false := by simpa using hg
      have hfa : foodAfter s0 a = s0.food + growthAmount s0 a := by
        simp [foodAfter, hg']
      rw [hfa]
      rw [popAfter_eq s0 a hg'] at hfloor
      have heI : (growthAmount s0 a : Int) ≤ 220 := by omega
      omega
  -- credit bound: `prog + credit < cost`, by population cases
  have hprogleI : ((s0.prog + credit a (qOf s0 a) : Nat) : Int) < (C : Int) := by
    by_cases hg : wouldGrow s0 a = true
    · -- growth step: population goes 1→2 or 2→3
      have hp1 : popAfter s0 a = s0.pop + 1 := by simp [popAfter, hg]
      have hthr : s0.food + growthAmount s0 a ≥ threshold s0.pop :=
        (wouldGrow_iff s0 a).mp hg
      rcases (by omega : s0.pop = 1 ∨ s0.pop = 2 ∨ s0.pop = 3) with h1 | h2' | h3'
      · -- 1 → 2: no credit at pre-turn population 1
        have hcz : credit a (qOf s0 a) = 0 :=
          credit_zero_of_pop_lt_two s0 a hleg (by omega)
        have hpz : (s0.prog : Int) = 0 := hd1 h1
        have hCpos : (0 : Int) < (C : Int) := by omega
        omega
      · -- 2 → 3: the basket before growth is `≥ 2400 − 220 = 2180`
        have hd := hd2 h2'
        have hthrI : (threshold s0.pop : Int) ≤ (s0.food : Int) + (growthAmount s0 a : Int) := by
          omega
        rw [h2', threshold_two] at hthrI
        have heI : (growthAmount s0 a : Int) ≤ 220 := by omega
        have hcrI : (credit a (qOf s0 a) : Int) ≤ 735 := by
          have hqI : (qOf s0 a : Int) ≤ 735 := by omega
          omega
        omega
      · -- 3 → 4: excluded by the ladder
        exact absurd hp1le3 (by omega)
    · -- non-growth step
      have hg' : wouldGrow s0 a = false := by simpa using hg
      have hp1 : popAfter s0 a = s0.pop := popAfter_eq s0 a hg'
      rcases (by omega : s0.pop = 1 ∨ s0.pop = 2 ∨ s0.pop = 3) with h1 | h2' | h3'
      · have hcz : credit a (qOf s0 a) = 0 :=
          credit_zero_of_pop_lt_two s0 a hleg (by omega)
        have hpz : (s0.prog : Int) = 0 := hd1 h1
        have hCpos : (0 : Int) < (C : Int) := by omega
        omega
      · have hd := (hd2 h2').1
        have hq : qOf s0 a ≤ 630 := qOf_le_630 s0 a hleg h2' hg'
        have hcrI : (credit a (qOf s0 a) : Int) ≤ 630 := by
          have hqI : (qOf s0 a : Int) ≤ 630 := by omega
          omega
        omega
      · have hd := hd3 h3'
        have hcrI : (credit a (qOf s0 a) : Int) ≤ 735 := by
          have hqI : (qOf s0 a : Int) ≤ 735 := by omega
          omega
        omega
  -- therefore the step does not complete, and the plain projections hold
  have hprogle : s0.prog + credit a (qOf s0 a) < p.cost := by
    have hltC : s0.prog + credit a (qOf s0 a) < C := by omega
    omega
  have hnc : ¬ completes p s0 a := by
    apply not_completes_of_progAfter_lt
    exact hprogle
  have hpop_plain : (step p s0 a).pop = popAfter s0 a := by
    unfold step
    rw [if_neg hnc]
  have hfood_plain : (step p s0 a).food = foodAfter s0 a := hfood_step
  have hprog_plain : (step p s0 a).prog = s0.prog + credit a (qOf s0 a) := by
    unfold step
    rw [if_neg hnc]
    rfl
  have htrained_plain : (step p s0 a).trained = 0 := by
    unfold step
    rw [if_neg hnc]
    exact htrained
  -- assemble the invariant at `n+1`
  refine ⟨hladder', ?_, htrained_plain, ?_, ?_, ?_⟩
  · rw [hpop_plain]
    exact Nat.le_trans hpos hpa
  · -- population 1: no credit was possible
    intro hpop1
    have hcz : credit a (qOf s0 a) = 0 := credit_zero_of_pop_lt_two s0 a hleg (by omega)
    have hpz : (s0.prog : Int) = 0 := hd1 (by omega)
    rw [hprog_plain]
    omega
  · -- population 2
    intro hpop2
    have hp1eq : popAfter s0 a = 2 := by rw [← hpop_plain]; exact hpop2
    by_cases hg : wouldGrow s0 a = true
    · -- arrival: 1 → 2, credit zero, food basket empty
      have hp0 : s0.pop = 1 := by
        have : popAfter s0 a = s0.pop + 1 := by simp [popAfter, hg]
        omega
      have hcz : credit a (qOf s0 a) = 0 :=
        credit_zero_of_pop_lt_two s0 a hleg (by omega)
      have hpz : (s0.prog : Int) = 0 := hd1 hp0
      have hfa : foodAfter s0 a = 0 := by simp [foodAfter, hg]
      have hge7 : (7 : Int) ≤ (n : Int) + 1 := by
        have hf2 : floorI (popAfter s0 a) = 1500 := by
          rw [hp1eq]; decide +kernel
        rw [hfood_plain, hpop_plain, hf2, hfa] at hladder'
        omega
      constructor
      · rw [hprog_plain]; omega
      · rw [hprog_plain, hfood_plain, hfa]; omega
    · -- non-growth at population 2: `q ≤ 630` and the dual
      have hg' : wouldGrow s0 a = false := by simpa using hg
      have hp0 : s0.pop = 2 := by
        have : popAfter s0 a = s0.pop := popAfter_eq s0 a hg'
        omega
      have hd := hd2 hp0
      have hq : qOf s0 a ≤ 630 := qOf_le_630 s0 a hleg hp0 hg'
      have hcrI : (credit a (qOf s0 a) : Int) ≤ 630 := by
        have hqI : (qOf s0 a : Int) ≤ 630 := by omega
        omega
      have hdual : 11 * (credit a (qOf s0 a) : Int) + 21 * (growthAmount s0 a : Int) ≤ 9240 := by
        have hnat := dual_credit s0 a hleg hpos hp0le3 hg'
        omega
      have heI : (growthAmount s0 a : Int) ≤ 220 := by omega
      have hfa : foodAfter s0 a = s0.food + growthAmount s0 a := by simp [foodAfter, hg']
      constructor
      · rw [hprog_plain]; omega
      · rw [hprog_plain, hfood_plain, hfa]; omega
  · -- population 3
    intro hpop3'
    have hp1eq : popAfter s0 a = 3 := by rw [← hpop_plain]; exact hpop3'
    by_cases hg : wouldGrow s0 a = true
    · -- transition 2 → 3: the basket `≥ 2180` is charged against the pop-2 dual
      have hp0 : s0.pop = 2 := by
        have : popAfter s0 a = s0.pop + 1 := by simp [popAfter, hg]
        omega
      have hd := hd2 hp0
      have hthr : s0.food + growthAmount s0 a ≥ threshold s0.pop :=
        (wouldGrow_iff s0 a).mp hg
      have hthrI : (threshold s0.pop : Int) ≤ (s0.food : Int) + (growthAmount s0 a : Int) := by
        omega
      rw [hp0, threshold_two] at hthrI
      have heI : (growthAmount s0 a : Int) ≤ 220 := by omega
      have hcrI : (credit a (qOf s0 a) : Int) ≤ 735 := by
        have hqI : (qOf s0 a : Int) ≤ 735 := by omega
        omega
      rw [hprog_plain]
      omega
    · -- non-growth at population 3: only the `q ≤ 735` cap is used
      have hg' : wouldGrow s0 a = false := by simpa using hg
      have hp0 : s0.pop = 3 := by
        have : popAfter s0 a = s0.pop := popAfter_eq s0 a hg'
        omega
      have hd := hd3 hp0
      have hcrI : (credit a (qOf s0 a) : Int) ≤ 735 := by
        have hqI : (qOf s0 a : Int) ≤ 735 := by omega
        omega
      rw [hprog_plain]
      omega

/-! ## 9. Reachability induction

The invariant is carried from `init` along every exact-step path. The horizon
`T ≤ 24` is used twice: the food ladder then forces `pop ≤ 3`, and the numeric
credit bounds are what make a completion impossible. -/

theorem inv_of_reachable (p : Params) (C T : Nat) (hcost : p.cost = C) (hT : T ≤ 24)
    (hC : 0 < C)
    (h2 : ∀ t, t ≤ T → 6930 * ((t : Int) - 7) < 11 * (C : Int))
    (h3 : ∀ t, t ≤ T → 9240 * (t : Int) - 111615 < 11 * (C : Int)) :
    ∀ t, t ≤ T → ∀ s, Reachable (model p) t s → Inv t s := by
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
          have hleg : legal s0 a := (model_legal_iff p s0 a).mp hlegal
          have hinv : Inv n s0 := ih (by omega) s0 hreach
          have hn : n ≤ 23 := by omega
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
          exact inv_step p C hC hcost hinv hleg hn h2n h3n

/-! ## 10. Lower bounds on the model

Both costs use the same invariant; only the horizon and the numeric endpoint
change. Case A is closed with `MvpArithmetic.caseA_19` / `caseA_24`, case B
with the state-local endpoint proved above. -/

/-- At `t = 19` no reachable state has trained a Settler (cost 80 model). -/
theorem trained_zero_at_19 (p : Params) (hcost : p.cost = 8000) :
    ∀ t, t ≤ 19 → ∀ s, Reachable (model p) t s → s.trained = 0 := by
  have hT : 19 ≤ 24 := by decide
  have hC : 0 < 8000 := by decide
  have h2 : ∀ t : Nat, t ≤ 19 → 6930 * ((t : Int) - 7) < 11 * (8000 : Int) := by
    intro t ht
    have : (t : Int) ≤ 19 := by exact_mod_cast ht
    omega
  have h3 : ∀ t : Nat, t ≤ 19 → 9240 * ((t : Int) - 111615 * 0) - 111615 < 11 * (8000 : Int) := by
    intro t ht
    have : (t : Int) ≤ 19 := by exact_mod_cast ht
    omega
  intro t ht s hreach
  have hinv := inv_of_reachable p 8000 19 hcost hT hC h2 h3 t ht s hreach
  exact hinv.2.2.1

/-- At `t = 24` no reachable state has trained a Settler (cost 110 model). -/
theorem trained_zero_at_24 (p : Params) (hcost : p.cost = 11000) :
    ∀ t, t ≤ 24 → ∀ s, Reachable (model p) t s → s.trained = 0 := by
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
  intro t ht s hreach
  have hinv := inv_of_reachable p 11000 24 hcost hT hC h2 h3 t ht s hreach
  exact hinv.2.2.1

/-- **Progress bound at `t = 19`** (cost-80 horizon): every reachable state has
`prog ≤ 7560`. Case A is attained by the model witness (`witness_after_nineteen`
has `prog = 7560`), case B is far below it. -/
theorem prog_le_7560_at_19 (p : Params) (hcost : p.cost = 8000) :
    ∀ s, Reachable (model p) 19 s → s.prog ≤ 7560 := by
  intro s hreach
  have hC : 0 < 8000 := by decide
  have h2 : ∀ t : Nat, t ≤ 19 → 6930 * ((t : Int) - 7) < 11 * (8000 : Int) := by
    intro t ht
    have : (t : Int) ≤ 19 := by exact_mod_cast ht
    omega
  have h3 : ∀ t : Nat, t ≤ 19 → 9240 * (t : Int) - 111615 < 11 * (8000 : Int) := by
    intro t ht
    have : (t : Int) ≤ 19 := by exact_mod_cast ht
    omega
  -- the invariant does not depend on the cost beyond `inv_step`'s side
  -- conditions, so any parameter with cost 8000 gives the bound
  have hinv := inv_of_reachable p 8000 19 hcost (by decide) hC h2 h3 19 (by decide) s hreach
  have hp := pop_le_three_of_ladder hinv.1 (by decide : 19 ≤ 23)
  obtain ⟨-, hposp, -, hd1, hd2, hd3⟩ := hinv
  rcases (by omega : s.pop = 1 ∨ s.pop = 2 ∨ s.pop = 3) with h1 | h2' | h3'
  · have := hd1 h1; omega
  · have := (hd2 h2').1; omega
  · have := hd3 h3'; omega

/-! ## 11. Headline: `NoEarlier` / `OptimalAt` on the actual model -/

/-- **No Settler can be trained before step 20** in the cost-80 model. This is
the lower-bound half of `OptimalAt (model p) goal 20`, derived from `Reachable`
(not from an enumeration of frontiers, and not from an assumed bridge). -/
theorem noEarlier_20 (p : Params) (hcost : p.cost = 8000) :
    NoEarlier (model p) goal 20 := by
  intro t ht s hreach hgoal
  have ht19 : t ≤ 19 := by omega
  have hz := trained_zero_at_19 p hcost t ht19 s hreach
  unfold goal at hgoal
  omega

/-- **`OptimalAt` at 20 for the baseline θ***: the model's own witness
(`baseline_achievable`) plus the proved lower bound. -/
theorem optimalAt_baseline : OptimalAt (model baselineParams) goal 20 :=
  ⟨baseline_achievable, noEarlier_20 baselineParams rfl⟩

/-- **No Settler can be trained before step 25** in the cost-110 model. -/
theorem noEarlier_25 (p : Params) (hcost : p.cost = 11000) :
    NoEarlier (model p) goal 25 := by
  intro t ht s hreach hgoal
  have ht24 : t ≤ 24 := by omega
  have hz := trained_zero_at_24 p hcost t ht24 s hreach
  unfold goal at hgoal
  omega

/-- **`OptimalAt` at 25 for the cost-110 candidate**: the model's own witness
plus the proved lower bound. -/
theorem optimalAt_cost110 : OptimalAt (model cost110Params) goal 25 :=
  ⟨cost110_achievable, noEarlier_25 cost110Params rfl⟩

/-! ## 12. Consistency with the model witness and the arithmetic core

The bound at `t = 19` is *tight*: the model's baseline witness has exactly
`prog = 7560` (`Mvp.witness_after_nineteen`), the case-A endpoint
`630·12`. The case-A endpoint itself is closed by the arithmetic core's
`MvpArithmetic.caseA_19`, which is the shared numeric fact. -/

/-- Case A endpoint via the arithmetic core: `11·prog ≤ 6930·12` implies
`prog < 8000`. -/
theorem caseA_endpoint (prog : Nat) (h : 11 * (prog : Int) ≤ 6930 * ((19 : Int) - 7)) :
    prog < 8000 := by
  have hnat : prog ≤ 630 * (19 - 7) := by
    have : (11 * (prog : Int)) ≤ 11 * 630 * 12 := by
      have : ((19 : Int) - 7) = 12 := by decide
      omega
    omega
  exact Civ6Verify.Bounds.MvpArithmetic.caseA_19 prog 7 (by decide) hnat

/-- Case B endpoint (state-local form): `11·prog ≤ 9240·19 − 111615` implies
`prog < 8000`. The document's case-B endpoint (`prog ≤ 5889`) is a further
relaxation of the same accounting. -/
theorem caseB_endpoint_19 (prog : Nat) (h : 11 * (prog : Int) ≤ 9240 * 19 - 111615) :
    prog < 8000 := by omega

theorem caseB_endpoint_24 (prog : Nat) (h : 11 * (prog : Int) ≤ 9240 * 24 - 111615) :
    prog < 11000 := by omega

/-- The baseline witness' progress at `t = 19` is exactly the case-A bound,
so no relaxation was wasted in case A. -/
theorem witness_prog_eq_bound :
    (run (model baselineParams) init (witness.take 19)).prog = 7560 := by
  rw [witness_after_nineteen]

end Civ6Verify.Bounds.MvpOptimality
