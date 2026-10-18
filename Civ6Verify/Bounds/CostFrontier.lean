/-
  Civ6Verify/Bounds/CostFrontier.lean

  CONDITIONAL, model-internal, **achievability-only** witness for the
  cost-dependent pop-2 vs pop-3 frontier explored in `search/cost_frontier.py`
  and documented in `mvp/COST-FRONTIER.md`.

  What this file proves
  ---------------------
  At settler cost `13861` (1/100 production units) there is a legal 29-step
  play whose tenth-through-last SETTLER credit is taken on a step that grows
  the city from population 2 to population 3 and completes the Settler in the
  same step.  This is `AchievableAt (model {cost := 13861}) goal 29`.

  What this file does **not** prove (and must not be read as proving)
  ----------------------------------------------------------------
  * It does **not** prove that cost 13861 is the first such cost, nor that the
    pop-3 line is *strictly earlier* than every strict pop-2 line.  That needs
    the strict pop-2 lower bound `N_p2(c) = 7 + ceil(c/630) >= 30` at
    `c = 13861`, which is the `mvp/LOWER-BOUND.md` bridge obligation
    (B-1/B-5/B-6), not a theorem in this development.
  * It makes no Civ6 claim at all.  `[V] = 0`, cost 13861 is outside the frozen
    contract box `Theta_MVP = {8000, 11000}`, and the result is a
    model-internal sensitivity point.

  Trust: no Mathlib, no `sorry`, no `native_decide`, no custom axiom.  The
  finite replay is closed with `decide +kernel`, matching
  `Civ6Verify/Model/Mvp.lean`.
-/

import Civ6Verify.Model.Mvp

namespace Civ6Verify.Bounds.CostFrontier

open Civ6Verify.Reachability
open Civ6Verify.Model.Mvp

/-- Settler cost 13861 (1/100 units).  This is the first cost at which the
untrusted search of `search/cost_frontier.py` reports a pop-3 growth line
completing at step 29 while every strict pop-2 line needs step 30.  It lies
outside the frozen candidate axis `{80, 110}`. -/
def cost13861Params : Params := { cost := 13861 }

/-- Worked-tile mask for `G` (tile 0). -/
def maskG : Fin 16 := ⟨1, by decide⟩
/-- Worked-tile mask for `GH + PH` (tiles 1 and 2). -/
def maskGHPH : Fin 16 := ⟨6, by decide⟩

/-- `G` with IDLE (the pop-1 food rush). -/
def aIdleG : Action := ⟨maskG, none, .idle⟩
/-- `GH + PH` with SETTLER, no growth, q = 630. -/
def aSettlerGHPH : Action := ⟨maskGHPH, none, .settler⟩
/-- `GH + PH` with the new citizen on `P` (tile 3); this is the growth step
`2 -> 3`, on which `extra` adds 100 production before `q` is computed. -/
def aSettlerGHPH_P : Action := ⟨maskGHPH, some ⟨3, by decide⟩, .settler⟩

/-- The 29-step witness: 7 x `G` IDLE (grow to pop 2 at step 7), 21 x
`GH+PH` SETTLER (food 110/step, prog 630/step), then one `GH+PH+P` SETTLER at
step 29.  At step 28 the state is `(2, 2310, 13230, 0)`; step 29 has
`d = 100`, grows to pop 3, adds `extra = P`, and credits `q = 735`, so
`prog = 13965 >= 13861` and completion drops the population back to 2. -/
def witnessCost13861 : List Action :=
  List.replicate 7 aIdleG ++ List.replicate 21 aSettlerGHPH ++ [aSettlerGHPH_P]

theorem witnessCost13861_length : witnessCost13861.length = 29 := by
  decide +kernel

/-- Every step of the witness is legal at cost 13861. -/
theorem witnessCost13861_legal :
    LegalPath (model cost13861Params) init witnessCost13861 :=
  legalPathB_sound cost13861Params init witnessCost13861 (by decide +kernel)

/-- Final state of the witness: pop 2 (the completing step grew to 3 and then
dropped one citizen), food 0 (basket zero), `prog = 13965 - 13861 = 104`,
`trained = 1`. -/
theorem witnessCost13861_run :
    run (model cost13861Params) init witnessCost13861 =
      { pop := 2, food := 0, prog := 104, trained := 1 } := by
  decide +kernel

theorem witnessCost13861_achieves :
    goal (run (model cost13861Params) init witnessCost13861) := by
  rw [witnessCost13861_run]
  unfold goal
  decide +kernel

/-- Kernel-checked trace fact: after the first 28 steps the city is at
population 2 with food 2310 and prog 13230, i.e. one food step short of
`T(2) = 2400`. -/
theorem witnessCost13861_after_28 :
    run (model cost13861Params) init (witnessCost13861.take 28) =
      { pop := 2, food := 2310, prog := 13230, trained := 0 } := by
  decide +kernel

/-- Kernel-checked trace fact: the final action grows the city `2 → 3`
(`d = 100`, `e = 110`, basket 2310 + 110 = 2420 ≥ 2400).  Completion then
drops one citizen, which is why the final state has pop 2 again. -/
theorem witnessCost13861_last_grows :
    wouldGrow (run (model cost13861Params) init (witnessCost13861.take 28))
      aSettlerGHPH_P = true := by
  rw [witnessCost13861_after_28]
  decide +kernel

/-- Achievability at step 29 for cost 13861.  Minimality / the comparison with
the strict pop-2 class is deliberately **not** claimed. -/
theorem cost13861_achievable : AchievableAt (model cost13861Params) goal 29 :=
  AchievableAt.of_legalPath (M := model cost13861Params) (goal := goal) (N := 29)
    (as := witnessCost13861) witnessCost13861_length witnessCost13861_legal
    witnessCost13861_achieves

end Civ6Verify.Bounds.CostFrontier
