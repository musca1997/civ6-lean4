/-
  Civ6Verify/Model/Mvp.lean

  CONDITIONAL MVP v2.1 baseline model `M_MVP(θ*, σ)` for BASE Civilization VI:
  one city, four fixed workable tiles, first trained Settler as the goal.

  **No claim about the real game.** This file formalises the *model* in
  `mvp/RULE-CONTRACT.md` §3–§4 under the baseline candidate θ* = (settlerCost
  80, growth_first, newCitizen best, amenityStock 2, basket zero, exact
  production, threshold exact 3383). It does not claim that Civ6 implements
  these rules, does not run a fixture, and does not contain a build id.

  Scope of this module
  --------------------
  * A concrete finite action type (4-tile bitmask × extra tile × build) with an
    independently defined legality predicate and a filtered enumeration.
  * A `Civ6Verify.Reachability.Model` instance whose `legalActions_sound` and
    `legalActions_complete` fields are *proved* from `List.mem_filter`; the
    enumeration is not allowed to be a modelling assumption.
  * The exact per-step integer pipeline of §4 (`growth_first`, basket zero,
    exact production rounding) in 1/100 units, with no `Float`.
  * The contract's baseline witness (GH × 7 with IDLE, then GH+PH × 13 with
    SETTLER) is replayed and kernel-reduced to `trained = 1` at step 20. This is
    an **upper bound only**: `NoEarlier` at 20 and the full horizon certificate
    are deliberately not attempted here.
  * A cost-110 instantiation (same witness prefix, 18 settler steps) as an
    upper-bound cross-check of the parameterised cost axis.

  Trust boundary
  --------------
  * No Mathlib, no `sorry`, no `native_decide`, no custom axiom.
  * Ground numeric facts are closed with `decide +kernel`, which reduces the
    decidable proposition inside the kernel (it adds no `Lean.ofReduceBool`).
  * `step?` is the normative Option step; `step` is its total core for the
    generic `Model` class. Only actions satisfying `legal` are composed by
    `Reachable`; illegal actions may use truncated `Nat` subtraction and are
    not meaningful.

  Contract alignment: this file follows RULE-CONTRACT v2.1 §0/§3/§4. The frozen
  interface is `step : State → Action → Option State` with
  `legal s a := (step s a).isSome`. We keep a total core `step` for the
  `Model.step` field and define `step?` as `some (step ...)` exactly on legal
  actions; `step_total` is proved. `extraGain(⊥) = 0`, and `IDLE ⇒ extra = ⊥`,
  so the baseline growth step is IDLE with no extra (`q = 420`, discarded), not
  the v2 reading `q = 525`.

  T3 is an explicit conditional assumption: `T(3) = 33.8284` food, represented
  as the exact integer comparison bound `3383` in 1/100 units (`thresholdRounding
  = exact`). Contract v2.1 argues C7 is inert by G1; this module does not
  re-derive G1 and simply fixes the exact reading. `T(4) = 4420` is defined only
  for totality and is never evaluated on the path proved here.

  Time convention: `t = 0` is the founding snapshot; a step is one settlement
  step, not a UI turn.
-/

import Civ6Verify.Reachability.Finite

namespace Civ6Verify.Model.Mvp

open Civ6Verify.Reachability

/-! ## 1. Tiles and yields

  Tile ids are `0 = G` (2F/0P), `1 = GH` (2F/1P), `2 = PH` (1F/2P),
  `3 = P` (1F/1P). Yields are in 1/100 units. The city centre and palace are
  folded into the fixed `200` food / `300` production below; they are never
  assignable. -/

/-- Tile food yield in 1/100 units. -/
def tileFood : Fin 4 → Nat
  | ⟨0, _⟩ => 200
  | ⟨1, _⟩ => 200
  | ⟨2, _⟩ => 100
  | _ => 100

/-- Tile production yield in 1/100 units. -/
def tileProd : Fin 4 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 100
  | ⟨2, _⟩ => 200
  | _ => 100

/-- The four tile ids, for readability. -/
def tileG : Fin 4 := ⟨0, by decide⟩
def tileGH : Fin 4 := ⟨1, by decide⟩
def tilePH : Fin 4 := ⟨2, by decide⟩
def tileP : Fin 4 := ⟨3, by decide⟩

/-! ## 2. Actions: bitmask subset, extra tile, build

  `work.val` is a 4-bit mask; bit `i` means tile `i` is worked. Every mask is a
  subset of the four tiles, so tile capacity 1 and "no duplicate tile" are
  structural. `extra` is the tile the new citizen would work; `build` is the
  step's selected item. -/

/-- Build choice. `idle` stands for "building something else" and credits no
settler progress (R-SET-9). -/
inductive Build where
  | idle
  | settler
  deriving DecidableEq, Repr

/-- A finite action: worked-tile mask, optional extra tile, build choice. -/
structure Action where
  /-- 4-bit worked-tile mask; `work.val < 16`. -/
  work : Fin 16
  /-- Tile the new citizen would work, if this step grows. -/
  extra : Option (Fin 4)
  /-- Selected item. -/
  build : Build
  deriving DecidableEq, Repr

/-- The subset of tiles worked by `a`, in tile-id order. The mask guarantees
each tile occurs at most once. -/
def workTiles (a : Action) : List (Fin 4) :=
  (List.finRange 4).filter (fun t => a.work.val.testBit t.val)

/-- Sum of food over worked tiles (1/100 units). -/
def workFood (a : Action) : Nat :=
  (workTiles a).foldl (fun acc t => acc + tileFood t) 0

/-- Sum of production over worked tiles (1/100 units). -/
def workProd (a : Action) : Nat :=
  (workTiles a).foldl (fun acc t => acc + tileProd t) 0

/-- Number of worked tiles, i.e. assigned citizens. -/
def workCount (a : Action) : Nat := (workTiles a).length

/-- `extraGain(⊥) = 0`, otherwise the extra tile's production. This is the
v2.1 totalised `extraGain`; it is added only on an actual growth event. -/
def extraGain (a : Action) : Nat :=
  match a.extra with
  | none => 0
  | some t => tileProd t

/-- Legality of the extra assignment: none is fine, and a present extra tile
must not already be in the worked mask. -/
def extraUnworked (a : Action) : Bool :=
  match a.extra with
  | none => true
  | some t => !(a.work.val.testBit t.val)

/-! ## 3. State and the numeric pipeline

  `prog` is settler-specific progress (R-PROD-2). `trained` is the monotone
  completion history counter; the goal is `trained ≥ 1`. -/

/-- City state `(pop, food, prog, trained)`. -/
structure State where
  /-- Population. -/
  pop : Nat
  /-- Stored food, 1/100 units. -/
  food : Nat
  /-- Settler-specific production progress, 1/100 units. -/
  prog : Nat
  /-- Monotone count of trained settlers. -/
  trained : Nat
  deriving DecidableEq, Repr

/-- Initial state: `t = 0`, pop 1, empty food basket, no settler progress, no
trained settler. -/
def init : State := { pop := 1, food := 0, prog := 0, trained := 0 }

/-- City food before the per-citizen ration: centre 200 + worked tiles.
The extra tile never feeds `F`. -/
def baseFood (a : Action) : Nat := 200 + workFood a

/-- City production before modifiers: centre 100 + palace 200 + worked tiles. -/
def baseProd (a : Action) : Nat := 300 + workProd a

/-- Raw food surplus `F − 200·pop`, as a natural number. Legality below proves
`200·pop ≤ F`; the subtraction is only meaningful on legal actions. -/
def surplus (s : State) (a : Action) : Nat := baseFood a - 200 * s.pop

/-- Growth thresholds in 1/100 units.

`T(3) = 3383` is the **conditional exact comparison bound** for 33.8284 food:
food is stored as an integer in 1/100 units, so `food ≥ 3383` is exactly
`food ≥ 33.8284`. This is the `thresholdRounding = exact` baseline (C7).
`T(4) = 4420` and the fallback are for totality only; G1 says they are never
evaluated on the baseline path. -/
def threshold : Nat → Nat
  | 0 => 100000000
  | 1 => 1500
  | 2 => 2400
  | 3 => 3383
  | 4 => 4420
  | _ => 100000000

/-- Amenity requirement `req(p) = max(0, ⌊(p−1)/2⌋)`. For `p = 0` the natural
number subtraction floors at zero. -/
def amenityReq (p : Nat) : Nat := (p - 1) / 2

/-- Amenity balance `stock − req(p)` for the baseline `amenityStock = 2`.
Signed, so the displeased tier is represented faithfully even though it is
unreachable on the baseline path. -/
def amenityBalance (p : Nat) : Int := 2 - (amenityReq p : Int)

/-- Growth multiplier: Happy 110, Content 100, Displeased 85. -/
def growthMult (p : Nat) : Nat :=
  if 1 ≤ amenityBalance p then 110
  else if 0 ≤ amenityBalance p then 100
  else 85

/-- Non-food multiplier: Happy 105, Content 100, Displeased 95. -/
def prodMult (p : Nat) : Nat :=
  if 1 ≤ amenityBalance p then 105
  else if 0 ≤ amenityBalance p then 100
  else 95

/-- Growth food `e = d · growthMult / 100`, exact on the reachable finite yield
set (G6). This is floor division, so it is total; on legal actions `d` is a
multiple of 100 and the division is exact. -/
def growthAmount (s : State) (a : Action) : Nat :=
  surplus s a * growthMult s.pop / 100

/-- Does this step actually grow? Evaluated on the pre-turn state and the
action, exactly as in the normative step. -/
def wouldGrow (s : State) (a : Action) : Bool :=
  decide (s.food + growthAmount s a ≥ threshold s.pop)

/-- Population after the growth phase (before any settler completion). -/
def popAfter (s : State) (a : Action) : Nat :=
  if wouldGrow s a then s.pop + 1 else s.pop

/-- Food basket after the growth phase. Baseline `basketOnGrowth = zero`:
the whole basket is emptied on growth and overflow is discarded. -/
def foodAfter (s : State) (a : Action) : Nat :=
  if wouldGrow s a then 0 else s.food + growthAmount s a

/-- Production `P` for this step. The extra tile contributes only when growth
actually occurs (`newCitizen = best`); otherwise it yields nothing. -/
def production (s : State) (a : Action) : Nat :=
  baseProd a + (if wouldGrow s a then extraGain a else 0)

/-- Modified production `q = P · prodMult(tier(popAfter)) / 100`, with exact
production rounding. -/
def qOf (s : State) (a : Action) : Nat :=
  production s a * prodMult (popAfter s a) / 100

/-- Settler credit: `q` only for `SETTLER`, zero for `IDLE` (R-SET-9). -/
def credit (a : Action) (q : Nat) : Nat :=
  if a.build = Build.settler then q else 0

/-- Settler progress after the production phase. -/
def progAfter (s : State) (a : Action) : Nat :=
  s.prog + credit a (qOf s a)

/-- Model parameters. Only the settler cost is parameterised in this module;
the other axes are fixed at the baseline θ*. -/
structure Params where
  /-- Settler production cost in 1/100 units (80 → 8000, 110 → 11000). -/
  cost : Nat
  deriving DecidableEq, Repr

/-- Baseline candidate θ*: settler cost 80, i.e. `8000` in 1/100 units. -/
def baselineParams : Params := { cost := 8000 }

/-- Cost-110 candidate, i.e. `11000` in 1/100 units. -/
def cost110Params : Params := { cost := 11000 }

/-- Completion test: the build is SETTLER and credited progress reaches the
cost. Legality separately requires pre-turn `pop ≥ 2`. -/
def completes (p : Params) (s : State) (a : Action) : Prop :=
  a.build = Build.settler ∧ progAfter s a ≥ p.cost

instance (p : Params) (s : State) (a : Action) : Decidable (completes p s a) := by
  unfold completes
  infer_instance

/-- One settlement step, `growth_first` order, exactly as §4:

1. food `F = 200 + Σ_work food`;
2. surplus `d = F − 200·pop` (legality ensures `d ≥ 0`);
3. growth food `e = d·growthMult(tier(pop))/100`;
4. one growth if `food + e ≥ T(pop)`, basket emptied (`zero`) and `pop` +1;
5. production `P = 300 + Σ_work prod + (grown ? extraGain(extra) : 0)`;
6. `q = P·prodMult(tier(popAfter))/100`;
7. `prog += q` only for SETTLER;
8. if SETTLER and `prog ≥ cost`: `pop := popAfter − 1`, `prog := prog − cost`,
   `trained += 1`; otherwise only the outputs of steps 1–7 are recorded.

`step` is total. -/
def step (p : Params) (s : State) (a : Action) : State :=
  if completes p s a then
    { pop := popAfter s a - 1, food := foodAfter s a,
      prog := progAfter s a - p.cost, trained := s.trained + 1 }
  else
    { pop := popAfter s a, food := foodAfter s a,
      prog := progAfter s a, trained := s.trained }

/-! ## 4. Legality, Option step and `step_total`

  `legalGuard` is the readable conjunction behind v2.1 §3:

  * worked citizens `≤ pop` (tile capacity 1 is structural in the mask);
  * the extra tile, if any, is not already worked;
  * SETTLER is legal only when the **pre-turn** pop is at least 2 (A8);
  * IDLE has no extra tile (`IDLE ⇒ extra = none`, frozen in v2.1);
  * the pre-ration food surplus is non-negative (`200·pop ≤ F`), i.e. no
    starvation actions.

  The extra tile is optional on a growth step: `extraGain(⊥) = 0`, so a growth
  step with no extra is legal and simply contributes no extra production. This
  is the v2.1 resolution of the v2 §3/§4 conflict; the baseline growth step is
  IDLE with `extra = none` and `q = 420`. -/

/-- The v2.1 legality conjunction (the body of the Option step's guard). -/
def legalGuard (s : State) (a : Action) : Prop :=
  workCount a ≤ s.pop ∧
  extraUnworked a = true ∧
  (a.build = Build.settler → 2 ≤ s.pop) ∧
  (a.build = Build.idle → a.extra = none) ∧
  200 * s.pop ≤ baseFood a

instance (s : State) (a : Action) : Decidable (legalGuard s a) := by
  unfold legalGuard
  infer_instance

/-- The Option-valued normative step: `some` exactly on legal actions,
  `none` on a starved or otherwise illegal action. -/
def step? (p : Params) (s : State) (a : Action) : Option State :=
  if legalGuard s a then some (step p s a) else none

/-- v2.1's frozen legality: `legal s a := (step s a).isSome`. The guard does
not depend on the cost, so the baseline instance is representative of every
parameter. -/
def legal (s : State) (a : Action) : Prop :=
  (step? baselineParams s a).isSome = true

instance (s : State) (a : Action) : Decidable (legal s a) := by
  unfold legal
  infer_instance

/-- The Option step is `some` exactly on `legalGuard`. -/
theorem step?_isSome (p : Params) (s : State) (a : Action) :
    (step? p s a).isSome = true ↔ legalGuard s a := by
  unfold step?
  by_cases h : legalGuard s a <;> simp [h]

/-- `legal` is exactly the readable guard. -/
theorem legal_iff_guard (s : State) (a : Action) :
    legal s a ↔ legalGuard s a := by
  unfold legal
  exact step?_isSome baselineParams s a

/-- On a legal action the Option step is the total core step. -/
theorem step?_eq_some (p : Params) (s : State) (a : Action)
    (h : legalGuard s a) : step? p s a = some (step p s a) := by
  unfold step?
  rw [if_pos h]

/-- O2b: a legal action has a successful Option step. -/
theorem step_total (p : Params) (s : State) (a : Action)
    (h : legalGuard s a) : ∃ s', step? p s a = some s' :=
  ⟨step p s a, step?_eq_some p s a h⟩

/-- O2b in `legal` form. -/
theorem step_total_of_legal (p : Params) (s : State) (a : Action)
    (h : legal s a) : ∃ s', step? p s a = some s' :=
  step_total p s a ((legal_iff_guard s a).mp h)

/-- One worked citizen per tile: the mask has at most four set bits. -/
theorem workCount_le_four (a : Action) : workCount a ≤ 4 := by
  unfold workCount workTiles
  simpa using List.length_filter_le (fun t : Fin 4 => a.work.val.testBit t.val) (List.finRange 4)

/-! ## 5. Finite enumeration and the `Model` instance

  The candidate list is the full product `16 masks × 5 extra values × 2 builds`
  (the 16 masks are exactly the powerset of the four tiles). `legalActions`
  filters it by `legal`. Soundness and completeness are therefore proved, not
  assumed. -/

/-- All 16 masks. -/
def allWork : List (Fin 16) := List.finRange 16

/-- `none` plus the four tile ids. -/
def allExtra : List (Option (Fin 4)) := none :: (List.finRange 4).map some

/-- Both build choices. -/
def allBuild : List Build := [.idle, .settler]

/-- The full candidate action list. -/
def allActions : List Action :=
  allWork.flatMap fun w =>
    allExtra.flatMap fun e =>
      allBuild.map fun b => ⟨w, e, b⟩

/-- Every action occurs in the candidate list. -/
theorem mem_allActions (a : Action) : a ∈ allActions := by
  obtain ⟨w, e, b⟩ := a
  simp only [allActions, List.mem_flatMap, List.mem_map]
  refine ⟨w, ?_, e, ?_, b, ?_, rfl⟩
  · rw [allWork, List.finRange]
    exact List.mem_ofFn.mpr ⟨w, rfl⟩
  · cases e with
    | none => simp [allExtra]
    | some t =>
        simp only [allExtra, List.mem_cons, List.mem_map]
        exact Or.inr ⟨t, by rw [List.finRange]; exact List.mem_ofFn.mpr ⟨t, rfl⟩, rfl⟩
  · cases b <;> simp [allBuild]

/-- The computable legal-action enumeration for a parameter. It filters the
full candidate list by `(step? p s a).isSome`, exactly v2.1's `legal`. -/
def legalActionsFor (p : Params) (s : State) : List Action :=
  allActions.filter (fun a => decide ((step? p s a).isSome))

/-- Baseline enumeration. -/
def legalActions (s : State) : List Action := legalActionsFor baselineParams s

/-- Enumeration membership is exactly the guard. -/
theorem mem_legalActionsFor (p : Params) (s : State) (a : Action) :
    a ∈ legalActionsFor p s ↔ legalGuard s a := by
  rw [legalActionsFor, List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact (step?_isSome p s a).mp (of_decide_eq_true h)
  · intro h
    exact ⟨mem_allActions a, by
      rw [decide_eq_true_eq]
      exact (step?_isSome p s a).mpr h⟩

/-- Baseline enumeration membership is exactly `legal`. -/
theorem mem_legalActions (s : State) (a : Action) :
    a ∈ legalActions s ↔ legal s a := by
  rw [legalActions, mem_legalActionsFor]
  exact (legal_iff_guard s a).symm

/-- The MVP `Model` instance for a cost parameter. `Model.legal` is literally
`(step? p s a).isSome = true`; the enumeration filters by the same predicate,
so soundness/completeness are proved rather than assumed. -/
def model (p : Params) : Model State Action where
  init := init
  step := step p
  legal := fun s a => (step? p s a).isSome = true
  legalDec := fun s a => inferInstance
  legalActions := legalActionsFor p
  legalActions_sound := by
    intro s a h
    rw [legalActionsFor] at h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  legalActions_complete := by
    intro s a h
    rw [legalActionsFor]
    exact List.mem_filter.mpr ⟨mem_allActions a, by rw [decide_eq_true_eq]; exact h⟩

/-- `Model.legal` is exactly the readable guard. -/
theorem model_legal_iff_guard (p : Params) (s : State) (a : Action) :
    (model p).legal s a ↔ legalGuard s a :=
  step?_isSome p s a

/-- The external `legal` predicate is the baseline representative of
`Model.legal` for every cost parameter. -/
theorem model_legal_iff (p : Params) (s : State) (a : Action) :
    (model p).legal s a ↔ legal s a := by
  rw [model_legal_iff_guard]
  exact (legal_iff_guard s a).symm

/-! ## 6. Goal and monotone history -/

/-- Goal: at least one trained Settler. `trained` is a history counter, not a
queue inspection. -/
def goal (s : State) : Prop := 1 ≤ s.trained

/-- Executable goal predicate. -/
def goalB (s : State) : Bool := decide (1 ≤ s.trained)

theorem goalB_spec (s : State) : goalB s = true ↔ goal s := by
  simp [goalB, goal]

theorem init_pop : init.pop = 1 := rfl
theorem init_food : init.food = 0 := rfl
theorem init_prog : init.prog = 0 := rfl
theorem init_trained : init.trained = 0 := rfl

theorem init_not_goal : ¬ goal init := by
  simp [goal, init]

/-- `trained` never decreases, so the goal is terminal. -/
theorem step_trained_ge (p : Params) (s : State) (a : Action) :
    s.trained ≤ (step p s a).trained := by
  unfold step
  split <;> simp

/-- Once the goal holds, every step keeps it. -/
theorem goal_step {p : Params} {s : State} {a : Action} (h : goal s) :
    goal (step p s a) :=
  Nat.le_trans h (step_trained_ge p s a)

/-- The goal is monotone along an arbitrary run (legality not needed). -/
theorem goal_run {p : Params} (s : State) (as : List Action) (h : goal s) :
    goal (run (model p) s as) := by
  induction as generalizing s with
  | nil => exact h
  | cons a rest ih =>
      exact ih (step p s a) (goal_step h)

/-! ## 7. Legal projections and semantic sanity lemmas -/

theorem legal_workCount {s : State} {a : Action} (h : legal s a) :
    workCount a ≤ s.pop :=
  ((legal_iff_guard s a).mp h).1

theorem legal_extraUnworked {s : State} {a : Action} (h : legal s a) :
    extraUnworked a = true :=
  ((legal_iff_guard s a).mp h).2.1

theorem legal_settler_pop {s : State} {a : Action} (h : legal s a)
    (hb : a.build = Build.settler) : 2 ≤ s.pop :=
  ((legal_iff_guard s a).mp h).2.2.1 hb

/-- v2.1 frozen rule: IDLE carries no extra tile. -/
theorem legal_idle_extra_none {s : State} {a : Action} (h : legal s a)
    (hb : a.build = Build.idle) : a.extra = none :=
  ((legal_iff_guard s a).mp h).2.2.2.1 hb

theorem legal_surplus {s : State} {a : Action} (h : legal s a) :
    200 * s.pop ≤ baseFood a :=
  ((legal_iff_guard s a).mp h).2.2.2.2

/-- On a legal action `extraGain` is zero when no extra is declared. -/
theorem extraGain_none (a : Action) (h : a.extra = none) : extraGain a = 0 := by
  simp [extraGain, h]

/-- On a legal action a declared extra contributes its tile production on a
growth step (and is ignored otherwise). -/
theorem extraGain_some (a : Action) (t : Fin 4) (h : a.extra = some t) :
    extraGain a = tileProd t := by
  simp [extraGain, h]

/-- A present extra tile is not worked. -/
theorem extraUnworked_spec {a : Action} (h : extraUnworked a = true) :
    ∀ t, a.extra = some t → a.work.val.testBit t.val = false := by
  intro t ht
  cases he : a.extra with
  | none => rw [he] at ht; exact absurd ht (by simp)
  | some t' =>
      have hbit : a.work.val.testBit t'.val = false := by
        simpa [extraUnworked, he] using h
      rw [he] at ht
      injection ht with htt
      subst htt
      exact hbit

/-- The extra tile is real and unworked. -/
theorem legal_extra_not_work {s : State} {a : Action} (h : legal s a)
    {t : Fin 4} (ht : a.extra = some t) : a.work.val.testBit t.val = false :=
  extraUnworked_spec (legal_extraUnworked h) t ht

/-- At pre-turn pop < 2 a legal action must be IDLE, so it credits zero. -/
theorem credit_zero_of_prePop_lt_two (s : State) (a : Action)
    (hl : legal s a) (hpop : s.pop < 2) : credit a (qOf s a) = 0 := by
  have hb : a.build = Build.idle := by
    cases hb : a.build with
    | idle => rfl
    | settler =>
        have := legal_settler_pop hl hb
        omega
  simp [credit, hb]

/-- Progress accounting for one total core step: either no completion and
`prog` increases by the credited `q`, or completion subtracts the cost and
increments `trained`. -/
theorem step_prog (p : Params) (s : State) (a : Action) :
    (step p s a).prog = s.prog + credit a (qOf s a) ∨
    ((step p s a).prog + p.cost = s.prog + credit a (qOf s a) ∧
      (step p s a).trained = s.trained + 1) := by
  unfold step
  by_cases h : completes p s a
  · rw [if_pos h]
    right
    constructor
    · simp [progAfter]
      have hge : progAfter s a ≥ p.cost := h.2
      simp [progAfter] at hge
      omega
    · rfl
  · rw [if_neg h]
    left
    simp [progAfter]

/-- IDLE leaves settler progress unchanged: no production banking. -/
theorem step_idle_prog (p : Params) (s : State) (a : Action)
    (h : a.build = Build.idle) : (step p s a).prog = s.prog := by
  simp [step, completes, progAfter, credit, h]

/-- IDLE never completes and never changes the trained-settler history. -/
theorem step_idle_trained (p : Params) (s : State) (a : Action)
    (h : a.build = Build.idle) : (step p s a).trained = s.trained := by
  simp [step, completes, h]

/-- Without an actual growth event the extra tile contributes no production
(the "no ghost output" requirement). -/
theorem step_no_growth_production (s : State) (a : Action)
    (hg : wouldGrow s a = false) : production s a = baseProd a := by
  simp [production, hg]

/-- Without growth the population is unchanged before completion. -/
theorem popAfter_eq (s : State) (a : Action) (hg : wouldGrow s a = false) :
    popAfter s a = s.pop := by
  simp [popAfter, hg]

/-! ## 8. Baseline witness: GH × 7 IDLE, then GH+PH × 13 SETTLER

  Masks: `GH = 0b0010 = 2`, `GH+PH = 0b0110 = 6`; the growth-step extra is
  `P` (tile 3). The first six IDLE steps store 220 food each (1320), the
  seventh grows (`1320 + 220 = 1540 ≥ 1500`) and empties the basket. The
  thirteen SETTLER steps add `e = 110` food and `q = 630` progress each, so
  the final step reaches `8190 ≥ 8000`. -/

/-- Mask for tile GH. -/
def maskGH : Fin 16 := ⟨2, by decide⟩
/-- Mask for the pair GH+PH. -/
def maskGHPH : Fin 16 := ⟨6, by decide⟩

/-- An IDLE action with an optional extra tile. -/
def aIdle (w : Fin 16) (e : Option (Fin 4)) : Action := ⟨w, e, .idle⟩

/-- A SETTLER action; no growth occurs on the settler steps of the witness, so
the canonical extra is `none`. -/
def aSettler (w : Fin 16) : Action := ⟨w, none, .settler⟩

/-- The v2.1 baseline witness, length 20: GH × 7 IDLE with no extra (the
growth step is IDLE with `extra = none`, q = 420 discarded), then GH+PH × 13
SETTLER. -/
def witness : List Action :=
  List.replicate 7 (aIdle maskGH none) ++ List.replicate 13 (aSettler maskGHPH)

/-- The cost-110 witness: the same prefix, then 18 SETTLER steps (length 25). -/
def witness110 : List Action :=
  List.replicate 7 (aIdle maskGH none) ++ List.replicate 18 (aSettler maskGHPH)

/-- Computable legality check for a whole action list. This is a proof device:
`legalPathB_sound` turns a `true` result into `LegalPath`. -/
def legalPathB (p : Params) : State → List Action → Bool
  | _, [] => true
  | s, a :: rest => decide ((step? p s a).isSome) && legalPathB p (step p s a) rest

/-- A successful boolean legality run yields a `LegalPath`. -/
theorem legalPathB_sound (p : Params) :
    ∀ (s : State) (as : List Action), legalPathB p s as = true →
      LegalPath (model p) s as
  | s, [], _ => LegalPath.nil s
  | s, a :: rest, h => by
      rw [legalPathB, Bool.and_eq_true] at h
      exact LegalPath.cons (of_decide_eq_true h.1)
        (legalPathB_sound p (step p s a) rest h.2)

theorem witness_length : witness.length = 20 := by decide +kernel
theorem witness110_length : witness110.length = 25 := by decide +kernel

/-- Every step of the baseline witness is legal. -/
theorem witness_legal : LegalPath (model baselineParams) init witness :=
  legalPathB_sound baselineParams init witness (by decide +kernel)

/-- The baseline witness reaches `trained = 1` at step 20; this is the
contract's predicted value, proved here as an upper bound only. -/
theorem witness_run :
    run (model baselineParams) init witness =
      { pop := 1, food := 1430, prog := 190, trained := 1 } := by
  decide +kernel

theorem witness_achieves : goal (run (model baselineParams) init witness) := by
  rw [witness_run]
  unfold goal
  decide +kernel

/-- Achievability at step 20 for the baseline. Minimality (`NoEarlier` at 20)
is **not** proved in this module. -/
theorem baseline_achievable : AchievableAt (model baselineParams) goal 20 :=
  AchievableAt.of_legalPath (M := model baselineParams) (goal := goal) (N := 20)
    (as := witness) witness_length witness_legal witness_achieves

/-- Cost-110 witness legality. -/
theorem witness110_legal : LegalPath (model cost110Params) init witness110 :=
  legalPathB_sound cost110Params init witness110 (by decide +kernel)

/-- Cost-110 witness final state: `11340 − 11000 = 340` overflow, food 1980. -/
theorem witness110_run :
    run (model cost110Params) init witness110 =
      { pop := 1, food := 1980, prog := 340, trained := 1 } := by
  decide +kernel

theorem witness110_achieves : goal (run (model cost110Params) init witness110) := by
  rw [witness110_run]
  unfold goal
  decide +kernel

/-- Cost-110 achievability at step 25 (upper bound only). -/
theorem cost110_achievable : AchievableAt (model cost110Params) goal 25 :=
  AchievableAt.of_legalPath (M := model cost110Params) (goal := goal) (N := 25)
    (as := witness110) witness110_length witness110_legal witness110_achieves

/-! ## 9. Kernel-checked trace facts along the witness

  These make the §10 table checkable without trusting the Python search. -/

/-- After six IDLE steps: pop 1, food 1320, no progress. -/
theorem witness_after_six :
    run (model baselineParams) init (witness.take 6) =
      { pop := 1, food := 1320, prog := 0, trained := 0 } := by
  decide +kernel

/-- The seventh step is a growth step (1540 ≥ 1500). -/
theorem witness_growth : wouldGrow { pop := 1, food := 1320, prog := 0, trained := 0 }
    (aIdle maskGH none) = true := by
  decide +kernel

/-- Growth food on the seventh step is 220. -/
theorem witness_growth_amount : growthAmount { pop := 1, food := 1320, prog := 0, trained := 0 }
    (aIdle maskGH none) = 220 := by
  decide +kernel

/-- Modified production on the growth step is 420 (400 × 1.05) in v2.1:
  `extraGain(⊥) = 0`. IDLE discards it, which is why the witness has
  `prog = 0` there. -/
theorem witness_growth_q : qOf { pop := 1, food := 1320, prog := 0, trained := 0 }
    (aIdle maskGH none) = 420 := by
  decide +kernel

/-- After the seventh step: pop 2, basket emptied, no settler progress yet. -/
theorem witness_after_seven :
    run (model baselineParams) init (witness.take 7) =
      { pop := 2, food := 0, prog := 0, trained := 0 } := by
  decide +kernel

/-- A settler step at pop 2 with GH+PH yields `q = 630`. -/
theorem witness_settler_q : qOf { pop := 2, food := 0, prog := 0, trained := 0 }
    (aSettler maskGHPH) = 630 := by
  decide +kernel

/-- The first witness action is in the *computed* legal-action enumeration. -/
theorem witness_first_mem : aIdle maskGH none ∈ legalActions init := by
  rw [mem_legalActions]
  decide +kernel

/-- The growth-step action (IDLE, no extra) is in the computed enumeration. -/
theorem witness_growth_mem :
    aIdle maskGH none ∈
      legalActions { pop := 1, food := 1320, prog := 0, trained := 0 } := by
  rw [mem_legalActions, legal_iff_guard]
  decide +kernel

/-- A pop-2 SETTLER action is in the computed enumeration. -/
theorem witness_settler_mem :
    aSettler maskGHPH ∈
      legalActions { pop := 2, food := 0, prog := 0, trained := 0 } := by
  rw [mem_legalActions]
  decide +kernel

/-- Before the final step: 12 settler steps give `prog = 7560` and food 1320. -/
theorem witness_after_nineteen :
    run (model baselineParams) init (witness.take 19) =
      { pop := 2, food := 1320, prog := 7560, trained := 0 } := by
  decide +kernel

/-- The threshold constants used by the baseline (T3 is the conditional exact
comparison bound). -/
theorem threshold_one : threshold 1 = 1500 := rfl
theorem threshold_two : threshold 2 = 2400 := rfl
theorem threshold_three : threshold 3 = 3383 := rfl

/-- With amenityStock 2, populations 1–3 are Happy: growth 110 %, non-food
105 %. This is the baseline multiplier block used by the witness. -/
theorem baseline_multipliers :
    growthMult 1 = 110 ∧ growthMult 2 = 110 ∧ growthMult 3 = 110 ∧
    prodMult 1 = 105 ∧ prodMult 2 = 105 ∧ prodMult 3 = 105 := by
  decide +kernel

/-! ## 10. Generic-engine integration smoke test

  The full lower bound at 20 would need the exact-step frontiers
  `0 … 19`; that is deliberately out of scope here. We do connect the concrete
  model to the generic `Reachable`/`NoEarlier` API at the smallest horizon. -/

theorem no_goal_at_zero (s : State) (h : Reachable (model baselineParams) 0 s) : ¬ goal s := by
  cases h with
  | zero => exact init_not_goal

/-- No goal can be reached in fewer than one step. Trivial, but it exercises the
generic `NoEarlier` definition on the concrete model. -/
theorem noEarlier_one : NoEarlier (model baselineParams) goal 1 := by
  intro t ht s hreach
  have ht0 : t = 0 := Nat.lt_one_iff.mp ht
  subst ht0
  exact no_goal_at_zero s hreach

/-- At the initial pop-1 state a SETTLER action is illegal (A8). -/
theorem legal_init_settler_impossible (a : Action) (h : legal init a) :
    a.build ≠ Build.settler := by
  intro hb
  have hp := legal_settler_pop h hb
  simp [init] at hp

/-- A legal first step from `init` cannot change `trained`: SETTLER is illegal
and IDLE credits nothing. -/
theorem step_init_trained (a : Action) (h : legal init a) :
    (step baselineParams init a).trained = init.trained := by
  have hb : a.build = Build.idle := by
    cases hb : a.build with
    | idle => rfl
    | settler => exact absurd hb (legal_init_settler_impossible a h)
  rw [step_idle_trained baselineParams init a hb]

/-- No goal is reachable in fewer than two steps. This uses the preturn-pop
guard and the IDLE zero-credit rule, not a frontier computation. -/
theorem noEarlier_two : NoEarlier (model baselineParams) goal 2 := by
  intro t ht s hreach hgoal
  have ht' : t = 0 ∨ t = 1 := by omega
  rcases ht' with rfl | rfl
  · exact no_goal_at_zero s hreach hgoal
  · cases hreach with
    | @succ t' s' a' h0 hlegal =>
        cases h0 with
        | zero =>
            have htr : (step baselineParams init a').trained = 0 := by
              simpa [legal] using step_init_trained a' hlegal
            have hgoal' : goal (step baselineParams init a') := hgoal
            simp [goal, htr] at hgoal'

/-! ## 11. Axiom audit

  Run `scripts/lean-env lake env lean Civ6Verify/Model/Mvp.lean`. Expected:
  only the ordinary core axioms `propext` and `Quot.sound` from list lemmas;
  no `sorryAx`, no `Classical.choice`, no `Lean.ofReduceBool`, no custom axiom. -/
#print axioms mem_allActions
#print axioms mem_legalActions
#print axioms workCount_le_four
#print axioms extraUnworked_spec
#print axioms legal_iff_guard
#print axioms model_legal_iff_guard
#print axioms model_legal_iff
#print axioms step_total
#print axioms step_total_of_legal
#print axioms extraGain_none
#print axioms extraGain_some
#print axioms credit_zero_of_prePop_lt_two
#print axioms step_prog
#print axioms step_idle_prog
#print axioms step_idle_trained
#print axioms step_no_growth_production
#print axioms goal_step
#print axioms goal_run
#print axioms witness_legal
#print axioms witness_run
#print axioms baseline_achievable
#print axioms witness110_legal
#print axioms witness110_run
#print axioms cost110_achievable
#print axioms witness_after_nineteen
#print axioms witness_first_mem
#print axioms witness_growth_mem
#print axioms baseline_multipliers
#print axioms witness_settler_mem
#print axioms noEarlier_one
#print axioms noEarlier_two

end Civ6Verify.Model.Mvp
