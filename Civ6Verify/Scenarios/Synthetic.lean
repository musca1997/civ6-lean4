/-
  Civ6Verify/Scenarios/Synthetic.lean

  SYNTHETIC benchmark `synthetic-v0` — **NOT Civilization VI**.

  This module kernel-checks the tiny, deliberately fake benchmark specified by
  `fixtures/synthetic-v0.json`, `search/synthetic.py` and
  `research/SYNTHETIC.md` (see also `research/SYNTHETIC-LEAN.md` for the
  cross-walk). Every constant below — growth thresholds 4 and 8, farm
  (3 food, 1 production), mine (0 food, 2 production), settler cost 8, one
  population point consumed on completion — is *invented for proof
  engineering*. Nothing here is a Civ6 formula, a Civ6 value, or a statement
  about the real game, and no result in this file is game evidence.

  Trust boundary
  --------------
  * No Mathlib. No `sorry`. No `native_decide`. No custom axioms.
  * Numeric computations are discharged with `decide +kernel`, which reduces
    the decidable proposition *inside the kernel* (unlike `native_decide`, it
    does not add `Lean.ofReduceBool` or any other axiom; `#print axioms` below
    shows only the ordinary core axioms).
  * The scenario owns only this file; the generic engine
    `Civ6Verify/Reachability/Finite.lean` is imported read-only and is not
    modified here.

  What is proved
  --------------
  1. `model : Model State Action` with an **independently defined** legality
     predicate `legal` (not "membership in the enumeration"), plus soundness
     and completeness of the computable enumeration `legalActions`.
  2. `step` is a line-by-line transcription of the Python round order (the
     growth loop is unrolled for the frozen `popMax = 2`); the fixture's own
     per-tick semantic assertions (growth-then-completion in one tick,
     prerequisite gate, food floor/cap, progress cap) are re-proved here.
  3. Exact-step frontiers (`Frontier`, the authoritative core notion) at
     `t = 0..5` have sizes `1, 2, 4, 7, 9, 10` and the fixture's contents.
  4. BFS *distance* layers recomputed here have sizes `1, 2, 4, 6, 7, 7`; the
     two notions differ and the difference is exhibited. Optimality is proved
     on the exact-step notion (`NoEarlier` quantifies over `Reachable`).
  5. `OptimalAt model goal 5` — the synthetic optimum is tick 5 — via the
     generic `checkCertificate`, plus an explicit legal trace, plus the
     "all legal sequences of length < 5 fail" corollary.
  6. Completion monotonicity and `reachable_goal_state`: every reachable goal
     state is exactly `(pop=1, food=0, prod=0, done=1)`.
  7. Exhaustive enumeration of legal action sequences of length 5: exactly one
     reaches the goal, namely the fixture witness (`optimalSequenceCount = 1`).
-/

import Civ6Verify.Reachability.Finite

namespace Civ6Verify.Scenarios.Synthetic

open Civ6Verify.Reachability

/-! ## 1. State and action types -/

/-- Synthetic state `(pop, food, production, settlersCompleted)`, all `Nat`.
Population is `1..2` on reachable states; the type itself is unbounded, which
makes the transition system total (see `step`). -/
structure State where
  /-- City population. -/
  pop : Nat
  /-- Stored food. -/
  food : Nat
  /-- Accumulated settler production. -/
  prod : Nat
  /-- Monotone count of completed settlers. -/
  done : Nat
  deriving DecidableEq, Repr

/-- Citizen assignment `(citizensOnFarm, citizensOnMine)`. Synthetic rule: two
citizens may share a tile, and every citizen works exactly one tile. -/
structure Action where
  /-- Citizens assigned to the farm tile. -/
  farm : Nat
  /-- Citizens assigned to the mine tile. -/
  mine : Nat
  deriving DecidableEq, Repr

/-! ## 2. Rule constants (v0, frozen by `fixtures/synthetic-v0.json`) -/

/-- Minimum population. -/
def popMin : Nat := 1
/-- Maximum population. -/
def popMax : Nat := 2
/-- Food eaten per citizen per tick. -/
def foodPerCitizen : Nat := 2
/-- Farm food yield. -/
def farmFood : Nat := 3
/-- Farm production yield. -/
def farmProd : Nat := 1
/-- Mine food yield. -/
def mineFood : Nat := 0
/-- Mine production yield. -/
def mineProd : Nat := 2
/-- Settler production cost. -/
def settleCost : Nat := 8
/-- Population consumed by a completed settler. -/
def settlePopCost : Nat := 1
/-- Population prerequisite for completion. -/
def prereqPop : Nat := 2
/-- Production progress cap while the prerequisite is unmet. -/
def progressCap : Nat := 7

/-- Growth threshold `T(p) = 4*p` for `p ∈ {1,2}` (linear **by design**, not a
Civ6 curve; the fixture's `growthThresholds` are `{1: 4, 2: 8}`). -/
def growthThreshold (p : Nat) : Nat := 4 * p

/-- Food cap `T(p) - 1`, i.e. `3` at `pop=1` and `7` at `pop=2`. -/
def foodCap (p : Nat) : Nat := growthThreshold p - 1

/-- The Python growth loop

```
while pop < popMax and food >= T(pop): food -= T(pop); pop += 1
```

unrolled for the frozen rules. With `popMax = 2` the loop can fire at most
once, and only at `pop = 1` (where `T(1) = 4`); `pop = 2` is at the maximum and
never grows. The fuel argument mirrors the loop bound. -/
def growthLoop : Nat → Nat → Nat → Nat × Nat
  | 0, pop, food => (pop, food)
  | fuel + 1, 1, food =>
      if 4 ≤ food then growthLoop fuel 2 (food - 4) else (1, food)
  | _, pop, food => (pop, food)

/-- Food phase: floor at `0`, run the growth loop with `popMax` fuel, then cap
stored food at `T(pop) - 1` when the population is at the maximum. -/
def foodPhase (pop food : Nat) : Nat × Nat :=
  let g := growthLoop popMax pop food
  let p := g.1
  let f := g.2
  (p, if p = popMax then min f (foodCap p) else f)

/-- Food after the food phase, before the production phase: `food + netFood`
truncated at zero (`Nat` subtraction). Net food is `3*nFarm - 2*pop`, and the
mine yields no food, matching the Python model. -/
def storedAfterFood (s : State) (a : Action) : Nat :=
  (s.food + farmFood * a.farm + mineFood * a.mine) - foodPerCitizen * s.pop

/-- Production gained in one tick: `1*nFarm + 2*nMine`. -/
def gainedProd (a : Action) : Nat := farmProd * a.farm + mineProd * a.mine

/-- One full tick, in the normative round order of `research/SYNTHETIC.md` §7:

1. read the assignment (from the tick-start state),
2. compute yields from the **pre-growth** population,
3. food phase: `food' = max(0, food + netFood)`, growth loop, cap at `T(pop)-1`,
4. production phase: `raw = production + gainedProd`,
5. prerequisite gate: `pop < 2` caps progress at `7` and forbids completion,
6. completion: `pop ≥ 2` and `raw ≥ 8` gives `done+1`, `pop-1`, `prod=0`,
   `food=0`.

`step` is total: on illegal actions it still returns *some* state, but every
theorem below quantifies over `legal` actions only. -/
def step (s : State) (a : Action) : State :=
  let F := storedAfterFood s a
  let g := foodPhase s.pop F
  let pop' := g.1
  let food' := g.2
  let raw := s.prod + gainedProd a
  if prereqPop ≤ pop' then
    if settleCost ≤ raw then
      { pop := pop' - settlePopCost, food := 0, prod := 0, done := s.done + 1 }
    else
      { pop := pop', food := food', prod := raw, done := s.done }
  else
    { pop := pop', food := food', prod := min raw progressCap, done := s.done }

/-! ## 3. Independent legality predicate, its enumeration, and the model -/

/-- **Authoritative** legality: the action must employ every citizen exactly
once (`farm + mine = pop`) and no action is legal once a settler has been
completed. Non-negativity is free because the fields are `Nat`. This predicate
is deliberately *not* defined as membership in `legalActions`. -/
def legal (s : State) (a : Action) : Prop :=
  s.done = 0 ∧ a.farm + a.mine = s.pop

instance : DecidableRel legal := fun _ _ => by
  unfold legal; infer_instance

/-- Computable enumeration `A(p) = {(k, p-k) : 0 ≤ k ≤ p}` in increasing-`k`
order, and `[]` in goal states (goal states are terminal). -/
def legalActions (s : State) : List Action :=
  if s.done = 0 then (List.range (s.pop + 1)).map (fun k => ⟨k, s.pop - k⟩) else []

/-- Every enumerated action is legal. -/
theorem legalActions_sound (s : State) (a : Action) (h : a ∈ legalActions s) :
    legal s a := by
  unfold legalActions at h
  split at h
  · rename_i hdone
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
    have hle : k ≤ s.pop := Nat.le_of_lt_succ (List.mem_range.mp hk)
    exact ⟨hdone, Nat.add_sub_of_le hle⟩
  · exact absurd h (List.not_mem_nil)

/-- Every legal action is enumerated: no branch can be silently dropped from a
frontier computation. -/
theorem legalActions_complete (s : State) (a : Action) (h : legal s a) :
    a ∈ legalActions s := by
  obtain ⟨hdone, hsum⟩ := h
  cases a with
  | mk f m =>
  dsimp only at hsum
  unfold legalActions
  rw [if_pos hdone]
  have hle : f ≤ s.pop := by omega
  have hm : m = s.pop - f := by omega
  rw [hm]
  exact List.mem_map.mpr ⟨f, List.mem_range.mpr (Nat.lt_succ_of_le hle), rfl⟩

/-- The full set of legal actions at `s` is exactly the enumeration: soundness
and completeness in one statement. -/
theorem mem_legalActions_iff (s : State) (a : Action) :
    a ∈ legalActions s ↔ legal s a :=
  ⟨legalActions_sound s a, legalActions_complete s a⟩

/-- The scenario model instance for the generic core. -/
def model : Model State Action where
  init := { pop := popMin, food := 0, prod := 0, done := 0 }
  step := step
  legal := legal
  legalDec := fun _ _ => inferInstance
  legalActions := legalActions
  legalActions_sound := legalActions_sound
  legalActions_complete := legalActions_complete

/-- The initial state, `t = 0`: `pop=1, food=0, prod=0, done=0`. -/
def init : State := model.init

/-- Goal: at least one settler has been completed (a monotone history marker,
never a queue/progress test). -/
def goal (s : State) : Prop := 1 ≤ s.done

/-- Executable goal predicate. -/
def goalB (s : State) : Bool := decide (1 ≤ s.done)

/-- `goalB` agrees with the propositional goal. -/
theorem goalB_spec (s : State) : goalB s = true ↔ goal s := by
  unfold goalB goal
  simp

/-- The fixture's `initialGoal` is `false`: the initial state is not a goal. -/
theorem initial_not_goal : ¬ goal init := by
  unfold goal init model
  decide +kernel

/-- The fixture's growth thresholds `maxFood` values: `T(1)-1 = 3` and
`T(2)-1 = 7`. -/
theorem foodCap_one : foodCap 1 = 3 := by decide +kernel
theorem foodCap_two : foodCap 2 = 7 := by decide +kernel

/-! ## 4. Completion monotonicity and terminal goal states -/

/-- The completion counter never decreases: `done` is monotone along every
step, legal or not. -/
theorem step_done_ge (s : State) (a : Action) : s.done ≤ (step s a).done := by
  rw [step]
  split <;> (try split) <;> simp

/-- One step increases the completion counter by at most one. -/
theorem step_done_le_succ (s : State) (a : Action) : (step s a).done ≤ s.done + 1 := by
  rw [step]
  split <;> (try split) <;> simp

/-- Legality forces `done = 0`; goal states are terminal. -/
theorem legal_done_eq_zero {s : State} {a : Action} (h : legal s a) : s.done = 0 := h.1

/-- No action is legal in a goal state: goal states have no outgoing actions,
so the search never expands them. -/
theorem legal_not_goal {s : State} {a : Action} (h : legal s a) : ¬ goal s := by
  have hz := legal_done_eq_zero h
  unfold goal
  omega

/-- Once the goal holds it cannot be undone by a legal step (vacuously: no legal
step exists in a goal state, which is exactly the monotone-marker shape). -/
theorem goal_monotone {s : State} {a : Action} (h : legal s a) (hg : goal s) :
    goal (step s a) :=
  absurd hg (legal_not_goal h)

/-! ## 5. Per-tick semantics: the fixture's own assertions, re-proved

Each of these mirrors an assertion of `search/synthetic.py`'s internal test
suite (`test_growth_then_production_order`, `test_prereq_gate_caps_progress`,
`test_food_floor_and_max_pop_cap`,
`test_progress_cap_while_prereq_unmet_wastes_production`). They pin the
normative round order, especially "grow and complete in the same tick". -/

/-- Growth-then-production order: one short of growth, one short of completion,
a single farm tick both grows to pop 2 and completes the settler. If
production were gated on the pre-growth population, this tick would *not*
complete. -/
theorem semantics_growth_then_completion :
    step { pop := 1, food := 3, prod := 7, done := 0 } { farm := 1, mine := 0 } =
      { pop := 1, food := 0, prod := 0, done := 1 } := by
  decide +kernel

/-- Prerequisite gate: at pop 1 with 7/8 production, a mine tick cannot
complete (progress saturates at 7). -/
theorem semantics_prereq_gate_pop_one :
    step { pop := 1, food := 0, prod := 7, done := 0 } { farm := 0, mine := 1 } =
      { pop := 1, food := 0, prod := 7, done := 0 } := by
  decide +kernel

/-- The same production at pop 2 does complete. -/
theorem semantics_prereq_gate_pop_two :
    step { pop := 2, food := 0, prod := 7, done := 0 } { farm := 0, mine := 2 } =
      { pop := 1, food := 0, prod := 0, done := 1 } := by
  decide +kernel

/-- Two mines at pop 2: net food `-4` floors at `0`, production `+4`. -/
theorem semantics_food_floor :
    step { pop := 2, food := 0, prod := 0, done := 0 } { farm := 0, mine := 2 } =
      { pop := 2, food := 0, prod := 4, done := 0 } := by
  decide +kernel

/-- At max population, surplus food beyond `T(2)-1 = 7` is discarded. -/
theorem semantics_food_cap :
    step { pop := 2, food := 5, prod := 0, done := 0 } { farm := 2, mine := 0 } =
      { pop := 2, food := 7, prod := 2, done := 0 } := by
  decide +kernel

/-- Growth carries the (zero) overflow and farms also bank 1 production. -/
theorem semantics_growth_overflow :
    step { pop := 1, food := 3, prod := 0, done := 0 } { farm := 1, mine := 0 } =
      { pop := 2, food := 0, prod := 1, done := 0 } := by
  decide +kernel

/-- While the prerequisite is unmet, production above `cost-1 = 7` is wasted,
not banked. -/
theorem semantics_progress_cap :
    step { pop := 1, food := 0, prod := 6, done := 0 } { farm := 0, mine := 1 } =
      { pop := 1, food := 0, prod := 7, done := 0 } := by
  decide +kernel

theorem semantics_progress_cap_at_cap :
    step { pop := 1, food := 0, prod := 7, done := 0 } { farm := 0, mine := 1 } =
      { pop := 1, food := 0, prod := 7, done := 0 } := by
  decide +kernel

/-! ## 6. The fixture witness and the trace of per-tick states -/

/-- The witness action sequence of `fixtures/synthetic-v0.json`
(`expected.witness`): four ticks with the single citizen on the farm, then two
citizens on the mine. -/
def witness : List Action :=
  [{ farm := 1, mine := 0 }, { farm := 1, mine := 0 }, { farm := 1, mine := 0 },
   { farm := 1, mine := 0 }, { farm := 0, mine := 2 }]

/-- The fixture's `expected.witnessStates`: states at ticks `0..5`. -/
def witnessStates : List State :=
  [{ pop := 1, food := 0, prod := 0, done := 0 },
   { pop := 1, food := 1, prod := 1, done := 0 },
   { pop := 1, food := 2, prod := 2, done := 0 },
   { pop := 1, food := 3, prod := 3, done := 0 },
   { pop := 2, food := 0, prod := 4, done := 0 },
   { pop := 1, food := 0, prod := 0, done := 1 }]

/-- States reached by replaying the first `k` witness actions, `k = 0..5`. -/
def witnessTrace : List State :=
  (List.range 6).map (fun k => run model init (witness.take k))

/-- Every action of the witness is legal at the state where it is played. -/
theorem witness_legal : LegalPath model init witness := by
  refine LegalPath.cons (s := init) ?_ (LegalPath.cons ?_ (LegalPath.cons ?_
    (LegalPath.cons ?_ (LegalPath.cons ?_ (LegalPath.nil _)))))
  all_goals decide +kernel

/-- Replaying the witness yields exactly the fixture's final goal state. -/
theorem witness_run : run model init witness =
    { pop := 1, food := 0, prod := 0, done := 1 } := by
  decide +kernel

/-- The per-tick trace of the witness is exactly the fixture's
`expected.witnessStates`, including the pop-2 transient at tick 4. -/
theorem witness_trace_eq : witnessTrace = witnessStates := by
  decide +kernel

/-- The witness reaches the goal. -/
theorem witness_achieves : goal (run model init witness) := by
  rw [witness_run]
  unfold goal
  decide +kernel

/-- Upper bound: tick 5 is achievable, exhibited by an explicit legal trace. -/
theorem achievable_at_five : AchievableAt model goal 5 :=
  AchievableAt.of_legalPath (M := model) (goal := goal) (N := 5) (as := witness)
    rfl witness_legal witness_achieves

/-! ## 7. Exact-step frontiers (the core notion)

`Frontier M t` keeps states reachable in **exactly** `t` steps: revisiting an
earlier state at a later tick is a *new* member. The lists below are the Lean
counterpart of `expected.exactStepFrontiers` (the fixture lists them sorted; the
order below is the enumeration order produced by `dedup`). -/

/-- Exact-step frontier at `t = 0`. -/
theorem frontier_zero_eq : Frontier model 0 = [{ pop := 1, food := 0, prod := 0, done := 0 }] := by
  decide +kernel

/-- Exact-step frontier at `t = 1`. -/
theorem frontier_one_eq : Frontier model 1 =
    [{ pop := 1, food := 0, prod := 2, done := 0 },
     { pop := 1, food := 1, prod := 1, done := 0 }] := by decide +kernel

/-- Exact-step frontier at `t = 2`. -/
theorem frontier_two_eq : Frontier model 2 =
    [{ pop := 1, food := 0, prod := 4, done := 0 },
     { pop := 1, food := 1, prod := 3, done := 0 },
     { pop := 1, food := 0, prod := 3, done := 0 },
     { pop := 1, food := 2, prod := 2, done := 0 }] := by decide +kernel

/-- Exact-step frontier at `t = 3`. -/
theorem frontier_three_eq : Frontier model 3 =
    [{ pop := 1, food := 0, prod := 6, done := 0 },
     { pop := 1, food := 1, prod := 5, done := 0 },
     { pop := 1, food := 0, prod := 5, done := 0 },
     { pop := 1, food := 2, prod := 4, done := 0 },
     { pop := 1, food := 1, prod := 4, done := 0 },
     { pop := 1, food := 0, prod := 4, done := 0 },
     { pop := 1, food := 3, prod := 3, done := 0 }] := by decide +kernel

/-- Exact-step frontier at `t = 4`. -/
theorem frontier_four_eq : Frontier model 4 =
    [{ pop := 1, food := 0, prod := 7, done := 0 },
     { pop := 1, food := 1, prod := 7, done := 0 },
     { pop := 1, food := 2, prod := 6, done := 0 },
     { pop := 1, food := 1, prod := 6, done := 0 },
     { pop := 1, food := 0, prod := 6, done := 0 },
     { pop := 1, food := 3, prod := 5, done := 0 },
     { pop := 1, food := 2, prod := 5, done := 0 },
     { pop := 1, food := 1, prod := 5, done := 0 },
     { pop := 2, food := 0, prod := 4, done := 0 }] := by decide +kernel

/-- Exact-step frontier at `t = 5`; it contains the unique goal state. -/
theorem frontier_five_eq : Frontier model 5 =
    [{ pop := 1, food := 0, prod := 7, done := 0 },
     { pop := 1, food := 1, prod := 7, done := 0 },
     { pop := 1, food := 2, prod := 7, done := 0 },
     { pop := 1, food := 3, prod := 7, done := 0 },
     { pop := 2, food := 0, prod := 6, done := 0 },
     { pop := 1, food := 3, prod := 6, done := 0 },
     { pop := 1, food := 2, prod := 6, done := 0 },
     { pop := 1, food := 0, prod := 0, done := 1 },
     { pop := 2, food := 0, prod := 7, done := 0 },
     { pop := 2, food := 2, prod := 6, done := 0 }] := by decide +kernel

/-- Exact-step frontier sizes `t = 0..5`: `1, 2, 4, 7, 9, 10`. This matches
`expected.exactStepFrontierCounts` and is **not** the distance-layer size. -/
theorem frontier_counts :
    (List.range 6).map (fun t => (Frontier model t).length) = [1, 2, 4, 7, 9, 10] := by
  decide +kernel

/-- Individual size statements, for readability. -/
theorem frontier_length_zero : (Frontier model 0).length = 1 := by decide +kernel
theorem frontier_length_one : (Frontier model 1).length = 2 := by decide +kernel
theorem frontier_length_two : (Frontier model 2).length = 4 := by decide +kernel
theorem frontier_length_three : (Frontier model 3).length = 7 := by decide +kernel
theorem frontier_length_four : (Frontier model 4).length = 9 := by decide +kernel
theorem frontier_length_five : (Frontier model 5).length = 10 := by decide +kernel

/-- Every state of the exact frontier at `t ≤ 5` satisfies the fixture's
canonical state invariants `1 ≤ pop ≤ 2`, `food ≤ T(pop)-1`, `prod ≤ 7`,
`done ≤ 1`. -/
theorem frontier_invariants_upto_five :
    (List.range 6).all (fun t =>
      (Frontier model t).all (fun s =>
        decide (1 ≤ s.pop ∧ s.pop ≤ 2 ∧ s.food ≤ foodCap s.pop ∧ s.prod ≤ progressCap ∧
          s.done ≤ 1))) = true := by
  decide +kernel

/-! ## 8. Optimality at tick 5, via the generic certificate -/

/-- The boolean certificate passes at `N = 5`: no goal state in frontiers
`0..4`, and a goal state in frontier `5`. -/
theorem checkCertificate_five : checkCertificate model goalB 5 = true := by decide +kernel

/-- **The synthetic optimum is tick 5** (synthetic benchmark only; not a Civ6
claim). Proved by the generic `optimalAt_of_checkCertificate`: the lower bound
and the upper bound both come from kernel-computed exact-step frontiers. -/
theorem optimalAt_five : OptimalAt model goal 5 :=
  optimalAt_of_checkCertificate (M := model) goalB goalB_spec checkCertificate_five

/-- Cross-check through the scan form of the certificate. -/
theorem earliestGoalTick_five : earliestGoalTick? model goalB 8 = some 5 := by decide +kernel

/-- The scan-form certificate yields the same optimality statement. -/
theorem optimalAt_five' : OptimalAt model goal 5 :=
  optimalAt_of_earliestGoalTick? (M := model) goalB goalB_spec earliestGoalTick_five

/-- No goal state occurs in frontiers `0..4`, in `Frontier` form. -/
theorem no_goal_below_five :
    ∀ t, t < 5 → ∀ s ∈ Frontier model t, goalB s = false :=
  (noEarlier_iff_no_goal_in_frontier (M := model) goalB goalB_spec 5).mp
    optimalAt_five.2

/-- Consequently no legal action sequence of length `< 5` reaches the goal,
quantified over *all* legal sequences (not just enumerated ones). -/
theorem no_legal_path_below_five {as : List Action} (hlen : as.length < 5)
    (hpath : LegalPath model init as) : ¬ goal (run model init as) :=
  (noEarlier_iff_all_legalPaths (M := model) (goal := goal) (N := 5)).mp
    optimalAt_five.2 as hlen hpath

/-- No tick below 5 is achievable, so the bound is tight. -/
theorem not_achievable_below_five : ∀ t, t < 5 → ¬ AchievableAt model goal t :=
  optimalAt_five.not_achievable_before

/-- The goal state found in frontier 5 is the fixture's unique completion state. -/
theorem witnessAt_five :
    witnessAt model goalB 5 = some { pop := 1, food := 0, prod := 0, done := 1 } := by
  decide +kernel

/-- The frontier at 5 does contain a goal state. -/
theorem frontier_five_has_goal : ∃ s ∈ Frontier model 5, goalB s = true := by
  refine ⟨{ pop := 1, food := 0, prod := 0, done := 1 }, ?_, by decide +kernel⟩
  rw [frontier_five_eq]
  simp

/-- The goal state at tick 5 is unique: exactly one frontier member satisfies
the goal (the fixture's `goalStatesAtOptimum` has a single entry). -/
theorem frontier_five_goal_unique :
    (Frontier model 5).filter goalB = [{ pop := 1, food := 0, prod := 0, done := 1 }] := by
  decide +kernel

/-! ## 9. Exact steps vs BFS distance: the distinction

`Frontier` allows revisiting a state at a later tick. The search in
`search/synthetic.py` instead keeps only the *earliest* tick (a global visited
set), producing **distance layers**. The two notions have different sizes from
`t = 3` on, and this file formalizes both so they cannot be confused:

* exact-step sizes (`frontier_counts`): `1, 2, 4, 7, 9, 10`,
* distance-layer sizes (`distLayer_counts`): `1, 2, 4, 6, 7, 7`.

Optimality is established on the exact-step notion, which is the authoritative
one: `NoEarlier` quantifies over `Reachable` (exact steps).
-/

/-- One BFS step: successors of `cur` that have never been seen. `seen` holds
all states of the previous layers. Goal states contribute no successors because
`legalActions` is empty for them. -/
def bfsStep (cur seen : List State) : List State :=
  (dedup (cur.flatMap (successors model))).filter (fun s => decide (s ∉ seen ++ cur))

/-- Distance-layer iteration: `distAux t cur seen` is the layer `t` steps after
`cur`, with `seen` the already-visited states. -/
def distAux : Nat → List State → List State → List State
  | 0, cur, _ => cur
  | t + 1, cur, seen =>
      let cur' := bfsStep cur seen
      distAux t cur' (seen ++ cur)

/-- The BFS distance layer at tick `t` (states whose earliest reachable tick is
exactly `t`). -/
def distLayer (t : Nat) : List State := distAux t [init] []

/-- `distLayer` at `t = 0..5` has sizes `1, 2, 4, 6, 7, 7`, matching the
fixture's `distanceLayerCounts` / `layerCounts`. -/
theorem distLayer_counts :
    (List.range 6).map (fun t => (distLayer t).length) = [1, 2, 4, 6, 7, 7] := by
  decide +kernel

/-- Distance layer at `t = 0`. -/
theorem distLayer_zero_eq : distLayer 0 = [{ pop := 1, food := 0, prod := 0, done := 0 }] := by
  decide +kernel

/-- Distance layer at `t = 1`. -/
theorem distLayer_one_eq : distLayer 1 =
    [{ pop := 1, food := 0, prod := 2, done := 0 },
     { pop := 1, food := 1, prod := 1, done := 0 }] := by decide +kernel

/-- Distance layer at `t = 3` — note the absence of `(1,0,4,0)`, which is
already at distance 2. -/
theorem distLayer_three_eq : distLayer 3 =
    [{ pop := 1, food := 0, prod := 6, done := 0 },
     { pop := 1, food := 1, prod := 5, done := 0 },
     { pop := 1, food := 0, prod := 5, done := 0 },
     { pop := 1, food := 2, prod := 4, done := 0 },
     { pop := 1, food := 1, prod := 4, done := 0 },
     { pop := 1, food := 3, prod := 3, done := 0 }] := by decide +kernel

/-- Distance layer at `t = 2` (same set as the fixture's `reachableLayers[2]`,
in enumeration order). -/
theorem distLayer_two_eq : distLayer 2 =
    [{ pop := 1, food := 0, prod := 4, done := 0 },
     { pop := 1, food := 1, prod := 3, done := 0 },
     { pop := 1, food := 0, prod := 3, done := 0 },
     { pop := 1, food := 2, prod := 2, done := 0 }] := by decide +kernel

/-- Distance layer at `t = 4`. -/
theorem distLayer_four_eq : distLayer 4 =
    [{ pop := 1, food := 0, prod := 7, done := 0 },
     { pop := 1, food := 1, prod := 7, done := 0 },
     { pop := 1, food := 2, prod := 6, done := 0 },
     { pop := 1, food := 1, prod := 6, done := 0 },
     { pop := 1, food := 3, prod := 5, done := 0 },
     { pop := 1, food := 2, prod := 5, done := 0 },
     { pop := 2, food := 0, prod := 4, done := 0 }] := by decide +kernel

/-- Distance layer at `t = 5`: it contains the unique goal state, in contrast
with the exact frontier, which additionally repeats `(1,0,7,0)`, `(1,1,7,0)`
and `(1,2,6,0)`. -/
theorem distLayer_five_eq : distLayer 5 =
    [{ pop := 1, food := 2, prod := 7, done := 0 },
     { pop := 1, food := 3, prod := 7, done := 0 },
     { pop := 2, food := 0, prod := 6, done := 0 },
     { pop := 1, food := 3, prod := 6, done := 0 },
     { pop := 1, food := 0, prod := 0, done := 1 },
     { pop := 2, food := 0, prod := 7, done := 0 },
     { pop := 2, food := 2, prod := 6, done := 0 }] := by decide +kernel

/-- The distance-layer members are exact-step reachable at the same tick, so
the BFS layers refine the exact frontiers. -/
theorem distAux_subset : ∀ (t base : Nat) (cur seen : List State),
    (∀ s, s ∈ cur → s ∈ Frontier model base) →
    ∀ s, s ∈ distAux t cur seen → s ∈ Frontier model (base + t)
  | 0, base, cur, seen, h, s, hs => by
      simpa using h s hs
  | t + 1, base, cur, seen, h, s, hs => by
      have hnext : ∀ s', s' ∈ bfsStep cur seen → s' ∈ Frontier model (base + 1) := by
        intro s' hs'
        have hmem : s' ∈ dedup (cur.flatMap (successors model)) :=
          (List.mem_filter.mp hs').1
        rw [mem_dedup] at hmem
        obtain ⟨p, hp, hsp⟩ := List.mem_flatMap.mp hmem
        obtain ⟨a, ha, hstep⟩ := mem_successors.mp hsp
        rw [frontier_succ, mem_dedup, List.mem_flatMap]
        exact ⟨p, h p hp, mem_successors.mpr ⟨a, ha, hstep⟩⟩
      have hrec := distAux_subset t (base + 1) (bfsStep cur seen) (seen ++ cur) hnext s hs
      have heq : base + (t + 1) = base + 1 + t := by omega
      rwa [heq]

/-- Every BFS distance layer is contained in the corresponding exact-step
frontier. The containment is strict from `t = 3` (next theorem). -/
theorem distLayer_subset_frontier (t : Nat) (s : State) (hs : s ∈ distLayer t) :
    s ∈ Frontier model t := by
  have := distAux_subset t 0 [init] [] (fun s' hs' => by
    have he : s' = init := by simpa using hs'
    rw [he, frontier_zero_eq]
    decide +kernel) s hs
  simpa using this

/-- **The distinction, exhibited**: `(1,0,4,0)` is reachable in exactly 3 steps
(it is in `Frontier 3`) but its earliest tick is 2, so it is not in distance
layer 3. Asserting the exact frontier sizes to be `[1,2,4,6,7,7]` would be a
semantic error. -/
theorem exact_step_not_distance :
    ({ pop := 1, food := 0, prod := 4, done := 0 } : State) ∈ Frontier model 3 ∧
      ({ pop := 1, food := 0, prod := 4, done := 0 } : State) ∉ distLayer 3 := by
  constructor
  · rw [frontier_three_eq]; simp
  · rw [distLayer_three_eq]; decide +kernel

/-- The distinction at the optimum tick: `(1,0,7,0)` is exactly-5-step
reachable (a revisit of a distance-4 state) but not a distance-5 state. -/
theorem exact_step_not_distance_five :
    ({ pop := 1, food := 0, prod := 7, done := 0 } : State) ∈ Frontier model 5 ∧
      ({ pop := 1, food := 0, prod := 7, done := 0 } : State) ∉ distLayer 5 := by
  constructor
  · rw [frontier_five_eq]; simp
  · rw [distLayer_five_eq]; decide +kernel

/-- **Every** BFS distance layer below tick 5 is goal-free.

Note the polarity: `(List.range 5).all (fun t => !((distLayer t).any goalB))`
asserts that *all* of the layers `0..4` fail to contain a goal. The weaker
`(List.range 5).all (fun t => (distLayer t).any goalB) = false` would only say
"not every layer contains a goal" (true as soon as layer 0 is goal-free) and
does **not** express this property; it is deliberately not used. -/
theorem distLayer_no_goal_below_five :
    (List.range 5).all (fun t => !((distLayer t).any goalB)) = true := by
  decide +kernel

/-- Pointwise form of `distLayer_no_goal_below_five`: for every `t < 5`, the BFS
distance layer at `t` contains no goal state. -/
theorem distLayer_no_goal_below_five' (t : Nat) (ht : t < 5) :
    (distLayer t).any goalB = false := by
  have h := (List.all_eq_true.mp distLayer_no_goal_below_five) t (List.mem_range.mpr ht)
  exact (not_eq_true_iff_eq_false _).mp h

/-- The goal flag of each BFS distance layer at `t = 0..5`, explicitly: only
tick 5 contains a goal state. This is the unambiguously quantified form of the
distance-layer side of the optimality claim. -/
theorem distLayer_goal_flags :
    (List.range 6).map (fun t => (distLayer t).any goalB) =
      [false, false, false, false, false, true] := by
  decide +kernel

/-- The BFS distance layer at tick 5 does contain the goal state. -/
theorem distLayer_five_goal : (distLayer 5).any goalB = true := by
  decide +kernel

/-! ## 10. Reachable-state invariants and uniqueness of the completion state -/

/-- Closed form of the food phase at `pop = 1`. -/
theorem foodPhase_one (f : Nat) :
    foodPhase 1 f = if 4 ≤ f then (2, min (f - 4) 7) else (1, f) := by
  simp only [foodPhase, growthLoop, popMax, growthThreshold, foodCap]
  by_cases h : 4 ≤ f <;> simp [h]

/-- Closed form of the food phase at `pop = 2`. -/
theorem foodPhase_two (f : Nat) : foodPhase 2 f = (2, min f 7) := rfl

/-- The food phase never leaves the population range `1..2`. -/
theorem foodPhase_pop_bounds {p f : Nat} (h1 : 1 ≤ p) (h2 : p ≤ 2) :
    1 ≤ (foodPhase p f).1 ∧ (foodPhase p f).1 ≤ 2 := by
  have hp : p = 1 ∨ p = 2 := by omega
  rcases hp with rfl | rfl
  · rw [foodPhase_one]; split <;> simp
  · rw [foodPhase_two]; simp

/-- One step preserves the population range `1..2`. -/
theorem step_pop_bounds {s : State} {a : Action} (h1 : 1 ≤ s.pop) (h2 : s.pop ≤ 2) :
    1 ≤ (step s a).pop ∧ (step s a).pop ≤ 2 := by
  rw [step]
  split
  · rename_i hgate
    simp only [prereqPop] at hgate
    split
    · have hb := foodPhase_pop_bounds (p := s.pop) (f := storedAfterFood s a) h1 h2
      obtain ⟨hb1, hb2⟩ := hb
      have h2' : (foodPhase s.pop (storedAfterFood s a)).1 = 2 := Nat.le_antisymm hb2 hgate
      rw [h2']
      simp only [settlePopCost]
      exact ⟨by decide, by decide⟩
    · exact foodPhase_pop_bounds (p := s.pop) (f := storedAfterFood s a) h1 h2
  · exact foodPhase_pop_bounds (p := s.pop) (f := storedAfterFood s a) h1 h2

/-- Every reachable state has population in `1..2` (Python's `check_state`
invariant, proved here for reachable states). -/
theorem reachable_pop_bounds {t : Nat} {s : State} (h : Reachable model t s) :
    1 ≤ s.pop ∧ s.pop ≤ 2 := by
  induction h with
  | zero => decide +kernel
  | succ hreach hlegal ih => exact step_pop_bounds ih.1 ih.2

/-- Every reachable state satisfies `done ≤ 1`: completion happens at most once
within any reachable horizon, because goal states have no legal actions. -/
theorem reachable_done_le_one {t : Nat} {s : State} (h : Reachable model t s) :
    s.done ≤ 1 := by
  induction h with
  | zero => decide +kernel
  | @succ t p a hreach hlegal ih =>
      have hp : p.done = 0 := hlegal.1
      have hle := step_done_le_succ p a
      show (step p a).done ≤ 1
      omega

/-- A step that raises the completion counter is exactly the completion branch:
population `pop'-1 = 1`, food and production reset to zero, `done = 1`. -/
theorem step_goal_shape {s : State} {a : Action}
    (h1 : 1 ≤ s.pop) (h2 : s.pop ≤ 2) (hdone : s.done = 0)
    (hg : 1 ≤ (step s a).done) :
    step s a = { pop := 1, food := 0, prod := 0, done := 1 } := by
  rw [step] at hg ⊢
  split
  · rename_i hgate
    rw [if_pos hgate] at hg
    split
    · rename_i hcomp
      have hb := foodPhase_pop_bounds (p := s.pop) (f := storedAfterFood s a) h1 h2
      obtain ⟨hb1, hb2⟩ := hb
      simp only [prereqPop] at hgate
      have hpop' : (foodPhase s.pop (storedAfterFood s a)).1 = 2 := Nat.le_antisymm hb2 hgate
      rw [hpop']
      simp only [settlePopCost, hdone]
    · rename_i hcomp
      rw [if_neg hcomp] at hg
      rw [hdone] at hg
      omega
  · rename_i hgate
    rw [if_neg hgate] at hg
    rw [hdone] at hg
    omega

/-- **`completion_unique`**: every reachable goal state is exactly
`(pop=1, food=0, prod=0, done=1)`. Consequently the only state where the goal
can fire is the fixture's `completionStateKey` `pop=1;food=0;prod=0;done=1`. -/
theorem reachable_goal_state {t : Nat} {s : State} (h : Reachable model t s)
    (hg : 1 ≤ s.done) : s = { pop := 1, food := 0, prod := 0, done := 1 } := by
  induction h with
  | zero => simp [model] at hg
  | @succ t p a hreach hlegal ih =>
      exact step_goal_shape (reachable_pop_bounds hreach).1 (reachable_pop_bounds hreach).2
        hlegal.1 hg

/-- The completion state is reachable only at ticks `t ≥ 5` (restating the
lower bound as a property of the single goal state). -/
theorem completion_state_only_from_five {t : Nat}
    (h : Reachable model t { pop := 1, food := 0, prod := 0, done := 1 }) : 5 ≤ t := by
  apply Nat.le_of_not_lt
  intro hlt
  have hb : goalB { pop := 1, food := 0, prod := 0, done := 1 } = false :=
    no_goal_below_five t hlt _ ((mem_frontier_iff t _).mpr h)
  exact absurd hb (by decide +kernel)

/-! ## 11. Exhaustive legal-sequence enumeration

`search/synthetic.py` reports `optimalSequenceCount = 1`. To state that over
*all* legal sequences (not only enumerated ones), sequences are enumerated by
prepending each legal action and recursing from the successor state; soundness
and completeness of that enumeration are proved. -/

/-- All legal action sequences of length `t` starting from `s`, built by
prepending legal actions. -/
def sequencesFrom (s : State) : Nat → List (List Action)
  | 0 => [[]]
  | t + 1 =>
      (legalActions s).flatMap
        (fun a => (sequencesFrom (step s a) t).map (fun rest => a :: rest))

/-- All legal action sequences of length `t` from the initial state. -/
def actionSequences (t : Nat) : List (List Action) := sequencesFrom init t

/-- **Soundness and completeness** of the sequence enumeration: a list is
enumerated exactly when it is a legal path of that length. -/
theorem mem_sequencesFrom (s : State) (t : Nat) (as : List Action) :
    as ∈ sequencesFrom s t ↔ as.length = t ∧ LegalPath model s as := by
  induction t generalizing as s with
  | zero =>
      constructor
      · intro h
        rcases List.mem_cons.mp h with h' | h'
        · subst h'
          exact ⟨rfl, LegalPath.nil s⟩
        · exact absurd h' (List.not_mem_nil)
      · rintro ⟨hlen, hpath⟩
        have has : as = [] := List.eq_nil_of_length_eq_zero hlen
        subst has
        exact List.mem_cons_self (l := [])
  | succ t ih =>
      constructor
      · intro h
        obtain ⟨a, ha, has⟩ := List.mem_flatMap.mp h
        obtain ⟨rest, hrest, rfl⟩ := List.mem_map.mp has
        obtain ⟨hlen, hpath⟩ := (ih (step s a) rest).mp hrest
        refine ⟨?_, LegalPath.cons (legalActions_sound s a ha) hpath⟩
        rw [List.length_cons, hlen]
      · rintro ⟨hlen, hpath⟩
        cases as with
        | nil => exact absurd hlen (Nat.noConfusion hlen)
        | cons a rest =>
            cases hpath with
            | cons hlegal hrest =>
                have hlen' : rest.length = t := by
                  rw [List.length_cons] at hlen
                  exact Nat.succ.inj hlen
                have hrest' := (ih (step s a) rest).mpr ⟨hlen', hrest⟩
                exact List.mem_flatMap.mpr
                  ⟨a, legalActions_complete s a hlegal,
                    List.mem_map.mpr ⟨rest, hrest', rfl⟩⟩

/-- The enumeration at length 5 from the initial state is complete for legal
paths. -/
theorem mem_actionSequences {as : List Action} :
    as ∈ actionSequences as.length ↔ LegalPath model init as := by
  rw [actionSequences, mem_sequencesFrom]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- There are exactly 33 legal 5-step sequences: 15 four-step prefixes end at
`pop = 1` (2 legal actions each) and the single all-farm prefix `(1,0)^4` ends
at `pop = 2` (3 legal actions), so `15*2 + 3 = 33`. -/
theorem legalSequences_five_count : (actionSequences 5).length = 33 := by
  decide +kernel

/-- Exhaustive check over all 33 legal 5-step sequences: the only one that
reaches a goal state is the fixture witness. Kernel-checked by enumeration. -/
theorem actionSequences_five_goals :
    (actionSequences 5).filter (fun as => goalB (run model init as)) = [witness] := by
  decide +kernel

/-- The fixture's `optimalSequenceCount = 1`, as an exhaustive count. -/
theorem optimalSequenceCount :
    ((actionSequences 5).filter (fun as => goalB (run model init as))).length = 1 := by
  rw [actionSequences_five_goals]
  rfl

/-- **Uniqueness over all legal sequences**: every legal 5-step sequence that
reaches the goal is the witness. This is stronger than the enumeration check
alone, because `mem_sequencesFrom` proves the enumeration has no gaps. -/
theorem unique_optimal_sequence {as : List Action} (hlen : as.length = 5)
    (hpath : LegalPath model init as) (hgoal : goal (run model init as)) :
    as = witness := by
  have hmem : as ∈ actionSequences 5 := by
    rw [← hlen]
    exact mem_actionSequences.mpr hpath
  have hfilter : as ∈ (actionSequences 5).filter (fun as => goalB (run model init as)) :=
    List.mem_filter.mpr ⟨hmem, (goalB_spec _).mpr hgoal⟩
  rw [actionSequences_five_goals] at hfilter
  rcases List.mem_cons.mp hfilter with h' | h'
  · exact h'
  · exact absurd h' (List.not_mem_nil)

/-- There is at least one optimal sequence, so the count above is exactly 1. -/
theorem witness_mem_actionSequences : witness ∈ actionSequences 5 := by
  have h := mem_actionSequences.mpr witness_legal
  rwa [show witness.length = 5 from rfl] at h

/-! ## 12. Frozen fixture scale numbers

These are the fixture's `distinctStatesTotal`, `expandedTransitions`,
`cartesianStateUpperBound` and `completionReachableUpperBound`, recomputed from
the model. They are bookkeeping facts about the synthetic state space, not game
content. -/

/-- 27 distinct states are reachable within ticks `0..5`. -/
theorem distinctStatesTotal :
    (dedup ((List.range 6).flatMap (fun t => Frontier model t))).length = 27 := by
  decide +kernel

/-- BFS expands exactly 41 `(state, action)` pairs when searching ticks `0..4`
(the goal tick 5 is never expanded). -/
theorem expandedTransitions :
    (List.range 5).foldl
      (fun acc t => acc + (distLayer t).foldl (fun acc s => acc + (legalActions s).length) 0) 0
      = 41 := by
  decide +kernel

/-- Cartesian upper bound `2 * Σ_p (maxFood p + 1) * cost = 192`. -/
theorem cartesianStateUpperBound :
    2 * ((List.range 2).foldl
      (fun acc i => acc + (foodCap (i + 1) + 1) * settleCost) 0) = 192 := by
  decide +kernel

/-- Completion-reachable upper bound `Σ_p (maxFood p + 1) * cost + 1 = 97`. -/
theorem completionReachableUpperBound :
    (List.range 2).foldl (fun acc i => acc + (foodCap (i + 1) + 1) * settleCost) 0 + 1
      = 97 := by
  decide +kernel

/-! ## 13. Axiom audit

The build command is

```
scripts/lean-env lake build Civ6Verify.Reachability.Finite
scripts/lean-env lake env lean Civ6Verify/Scenarios/Synthetic.lean
```

Expected output: `does not depend on any axioms` for the scenario theorems
(possibly `propext` / `Quot.sound` for theorems routed through the generic
engine's list lemmas — those are the ordinary core axioms, and in particular
there is no `sorryAx` and no `Lean.ofReduceBool`). -/
#print axioms legalActions_sound
#print axioms legalActions_complete
#print axioms initial_not_goal
#print axioms semantics_growth_then_completion
#print axioms witness_legal
#print axioms witness_run
#print axioms step_done_ge
#print axioms reachable_pop_bounds
#print axioms witness_trace_eq
#print axioms frontier_counts
#print axioms checkCertificate_five
#print axioms optimalAt_five
#print axioms optimalAt_five'
#print axioms no_legal_path_below_five
#print axioms distLayer_counts
#print axioms distLayer_no_goal_below_five
#print axioms distLayer_no_goal_below_five'
#print axioms distLayer_goal_flags
#print axioms distLayer_subset_frontier
#print axioms exact_step_not_distance
#print axioms exact_step_not_distance_five
#print axioms frontier_five_goal_unique
#print axioms reachable_goal_state
#print axioms completion_state_only_from_five
#print axioms mem_sequencesFrom
#print axioms legalSequences_five_count
#print axioms actionSequences_five_goals
#print axioms optimalSequenceCount
#print axioms unique_optimal_sequence
#print axioms distinctStatesTotal
#print axioms expandedTransitions

end Civ6Verify.Scenarios.Synthetic
