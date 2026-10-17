/-
  Civ6Verify/Reachability/Finite.lean

  Generic, kernel-checked finite-horizon reachability / optimality core.

  This module contains **no Civilization VI rules**. It is the reusable engine
  that scenario modules instantiate with a concrete `State`, `Action`, `step`,
  `legal` predicate and a *sound and complete* legal-action enumeration.

  Trust boundary
  --------------
  * No Mathlib, no `sorry`, no custom axioms, no `native_decide`.
  * Everything below is checked by Lean's kernel; the executable frontier
    functions are ordinary definitions and their specifications are theorems.
  * The only "modelling" assumptions are the fields of `Model`, in particular
    `legalActions_sound` / `legalActions_complete`. A scenario that fails to
    enumerate every legal action cannot use the lower-bound theorems: the
    completeness field is a proof obligation, not an axiom.

  Internal time convention (PLAN.md §2.1): `t = 0` is the initial state and
  `t = k` is the state after exactly `k` turn resolutions.
-/

namespace Civ6Verify.Reachability

universe u v

/-- A finite-horizon turn model.

  `State` and `Action` need not be finite types: only the horizon is finite.
  `legalActions s` is the scenario's action enumeration at `s`; the two
  soundness/completeness fields tie it to the independently defined `legal`
  predicate. Every lower-bound theorem in this file quantifies over `legal`
  actions (through `ReachableFrom`), so replacing `legalActions` by a smaller
  list can never make an unsound lower bound pass without also proving the
  (false) completeness field. -/
class Model (State : Type u) (Action : Type v) where
  /-- The scenario's initial state (`t = 0`). -/
  init : State
  /-- One turn resolution: apply one action and advance the clock by one. -/
  step : State → Action → State
  /-- The authoritative legality predicate. -/
  legal : State → Action → Prop
  /-- Legality is decidable, so scenarios can compute and `decide` about it. -/
  legalDec : (s : State) → (a : Action) → Decidable (legal s a)
  /-- The computable action enumeration used to build frontiers. -/
  legalActions : State → List Action
  /-- Every enumerated action is legal. -/
  legalActions_sound : ∀ (s : State) (a : Action), a ∈ legalActions s → legal s a
  /-- Every legal action is enumerated. This is what makes a missing branch a
  proof failure rather than a silently weaker lower bound. -/
  legalActions_complete : ∀ (s : State) (a : Action), legal s a → a ∈ legalActions s

/-- Use the model's decidability of `legal` as the ambient instance. Low
priority so that a scenario may override it if it has a cheaper decision
procedure. -/
instance (priority := 100) instDecidableLegal {State : Type u} {Action : Type v}
    [Model State Action] (s : State) (a : Action) : Decidable (Model.legal s a) :=
  Model.legalDec s a

/-- Exact-step reachability from an arbitrary start state. `ReachableFrom M s t s'`
means: starting at `s`, after exactly `t` legal turn resolutions the state is
`s'`. -/
inductive ReachableFrom {State : Type u} {Action : Type v} (M : Model State Action)
    (start : State) : Nat → State → Prop where
  /-- Zero resolutions: the state is unchanged. -/
  | zero : ReachableFrom M start 0 start
  /-- One more legal action, then the remaining path. -/
  | succ {t : Nat} {s : State} {a : Action} :
      ReachableFrom M start t s → M.legal s a →
        ReachableFrom M start (t + 1) (M.step s a)

/-- Exact-step reachability from the scenario initial state, the notion used by
the certificates. `ReachableFrom` is the underlying inductive relation;
`Reachable M t s` is definitionally `ReachableFrom M M.init t s`. -/
abbrev Reachable {State : Type u} {Action : Type v} (M : Model State Action)
    (t : Nat) (s : State) : Prop :=
  ReachableFrom M M.init t s

/-- Prepend one legal action to an exact-step path. This is the "front" version
of `ReachableFrom.succ` (which appends the last action). -/
theorem ReachableFrom.head {State : Type u} {Action : Type v} {M : Model State Action}
    {s : State} {a : Action} {t : Nat} {s' : State}
    (hlegal : M.legal s a) (h : ReachableFrom M (M.step s a) t s') :
    ReachableFrom M s (t + 1) s' := by
  induction h with
  | zero => exact ReachableFrom.succ ReachableFrom.zero hlegal
  | succ hreach hlegal' ih => exact ReachableFrom.succ ih hlegal'

/-- Reachability composes: `t₁` steps then `t₂` steps is `t₁ + t₂` steps. -/
theorem ReachableFrom.trans {State : Type u} {Action : Type v} {M : Model State Action}
    {start : State} {t₁ : Nat} {s : State} {t₂ : Nat} {s' : State}
    (h₁ : ReachableFrom M start t₁ s) (h₂ : ReachableFrom M s t₂ s') :
    ReachableFrom M start (t₁ + t₂) s' := by
  induction h₂ with
  | zero => simpa using h₁
  | succ hreach hlegal ih => simpa [Nat.add_assoc] using ReachableFrom.succ ih hlegal

/-- A legal action sequence, replayed from an explicit start state. This is the
witness format scenario modules should emit; `run` computes the final state. -/
def run {State : Type u} {Action : Type v} (M : Model State Action) : State → List Action → State
  | s, [] => s
  | s, a :: rest => run M (M.step s a) rest

/-- Every prefix of this sequence consists of actions legal at the state
reached so far. -/
inductive LegalPath {State : Type u} {Action : Type v} (M : Model State Action) :
    State → List Action → Prop where
  | nil (s : State) : LegalPath M s []
  | cons {s : State} {a : Action} {rest : List Action} :
      M.legal s a → LegalPath M (M.step s a) rest → LegalPath M s (a :: rest)

/-- Replaying a legal sequence advances exactly one tick per action. -/
theorem run_append {State : Type u} {Action : Type v} {M : Model State Action}
    (s : State) : ∀ as bs : List Action,
      run M s (as ++ bs) = run M (run M s as) bs
  | [], _ => rfl
  | a :: as, bs => by
      simp only [List.cons_append, run]
      exact run_append (M.step s a) as bs

/-- Concatenation of legal action sequences. -/
theorem LegalPath.append {State : Type u} {Action : Type v} {M : Model State Action}
    {s : State} {as bs : List Action}
    (h₁ : LegalPath M s as) (h₂ : LegalPath M (run M s as) bs) :
    LegalPath M s (as ++ bs) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hlegal _ ih => exact LegalPath.cons hlegal (ih h₂)

/-- A legal action sequence of length `t` yields an exact-step reachable state. -/
theorem legalPath_run_reachableFrom {State : Type u} {Action : Type v}
    {M : Model State Action} {s : State} :
    ∀ {as : List Action}, LegalPath M s as →
      ReachableFrom M s as.length (run M s as)
  | [], h => by cases h; exact ReachableFrom.zero
  | a :: rest, h => by
      cases h with
      | cons hlegal hrest =>
          exact ReachableFrom.head hlegal (legalPath_run_reachableFrom hrest)

/-- Conversely, every exact-step reachable state has a legal action sequence
witness of the same length. -/
theorem reachableFrom_exists_legalPath {State : Type u} {Action : Type v}
    {M : Model State Action} {start : State} :
    ∀ {t : Nat} {s : State}, ReachableFrom M start t s →
      ∃ as : List Action, as.length = t ∧ run M start as = s ∧ LegalPath M start as
  | 0, _, h => by
      cases h with
      | zero => exact ⟨[], rfl, rfl, LegalPath.nil _⟩
  | t + 1, _, h => by
      cases h with
      | @succ t' s' a' hreach hlegal =>
          obtain ⟨as, hlen, hrun, hpath⟩ := reachableFrom_exists_legalPath hreach
          have hlast : M.legal (run M start as) a' := by rw [hrun]; exact hlegal
          refine ⟨as ++ [a'], by simp [hlen], ?_, ?_⟩
          · rw [run_append, hrun]
            rfl
          · exact LegalPath.append hpath (LegalPath.cons hlast (LegalPath.nil _))

/-- Exact-step reachability is exactly existence of a legal action sequence of
that length. -/
theorem reachable_iff_exists_legalPath {State : Type u} {Action : Type v}
    {M : Model State Action} {t : Nat} {s : State} :
    Reachable M t s ↔
      ∃ as : List Action, as.length = t ∧ run M M.init as = s ∧ LegalPath M M.init as :=
  ⟨reachableFrom_exists_legalPath, fun ⟨_, hlen, hrun, hpath⟩ => by
    rw [← hrun]
    rw [← hlen]
    exact legalPath_run_reachableFrom hpath⟩


/-! ### Computable frontiers -/

/-- Membership-preserving deduplication. Core Lean does not ship `List.dedup`
with a membership lemma, so we provide a small self-contained one. Deduplication
only affects the size of the frontier, never which states are reachable. -/
def dedup {α : Type u} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as => a :: ((dedup as).filter (fun b => decide (b ≠ a)))

/-- `dedup` does not change membership. -/
theorem mem_dedup {α : Type u} [DecidableEq α] {b : α} :
    ∀ {l : List α}, b ∈ dedup l ↔ b ∈ l
  | [] => by simp [dedup]
  | a :: as => by
      simp only [dedup, List.mem_cons, List.mem_filter, mem_dedup (b := b) (l := as)]
      constructor
      · rintro (rfl | ⟨hmem, _⟩)
        · exact Or.inl rfl
        · exact Or.inr hmem
      · rintro (rfl | hmem)
        · exact Or.inl rfl
        · by_cases hba : b = a
          · exact Or.inl hba
          · exact Or.inr ⟨hmem, decide_eq_true hba⟩

/-- All successor states of `s` under the enumerated legal actions. -/
def successors {State : Type u} {Action : Type v} (M : Model State Action)
    (s : State) : List State :=
  (M.legalActions s).map (fun a => M.step s a)

/-- Membership in `successors` is exactly "one legal action away". -/
theorem mem_successors {State : Type u} {Action : Type v} {M : Model State Action}
    {s s' : State} :
    s' ∈ successors M s ↔ ∃ a ∈ M.legalActions s, M.step s a = s' := by
  simp [successors]

/-- The computed exact-step frontier: `Frontier M t` is the deduplicated list of
all states reachable from `M.init` in exactly `t` legal resolutions. -/
def Frontier {State : Type u} {Action : Type v} [DecidableEq State]
    (M : Model State Action) : Nat → List State
  | 0 => [M.init]
  | t + 1 => dedup ((Frontier M t).flatMap (successors M))

@[simp] theorem frontier_zero {State : Type u} {Action : Type v} [DecidableEq State]
    (M : Model State Action) : Frontier M 0 = [M.init] := rfl

@[simp] theorem frontier_succ {State : Type u} {Action : Type v} [DecidableEq State]
    (M : Model State Action) (t : Nat) :
    Frontier M (t + 1) = dedup ((Frontier M t).flatMap (successors M)) := rfl

/-- **Frontier soundness and completeness.** Membership in the computed frontier
is equivalent to exact-step reachability. The backward direction is where
`legalActions_complete` is used: every legal action must appear in the
enumeration, otherwise a reachable state could be missing from the frontier and
a lower bound could be unsound. -/
theorem mem_frontier_iff {State : Type u} {Action : Type v} [DecidableEq State]
    {M : Model State Action} (t : Nat) (s : State) :
    s ∈ Frontier M t ↔ Reachable M t s := by
  induction t generalizing s with
  | zero =>
      constructor
      · intro h
        have hs : s = M.init := by simpa [frontier_zero] using h
        rw [hs]
        exact ReachableFrom.zero
      · intro h
        cases h with
        | zero => simp [frontier_zero]
  | succ t ih =>
      constructor
      · intro h
        rw [frontier_succ, mem_dedup, List.mem_flatMap] at h
        obtain ⟨p, hp, hsp⟩ := h
        rw [mem_successors] at hsp
        obtain ⟨a, ha, hstep⟩ := hsp
        rw [← hstep]
        exact ReachableFrom.succ ((ih p).mp hp) (Model.legalActions_sound p a ha)
      · intro h
        rw [frontier_succ, mem_dedup, List.mem_flatMap]
        cases h with
        | @succ t' s' a' hreach hlegal =>
            refine ⟨s', (ih s').mpr hreach, ?_⟩
            rw [mem_successors]
            exact ⟨a', Model.legalActions_complete s' a' hlegal, rfl⟩


/-! ### Goal predicates, lower bounds and optimality -/

/-- The goal is achievable after exactly `t` turn resolutions. -/
def AchievableAt {State : Type u} {Action : Type v} (M : Model State Action)
    (goal : State → Prop) (t : Nat) : Prop :=
  ∃ s, Reachable M t s ∧ goal s

/-- No goal state is reachable in strictly fewer than `N` resolutions.

  The quantifier ranges over `Reachable`, which is the exact-step relation built
  from the authoritative `legal` predicate. By
  `noEarlier_iff_all_legalPaths` below this is the same as saying that *every*
  legal action sequence of length `< N` fails to reach the goal. -/
def NoEarlier {State : Type u} {Action : Type v} (M : Model State Action)
    (goal : State → Prop) (N : Nat) : Prop :=
  ∀ t, t < N → ∀ s, Reachable M t s → ¬ goal s

/-- `N` is the first tick at which the goal is achievable. -/
def OptimalAt {State : Type u} {Action : Type v} (M : Model State Action)
    (goal : State → Prop) (N : Nat) : Prop :=
  AchievableAt M goal N ∧ NoEarlier M goal N

/-- A legal action sequence of length `N` reaching the goal gives achievability
at `N`. This is the preferred witness format: the scenario supplies the list of
actions, and this theorem replays it through `run`. -/
theorem AchievableAt.of_legalPath {State : Type u} {Action : Type v}
    {M : Model State Action} {goal : State → Prop} {N : Nat} {as : List Action}
    (hlen : as.length = N) (hpath : LegalPath M M.init as)
    (hgoal : goal (run M M.init as)) : AchievableAt M goal N := by
  refine ⟨run M M.init as, ?_, hgoal⟩
  rw [← hlen]
  exact legalPath_run_reachableFrom hpath

/-- A concrete frontier member satisfying the goal witnesses achievability at
`N`. This is the propositional counterpart of `achievableAt_of_witness`. -/
theorem AchievableAt.of_mem_frontier {State : Type u} {Action : Type v}
    [DecidableEq State] {M : Model State Action} {goal : State → Prop} {N : Nat}
    {s : State} (hs : s ∈ Frontier M N) (hg : goal s) : AchievableAt M goal N :=
  ⟨s, (mem_frontier_iff N s).mp hs, hg⟩

/-- A lower bound for `N` is also a lower bound for every smaller horizon. -/
theorem NoEarlier.mono {State : Type u} {Action : Type v} {M : Model State Action}
    {goal : State → Prop} {N N' : Nat} (hNN' : N ≤ N') (h : NoEarlier M goal N') :
    NoEarlier M goal N :=
  fun t ht => h t (Nat.lt_of_lt_of_le ht hNN')

/-- Minimality consequence: no smaller horizon is achievable. -/
theorem OptimalAt.not_achievable_before {State : Type u} {Action : Type v}
    {M : Model State Action} {goal : State → Prop} {N : Nat}
    (h : OptimalAt M goal N) :
    ∀ t, t < N → ¬ AchievableAt M goal t := by
  intro t ht ⟨s, hreach, hgoal⟩
  exact h.2 t ht s hreach hgoal

/-- The lower bound expressed directly on the computed frontiers. This is the
bridge used by the executable checkers. -/
theorem noEarlier_iff_no_goal_in_frontier {State : Type u} {Action : Type v}
    [DecidableEq State] {M : Model State Action} {goal : State → Prop}
    (goalB : State → Bool) (hspec : ∀ s, goalB s = true ↔ goal s) (N : Nat) :
    NoEarlier M goal N ↔
      ∀ t, t < N → ∀ s ∈ Frontier M t, goalB s = false := by
  constructor
  · intro h t ht s hs
    have hreach : Reachable M t s := (mem_frontier_iff t s).mp hs
    cases hb : goalB s with
    | false => rfl
    | true => exact absurd ((hspec s).mp hb) (h t ht s hreach)
  · intro h t ht s hreach hgoal
    have hb : goalB s = true := (hspec s).mpr hgoal
    have hfalse := h t ht s ((mem_frontier_iff t s).mpr hreach)
    rw [hb] at hfalse
    exact Bool.noConfusion hfalse

/-- **The negative result covers every legal action sequence**, not just the
paths the frontier builder happened to explore. A scenario therefore cannot
prove a lower bound by silently dropping a legal action: `LegalPath` restricts
only to actions satisfying `legal`, and the enumeration is linked to `legal` by
`legalActions_sound`/`legalActions_complete`. -/
theorem noEarlier_iff_all_legalPaths {State : Type u} {Action : Type v}
    {M : Model State Action} {goal : State → Prop} {N : Nat} :
    NoEarlier M goal N ↔
      ∀ (as : List Action), as.length < N → LegalPath M M.init as →
        ¬ goal (run M M.init as) := by
  constructor
  · intro h as hlen hpath hgoal
    have hreach : Reachable M as.length (run M M.init as) :=
      legalPath_run_reachableFrom hpath
    exact h as.length hlen _ hreach hgoal
  · intro h t ht s hreach hgoal
    obtain ⟨as, hlen, hrun, hpath⟩ := reachableFrom_exists_legalPath hreach
    exact h as (by rw [hlen]; exact ht) hpath (by rwa [← hrun] at hgoal)

/-! ### Executable checks -/

/-- Boolean negations of `true` are `false` and vice versa. -/
theorem not_eq_true_iff_eq_false (b : Bool) : (Bool.not b = true) ↔ (b = false) := by
  cases b <;> simp

/-- Check that none of the frontiers `0, …, N-1` contains a goal state. -/
def checkNoGoalBelow {State : Type u} {Action : Type v} [DecidableEq State]
    (M : Model State Action) (goalB : State → Bool) : Nat → Bool
  | 0 => true
  | Nat.succ N => checkNoGoalBelow M goalB N && Bool.not ((Frontier M N).any goalB)

/-- Specification of `checkNoGoalBelow`. -/
theorem checkNoGoalBelow_eq_true_iff {State : Type u} {Action : Type v}
    [DecidableEq State] {M : Model State Action} {goalB : State → Bool} {N : Nat} :
    checkNoGoalBelow M goalB N = true ↔
      ∀ t, t < N → ∀ s ∈ Frontier M t, goalB s = false := by
  induction N with
  | zero => simp [checkNoGoalBelow]
  | succ N ih =>
      rw [checkNoGoalBelow, Bool.and_eq_true]
      constructor
      · rintro ⟨hbelow, hlast⟩ t ht s hs
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
        · exact (ih.mp hbelow) t ht' s hs
        · have hany : (Frontier M t).any goalB = false :=
            (not_eq_true_iff_eq_false _).mp hlast
          exact (Bool.eq_false_iff).mpr ((List.any_eq_false).mp hany s hs)
      · intro h
        refine ⟨ih.mpr (fun t ht => h t (Nat.lt_succ_of_lt ht)), ?_⟩
        have hany : (Frontier M N).any goalB = false :=
          (List.any_eq_false).mpr (fun s hs =>
            (Bool.eq_false_iff).mp (h N (Nat.lt_succ_self N) s hs))
        exact (not_eq_true_iff_eq_false _).mpr hany

/-- The lower-bound theorem produced by the boolean checker. -/
theorem noEarlier_of_checkNoGoalBelow {State : Type u} {Action : Type v}
    [DecidableEq State] {M : Model State Action} {goal : State → Prop}
    (goalB : State → Bool) (hspec : ∀ s, goalB s = true ↔ goal s) {N : Nat}
    (h : checkNoGoalBelow M goalB N = true) : NoEarlier M goal N := by
  intro t ht s hreach hgoal
  have hfalse : goalB s = false :=
    (checkNoGoalBelow_eq_true_iff.mp h) t ht s ((mem_frontier_iff t s).mpr hreach)
  have htrue : goalB s = true := (hspec s).mpr hgoal
  rw [hfalse] at htrue
  exact Bool.noConfusion htrue

/-- First goal state in the frontier at `N`, if any. This is a computable
witness finder for the upper-bound half of a certificate. -/
def witnessAt {State : Type u} {Action : Type v} [DecidableEq State]
    (M : Model State Action) (goalB : State → Bool) (N : Nat) : Option State :=
  (Frontier M N).find? goalB

/-- `witnessAt` returns a frontier member satisfying the boolean goal. -/
theorem witnessAt_spec {State : Type u} {Action : Type v} [DecidableEq State]
    {M : Model State Action} {goal : State → Prop} {goalB : State → Bool}
    (hspec : ∀ s, goalB s = true ↔ goal s) {N : Nat} {s : State}
    (h : witnessAt M goalB N = some s) : s ∈ Frontier M N ∧ goal s :=
  ⟨List.mem_of_find?_eq_some h, (hspec s).mp (List.find?_some h)⟩

/-- A computable witness at `N` gives achievability at `N`. -/
theorem achievableAt_of_witness {State : Type u} {Action : Type v}
    [DecidableEq State] {M : Model State Action} {goal : State → Prop}
    {goalB : State → Bool} (hspec : ∀ s, goalB s = true ↔ goal s) {N : Nat}
    (h : ∃ s, s ∈ Frontier M N ∧ goalB s = true) : AchievableAt M goal N := by
  obtain ⟨s, hs, hg⟩ := h
  exact ⟨s, (mem_frontier_iff N s).mp hs, (hspec s).mp hg⟩

/-- One boolean pass: no goal below `N` **and** a goal at `N`. -/
def checkCertificate {State : Type u} {Action : Type v} [DecidableEq State]
    (M : Model State Action) (goalB : State → Bool) (N : Nat) : Bool :=
  checkNoGoalBelow M goalB N && (Frontier M N).any goalB

/-- **Main certificate theorem (frontier form).** If the check passes, then `N`
is exactly the first tick at which the goal is achievable. The hypothesis
`hspec` is the only connection between the boolean `goalB` used for computation
and the propositional goal used in the theorem. -/
theorem optimalAt_of_checkCertificate {State : Type u} {Action : Type v}
    [DecidableEq State] {M : Model State Action} {goal : State → Prop}
    (goalB : State → Bool) (hspec : ∀ s, goalB s = true ↔ goal s) {N : Nat}
    (h : checkCertificate M goalB N = true) : OptimalAt M goal N := by
  have h' : checkNoGoalBelow M goalB N = true ∧ (Frontier M N).any goalB = true := by
    rw [checkCertificate, Bool.and_eq_true] at h
    exact h
  refine ⟨achievableAt_of_witness hspec ((List.any_eq_true).mp h'.2),
    noEarlier_of_checkNoGoalBelow goalB hspec h'.1⟩

/-- Separate lower-bound and witness form of the certificate: no goal in any
frontier below `N`, plus one goal state in the frontier at `N`. This is the
most direct match for the phrase "check no goal below N and a witness at N". -/
theorem optimalAt_of_noGoalBelow_and_witness {State : Type u} {Action : Type v}
    [DecidableEq State] {M : Model State Action} {goal : State → Prop}
    (goalB : State → Bool) (hspec : ∀ s, goalB s = true ↔ goal s) {N : Nat}
    (hbelow : checkNoGoalBelow M goalB N = true)
    (hwit : ∃ s, s ∈ Frontier M N ∧ goalB s = true) : OptimalAt M goal N :=
  ⟨achievableAt_of_witness hspec hwit,
    noEarlier_of_checkNoGoalBelow goalB hspec hbelow⟩

/-- Find the first tick in `0, …, bound` whose frontier contains a goal state. -/
def earliestGoalTick? {State : Type u} {Action : Type v} [DecidableEq State]
    (M : Model State Action) (goalB : State → Bool) (bound : Nat) : Option Nat :=
  (List.range (bound + 1)).find? (fun t => (Frontier M t).any goalB)


/-- Specification of `List.find?` on `List.range`, proved here without
`Classical.choice` (the core library version pulls in that axiom). -/
theorem find?_range_eq_some_spec {p : Nat → Bool} :
    ∀ {n i : Nat}, (List.range n).find? p = some i →
      p i = true ∧ i < n ∧ ∀ j, j < i → p j = false
  | 0, i, h => by simp at h
  | n + 1, i, h => by
      rw [List.range_succ, List.find?_append, Option.or_eq_some_iff] at h
      rcases h with hleft | ⟨hleft_none, hright⟩
      · obtain ⟨hp, hlt, hbefore⟩ := find?_range_eq_some_spec hleft
        exact ⟨hp, Nat.lt_succ_of_lt hlt, hbefore⟩
      · rw [List.find?_singleton] at hright
        split at hright
        · rename_i hp
          injection hright with hi
          subst hi
          refine ⟨hp, Nat.lt_succ_self n, ?_⟩
          intro j hj
          have hnone : (List.range n).find? p = none := hleft_none
          exact (Bool.eq_false_iff).mpr
            ((List.find?_eq_none).mp hnone j (List.mem_range.mpr hj))
        · simp at hright

/-- Specification of `earliestGoalTick?`: it returns a tick `N ≤ bound` whose
frontier has a goal, and every strictly earlier frontier is goal-free. -/
theorem earliestGoalTick?_spec {State : Type u} {Action : Type v} [DecidableEq State]
    {M : Model State Action} {goalB : State → Bool} {bound N : Nat}
    (h : earliestGoalTick? M goalB bound = some N) :
    N ≤ bound ∧ (Frontier M N).any goalB = true ∧
      ∀ t, t < N → (Frontier M t).any goalB = false := by
  obtain ⟨hp, hmem, hbefore⟩ := find?_range_eq_some_spec h
  refine ⟨Nat.lt_succ_iff.mp hmem, hp, ?_⟩
  intro t ht
  exact hbefore t ht

/-- **Main certificate theorem (scan form).** A successful earliest-goal scan
is a complete optimality certificate, including the lower bound. -/
theorem optimalAt_of_earliestGoalTick? {State : Type u} {Action : Type v}
    [DecidableEq State] {M : Model State Action} {goal : State → Prop}
    (goalB : State → Bool) (hspec : ∀ s, goalB s = true ↔ goal s) {bound N : Nat}
    (h : earliestGoalTick? M goalB bound = some N) : OptimalAt M goal N := by
  obtain ⟨-, hany, hbefore⟩ := earliestGoalTick?_spec h
  refine ⟨achievableAt_of_witness hspec ((List.any_eq_true).mp hany), ?_⟩
  intro t ht s hreach hgoal
  have htrue : goalB s = true := (hspec s).mpr hgoal
  have hfalse : goalB s = false :=
    (Bool.eq_false_iff).mpr
      ((List.any_eq_false).mp (hbefore t ht) s ((mem_frontier_iff t s).mpr hreach))
  rw [hfalse] at htrue
  exact Bool.noConfusion htrue

/-- If the scan finds nothing up to `bound`, every frontier in `0, …, bound` is
goal-free. Scenario modules use this to justify searching a larger horizon (or
to report an unproved lower bound, never to claim optimality). -/
theorem noGoal_below_of_earliestGoalTick?_none {State : Type u} {Action : Type v}
    [DecidableEq State] {M : Model State Action} {goalB : State → Bool} {bound : Nat}
    (h : earliestGoalTick? M goalB bound = none) :
    ∀ t, t < bound + 1 → ∀ s ∈ Frontier M t, goalB s = false := by
  intro t ht s hs
  have hany : (Frontier M t).any goalB = false :=
    (not_eq_true_iff_eq_false _).mp ((List.find?_range_eq_none).mp h t ht)
  exact (Bool.eq_false_iff).mpr ((List.any_eq_false).mp hany s hs)


/-! ### Smoke test: a four-state synthetic model

  This is deliberately not a Civilization VI scenario. It exercises the whole
  pipeline (model instance, legal-path witness, computed frontier, boolean
  check, optimality theorem, and a deliberately-too-small lower bound) so that
  the generic API is known to be usable end to end.
-/

namespace Toy

/-- Four states in a line; only `advance` makes progress. -/
inductive State where
  | s0 | s1 | s2 | s3
  deriving DecidableEq, Repr

/-- `wait` is a legal no-op at the endpoints; `advance` moves one step. -/
inductive Action where
  | wait | advance
  deriving DecidableEq, Repr

/-- Deterministic transition function. -/
def step : State → Action → State
  | .s0, .advance => .s1
  | .s1, .advance => .s2
  | .s2, .advance => .s3
  | s, .wait => s
  | .s3, .advance => .s3

/-- The authoritative legality predicate, defined independently of the
enumeration below. -/
def legal : State → Action → Prop
  | .s0, .wait => True
  | .s0, .advance => True
  | .s1, .advance => True
  | .s2, .advance => True
  | .s3, .wait => True
  | _, _ => False

/-- The enumeration whose soundness and completeness are proved below. -/
def legalActions : State → List Action
  | .s0 => [.wait, .advance]
  | .s1 => [.advance]
  | .s2 => [.advance]
  | .s3 => [.wait]

/-- The toy model instance. -/
def model : Model State Action where
  init := .s0
  step := step
  legal := legal
  legalDec := fun s a => by
    cases s <;> cases a <;> simp [legal] <;> infer_instance
  legalActions := legalActions
  legalActions_sound := by
    intro s a h
    cases s <;> cases a <;> simp [legalActions, legal] at h ⊢
  legalActions_complete := by
    intro s a h
    cases s <;> cases a <;> simp [legalActions, legal] at h ⊢

/-- Target: reach the last state. -/
def goal (s : State) : Prop := s = .s3

/-- Executable version of the target. -/
def goalB (s : State) : Bool := decide (s = .s3)

/-- `goalB` agrees with the propositional goal. -/
theorem goalB_spec (s : State) : goalB s = true ↔ goal s := by
  simp [goalB, goal]

/-- Three `advance` actions are the shortest witness. -/
def witness : List Action := [.advance, .advance, .advance]

/-- The witness is legal at every step. -/
theorem witness_legal : LegalPath model .s0 witness := by
  refine LegalPath.cons ?_ (LegalPath.cons ?_ (LegalPath.cons ?_ (LegalPath.nil _)))
  all_goals decide

/-- Replaying the witness reaches `s3`. -/
theorem witness_run : run model .s0 witness = .s3 := by decide

/-- The witness achieves the goal. -/
theorem witness_achieves : goal (run model .s0 witness) := by
  simp [goal, witness_run]

/-- Upper bound by replaying an explicit legal action list. -/
theorem toy_achievable : AchievableAt model goal 3 :=
  AchievableAt.of_legalPath (M := model) (goal := goal) (N := 3) (as := witness)
    rfl witness_legal witness_achieves

/-- The computed scan finds the first goal tick. -/
theorem toy_earliest : earliestGoalTick? model goalB 6 = some 3 := by decide

/-- Full optimality from the computable scan. -/
theorem toy_optimal : OptimalAt model goal 3 :=
  optimalAt_of_earliestGoalTick? goalB goalB_spec toy_earliest

/-- The single boolean certificate also passes at `N = 3`. -/
theorem toy_check : checkCertificate model goalB 3 = true := by decide

/-- Full optimality from the single boolean certificate. -/
theorem toy_optimal_check : OptimalAt model goal 3 :=
  optimalAt_of_checkCertificate goalB goalB_spec toy_check

/-- The separated lower-bound + witness form gives the same optimality result. -/
theorem toy_optimal_split : OptimalAt model goal 3 :=
  optimalAt_of_noGoalBelow_and_witness goalB goalB_spec
    (by decide) (List.any_eq_true.mp (by decide))

/-- The same certificate deliberately checked at the too-small `N = 2` fails. -/
theorem toy_check_two_fails : checkCertificate model goalB 2 = false := by decide

/-- Consequently, tick 2 is not achievable (this is the negative direction that
a wrong lower bound would have to overcome). -/
theorem toy_not_achievable_two : ¬ AchievableAt model goal 2 :=
  fun h => toy_optimal.not_achievable_before (t := 2) (by decide) h

/-- The witness finder returns the unique goal state from the level-3 frontier. -/
theorem toy_witnessAt : witnessAt model goalB 3 = some .s3 := by decide

end Toy

/-! ### Axiom audit

  The exact build command is

  ```
  scripts/lean-env lake env lean Civ6Verify/Reachability/Finite.lean
  ```

  These commands make the trust dependencies of the main theorems explicit.
  Expected output (Lean 4.25.0): only the standard Lean axioms `propext` and
  `Quot.sound`, introduced by core `List` lemmas. There is no `sorryAx`, no
  custom axiom, no `native_decide`, and no `Classical.choice` (the local
  `find?_range_eq_some_spec` replaces the core `find?`/`range` lemma that would
  introduce `Classical.choice`). -/
#print axioms mem_frontier_iff
#print axioms reachable_iff_exists_legalPath
#print axioms AchievableAt.of_legalPath
#print axioms AchievableAt.of_mem_frontier
#print axioms noEarlier_iff_all_legalPaths
#print axioms noEarlier_iff_no_goal_in_frontier
#print axioms checkNoGoalBelow_eq_true_iff
#print axioms witnessAt_spec
#print axioms optimalAt_of_checkCertificate
#print axioms optimalAt_of_noGoalBelow_and_witness
#print axioms find?_range_eq_some_spec
#print axioms optimalAt_of_earliestGoalTick?
#print axioms Toy.toy_optimal
#print axioms Toy.toy_optimal_check
#print axioms Toy.toy_optimal_split
#print axioms Toy.toy_check_two_fails
#print axioms Toy.toy_not_achievable_two

end Civ6Verify.Reachability
