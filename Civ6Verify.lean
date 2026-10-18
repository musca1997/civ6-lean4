/-
  Root module for the Civ6 optimality-certificate development.

  Scope and status: skeleton only. This module defines the project's internal
  time convention (PLAN.md §2.1) and a few kernel-checked sanity lemmas so that
  `lake build` exercises a real proof dependency. It makes **no** claims about
  Civilization VI rules; all rule constants live in the M0-verified modules
  added later under `Civ6Verify/Rules/`.

  Conventions established here:
  * `Tick` is the internal clock: the initial state is `t = 0`, and the state
    after `k` completed turn resolutions is `t = k`.
  * Completion events must be monotone history flags/counters, never inferred
    from the current production queue (PLAN.md §2.1).

  Trust: no `sorry`, no custom axioms, no `native_decide` in this file. Proofs
  are closed by `rfl`/`omega`-free definitional reduction so that the root
  module has no extra kernel dependencies.
-/

import Civ6Verify.Reachability.Finite
import Civ6Verify.Scenarios.Synthetic
import Civ6Verify.Model.Mvp
import Civ6Verify.Bounds.MvpArithmetic
import Civ6Verify.Bounds.MvpOptimality

namespace Civ6Verify

/-- Internal turn clock. `0` is the initial state; `k` is the state after `k`
turn resolutions. Mapping to the in-game turn counter is documented per
scenario (PLAN.md §2.1). -/
abbrev Tick := Nat

/-- One turn resolution advances the clock by exactly one. -/
def advance (t : Tick) : Tick := t + 1

/-- A monotone completion-history marker: once a goal is recorded at some tick,
it stays recorded at every later tick. This is the shape every "completed at
least one Settler" predicate in later modules must have. -/
def CompletedBy (done : Tick → Bool) : Prop :=
  ∀ t, done t = true → ∀ t', t ≤ t' → done t' = true

theorem advance_injective : Function.Injective advance := by
  intro a b h
  exact Nat.succ.inj h

theorem advance_monotone : ∀ t : Tick, t < advance t := by
  intro t
  exact Nat.lt_succ_self t

/-- Sample value used by `Main.lean`; keeps the executable's output tied to a
checked definition rather than a literal. -/
def tickExample : Tick := advance 0

theorem tickExample_eq : tickExample = 1 := rfl

end Civ6Verify
