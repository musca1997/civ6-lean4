/-
  Civ6Verify/Bounds/MvpArithmetic.lean

  Scenario-arithmetic core of the **conditional** MVP lower bound
  (`mvp/LOWER-BOUND.md`).  This module is *not* the Civ6 model: it owns the
  finite yield arithmetic of σ = `sigma-capital-4tiles-v1` and the pure
  horizon inequalities that the model-side proof instantiates.

  What is proved here (all kernel-checked, no `sorry`, no custom axioms, no
  compiler-trust tactics):

  * §1  tile yields and the per-tile budget `2·food + prod ≤ 4 + [tile = GH]`;
  * §2  the induced per-assignment caps for pop 1..4, including the two
        *Pareto-dual* inequalities
          pop 2, non-growth:  11·q + 21·e ≤ 9240
          pop 3, non-growth:  11·q + 21·e ≤ 9240
        and the coarse caps `q ≤ 630` (pop 2, no growth), `q ≤ 735`
        (any step, including the extra citizen's production) and `e ≤ 220`;
  * §3  a list-summing lemma turning per-step dual facts into one inequality
        over a whole play;
  * §4  the two-case horizon arithmetic: case A (pop never reaches 3) and
        case B (pop 3 is reached at step `k ≥ 18`), for horizons 19 and 24,
        concluding `prog < 8000` resp. `prog < 11000`;
  * §5  the matching achievability numbers and the *counterexample* showing
        that the closed form `7 + ⌈cost/630⌉` is not a consequence of a
        per-step maximum alone.

  Units are the contract's fixed point (1/100).  Internally the proofs work in
  "points" (1 point = 100 units): tile yields 2/2/1/1 food and 0/1/2/1
  production, base 2 food + 3 production (centre 1 + palace 2, A1).  Every
  quantity in σ is an integer multiple of 100, so no rounding is hidden in the
  conversion.

  Trust boundary: this module makes no Civ6 claim and no statement about an
  in-game optimum.  The reduction "M_MVP step ⇒ these hypotheses" is *not*
  formalised here; the required model lemmas are listed in
  `mvp/LOWER-BOUND.md` §7 (bridge obligations).
-/

namespace Civ6Verify.Bounds.MvpArithmetic

/-! ## 1. Scenario σ yields and the per-tile budget -/

/-- The four assignable tiles of σ (the city centre is free and never
assignable; the palace contributes its +2 production to the base). -/
inductive Tile where
  | G
  | GH
  | PH
  | P
  deriving DecidableEq, Repr

/-- Food yield in points (1 point = 100 in the contract's fixed point). -/
def foodPts : Tile → Nat
  | .G => 2
  | .GH => 2
  | .PH => 1
  | .P => 1

/-- Production yield in points. -/
def prodPts : Tile → Nat
  | .G => 0
  | .GH => 1
  | .PH => 2
  | .P => 1

/-- The unique tile that beats the uniform per-tile budget
`2·food + prod ≤ 4`; every other tile satisfies it with slack. -/
def ghWeight : Tile → Nat
  | .GH => 1
  | _ => 0

/-- **Per-tile budget.**  This is the only combinatorial input of the whole
bound: summing it over a work set gives `2·food + prod ≤ 4·|work| + 1`. -/
theorem per_tile_budget (t : Tile) : 2 * foodPts t + prodPts t ≤ 4 + ghWeight t := by
  cases t <;> decide

theorem per_tile_food (t : Tile) : foodPts t ≤ 2 := by cases t <;> decide

theorem per_tile_prod (t : Tile) : prodPts t ≤ 2 := by cases t <;> decide

/-! ## 2. Per-assignment caps

An assignment is represented by four 0/1 indicators.  The model's `work` field
(one citizen per tile, no duplicates) is converted to these indicators by the
bridge; `h0..h3` are the "at most one citizen on this tile" facts. -/

/-- A work assignment as 0/1 indicators of the four tiles.  (Optimal lines work
exactly `pop` tiles, but the caps below hold for every legal `|work| ≤ pop`,
i.e. also for the idle-citizen relaxation G5.) -/
structure Assign where
  (g gh ph p : Nat)
  (h0 : g ≤ 1)
  (h1 : gh ≤ 1)
  (h2 : ph ≤ 1)
  (h3 : p ≤ 1)

namespace Assign

/-- Total food of the work set, in points. -/
def food (a : Assign) : Nat := 2 * a.g + 2 * a.gh + a.ph + a.p

/-- Total production of the work set, in points. -/
def prod (a : Assign) : Nat := a.gh + 2 * a.ph + a.p

/-- Number of worked tiles = |work| (≤ pop on every legal step). -/
def count (a : Assign) : Nat := a.g + a.gh + a.ph + a.p

theorem bounds (a : Assign) : a.g ≤ 1 ∧ a.gh ≤ 1 ∧ a.ph ≤ 1 ∧ a.p ≤ 1 :=
  ⟨a.h0, a.h1, a.h2, a.h3⟩

/-- **Budget.** `2·food + prod ≤ 4·|work| + 1`. -/
theorem budget (a : Assign) : 2 * a.food + a.prod ≤ 4 * a.count + 1 := by
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [food, prod, count]
  omega

theorem food_le (a : Assign) : a.food ≤ 2 * a.count := by
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [food, count]
  omega

theorem prod_le (a : Assign) : a.prod ≤ 2 * a.count := by
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [prod, count]
  omega

/-! ### Food caps per population

`F = 200 + 100·food` and `d = F - 200·pop = 100·(2 + food - 2·pop)`.  The
model's growth surplus is `e = 110·dpts` at the happy tier (≤ 110 over Θ),
where `dpts = 2 + food - 2·pop`.  Hence the caps below on `food`, `dpts`, `e`.
-/

theorem food_le_pop1 (a : Assign) (h : a.count ≤ 1) : a.food ≤ 2 := by
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [count] at h
  simp only [food]
  omega

theorem food_le_pop2 (a : Assign) (h : a.count ≤ 2) : a.food ≤ 4 := by
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [count] at h
  simp only [food]
  omega

theorem food_le_pop3 (a : Assign) (h : a.count ≤ 3) : a.food ≤ 5 := by
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [count] at h
  simp only [food]
  omega

theorem food_le_pop4 (a : Assign) : a.food ≤ 6 := by
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [food]
  omega

theorem prod_le_pop2 (a : Assign) (h : a.count ≤ 2) : a.prod ≤ 3 := by
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [count] at h
  simp only [prod]
  omega

theorem prod_le_pop3 (a : Assign) (h : a.count ≤ 3) : a.prod ≤ 4 := by
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [count] at h
  simp only [prod]
  omega

/-- `dpts ≤ 2` at pop 2: the largest surplus is `GH + G` (`d = 200`). -/
theorem dpts_pop2 (a : Assign) (h : a.count ≤ 2) : 2 + a.food - 2 * 2 ≤ 2 := by
  have := a.food_le_pop2 h
  omega

/-- `dpts ≤ 1` at pop 3: the largest food triple is `2+2+1 = 5`, `d = 100`. -/
theorem dpts_pop3 (a : Assign) (h : a.count ≤ 3) : 2 + a.food - 2 * 3 ≤ 1 := by
  have := a.food_le_pop3 h
  omega

/-- At pop 4 the full tile set is `2+2+1+1 = 6`, so `d ≤ 0` (no surplus). -/
theorem dpts_pop4 (a : Assign) : 2 + a.food - 2 * 4 ≤ 0 := by
  have := a.food_le_pop4
  omega

/-! ### Production caps in contract units

`P = 300 + 100·prod` and `q = round10(P·prodMult/100)`.  Over all of Θ the
non-food multiplier is at most `105` (happy) and `round10` never rounds up, so
`q ≤ 105·(3 + prod)`.  On a non-growth step the extra tile contributes
nothing; on a growth step `work ∪ {extra}` is still a set of distinct tiles, so
`prod ≤ 4` and `q ≤ 735` there as well. -/

/-- Pop-2, non-growth: at most two tiles, total production ≤ 3, so `q ≤ 630`. -/
theorem q_le_630 (prod q : Nat) (hp : prod ≤ 3) (hq : q ≤ 105 * (3 + prod)) :
    q ≤ 630 := by omega

/-- Any step (including a growth step with the extra citizen): `q ≤ 735`. -/
theorem q_le_735 (prod q : Nat) (hp : prod ≤ 4) (hq : q ≤ 105 * (3 + prod)) :
    q ≤ 735 := by omega

/-- Happy growth surplus at pop ≤ 2. -/
theorem e_le_220 (d e : Nat) (hd : d ≤ 2) (he : e ≤ 110 * d) : e ≤ 220 := by omega

/-- Growth surplus at pop 3 (happy tier; content is smaller). -/
theorem e_le_110 (d e : Nat) (hd : d ≤ 1) (he : e ≤ 110 * d) : e ≤ 110 := by omega

/-! ### The Pareto-dual inequalities

At pop 2 and pop 3, food and settler production trade off along the tile
frontier.  The linear form `11·q + 21·e` is the exact dual certificate: it is
maximised by both extremes `(q,e) = (630,0)` and `(420,220)` at pop 2, and by
`(735,0)` / `(630,110)` at pop 3, and no assignment exceeds `9240`.  Note
`11·630 = 6930`, `11·420 + 21·220 = 9240`, `11·735 = 8085`.

The lemma needs the strengthened budget `2·food + prod ≤ 9` (pop 2) resp.
`≤ 13` (pop 3); the budget in `2·food + prod ≤ 4·|work| + 1` supplies exactly
those. -/

theorem budget_pop2 (a : Assign) (h : a.count ≤ 2) : 2 * a.food + a.prod ≤ 9 := by
  have hb := a.budget
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [count] at h
  simp only [food, prod] at hb ⊢
  omega

theorem budget_pop3 (a : Assign) (h : a.count ≤ 3) : 2 * a.food + a.prod ≤ 13 := by
  have hb := a.budget
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [count] at h
  simp only [food, prod] at hb ⊢
  omega

/-- **Pop-2 dual.**  For a non-growth step at pop 2 with food surplus `e` and
credited progress `q`: `11·q + 21·e ≤ 9240`. -/
theorem dual_pop2 (a : Assign) (h : a.count ≤ 2) (q e : Nat)
    (hq : q ≤ 105 * (3 + a.prod)) (he : e ≤ 110 * (a.food - 2)) :
    11 * q + 21 * e ≤ 9240 := by
  have hb := a.budget_pop2 h
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [food, prod] at hq he
  simp only [food, prod] at hb ⊢
  omega

/-- **Pop-3 dual.**  Same linear form on a non-growth step at pop 3. -/
theorem dual_pop3 (a : Assign) (h : a.count ≤ 3) (q e : Nat)
    (hq : q ≤ 105 * (3 + a.prod)) (he : e ≤ 110 * (a.food - 4)) :
    11 * q + 21 * e ≤ 9240 := by
  have hb := a.budget_pop3 h
  have ⟨h0, h1, h2, h3⟩ := a.bounds
  simp only [food, prod] at hq he
  simp only [food, prod] at hb ⊢
  omega

end Assign

/-! ## 3. Summing a play

A play is a list of resolved steps, each carrying the progress it credited
(`q`, zero on non-settler and pop-1 steps by R-SET-9 / A8) and the food surplus
it added (`e`).  The model's `prog` at the end of the play is `Σq`. -/

/-- One resolved step, as seen by the bound. -/
structure Step where
  (q e : Nat)

namespace Step

/-- Total credited settler progress of a play (the model's `prog`). -/
def sumQ (l : List Step) : Nat := (l.map Step.q).sum

/-- Total food surplus generated by a play. -/
def sumE (l : List Step) : Nat := (l.map Step.e).sum

/-- **Dual summation.**  If every step satisfies the dual inequality, so does
the whole play: `11·Σq + 21·Σe ≤ 9240·|play|`. -/
theorem sum_dual (l : List Step)
    (h : ∀ s ∈ l, 11 * s.q + 21 * s.e ≤ 9240) :
    11 * sumQ l + 21 * sumE l ≤ 9240 * l.length := by
  induction l with
  | nil => simp [sumQ, sumE]
  | cons x xs ih =>
    have hx : 11 * x.q + 21 * x.e ≤ 9240 := h x (by simp)
    have hxs : ∀ s ∈ xs, 11 * s.q + 21 * s.e ≤ 9240 := fun s hs => h s (by simp [hs])
    have hih := ih hxs
    simp only [sumQ, sumE, List.map_cons, List.sum_cons, List.length_cons] at hih ⊢
    omega

end Step

/-! ## 4. Horizon arithmetic

The two structural facts supplied by the model are
`n ≥ 7` (pop 2 cannot be reached before step 7: `6·220 = 1320 < T(1) = 1500`)
and `k ≥ 18` (pop 3 cannot be reached before step 18: `17·220 = 3740 <
T(1) + T(2) = 3900`; the total generated food must cover both growth baskets,
and every step adds at most 220).

* **Case A** (pop stays ≤ 2 through the horizon `T`): every credited step is a
  non-growth pop-2 step, so `q ≤ 630`, and there are at most `T - n ≤ T - 7`
  credited steps.  Hence `prog ≤ 630·(T - 7)`: `7560` at `T = 19`, `10710` at
  `T = 24`.
* **Case B** (pop 3 is reached at step `k`): the `m = k-1-n` non-growth pop-2
  steps with credit `q_i` and surplus `e_i` satisfy the dual, the growth step
  and the `T-k` pop-3 steps each credit at most `735`, and the pop-2 steps must
  generate `Emid ≥ 3680 - 220n` food.  This gives
  `11·prog ≤ 9240·m - 21·Emid + 8085·(1 + T - k)`, whose maximum over
  `n ≥ 7, 18 ≤ k ≤ T` is `64785` (`T = 19`) resp. `110985` (`T = 24`); both are
  strictly below `11·cost` (`88000` resp. `121000`).
-/

theorem pop2_not_before_seven : 6 * 220 < 1500 := by decide

theorem pop3_not_before_eighteen : 17 * 220 < 3900 := by decide

/-- Case A at `T = 19`: at most `19 - n ≤ 12` credited steps of value ≤ 630. -/
theorem caseA_19 (prog n : Nat) (hn : 7 ≤ n) (h : prog ≤ 630 * (19 - n)) :
    prog < 8000 := by omega

/-- Case A at `T = 24`: at most `17` credited steps of value ≤ 630. -/
theorem caseA_24 (prog n : Nat) (hn : 7 ≤ n) (h : prog ≤ 630 * (24 - n)) :
    prog < 11000 := by omega

/-- Case B at `T = 19` (Int arithmetic; `Emid` is the food generated by the
pop-2 non-growth steps, `m` their count, `r = 1 + 19 - k` the number of
"high-value" steps after pop 2). -/
theorem caseB_19 (prog n k Emid m r : Int)
    (hn : 7 ≤ n) (hk1 : 18 ≤ k) (hk : k ≤ 19)
    (hm : m = k - 1 - n) (hr : r = 1 + 19 - k)
    (hE : 3680 - 220 * n ≤ Emid)
    (hsum : 11 * prog ≤ 9240 * m - 21 * Emid + 8085 * r) :
    prog < 8000 := by omega

/-- Case B at `T = 24`. -/
theorem caseB_24 (prog n k Emid m r : Int)
    (hn : 7 ≤ n) (hk1 : 18 ≤ k) (hk : k ≤ 24)
    (hm : m = k - 1 - n) (hr : r = 1 + 24 - k)
    (hE : 3680 - 220 * n ≤ Emid)
    (hsum : 11 * prog ≤ 9240 * m - 21 * Emid + 8085 * r) :
    prog < 11000 := by omega

/-! ## 5. Achievability and the limits of the closed form

The witness of `mvp/LOWER-BOUND.md` §3 credits exactly `630` per step from
step 8 on, so these numbers are tight, not slack. -/

/-- `12` credited steps do not pay for the cost-80 settler. -/
example : 630 * 12 < 8000 := by decide

/-- `13` credited steps do (the witness completes at `t = 20`). -/
example : 8000 ≤ 630 * 13 := by decide

/-- `17` credited steps do not pay for the cost-110 settler. -/
example : 630 * 17 < 11000 := by decide

/-- `18` credited steps do (the witness completes at `t = 25`). -/
example : 11000 ≤ 630 * 18 := by decide

/-- **Why the per-step maximum alone is not enough.**  If a step at the
beginning of the credit window could already credit `735` (the pop-3 maximum),
then `11` steps would suffice for cost 80 and `15` for cost 110 — i.e. `t = 18`
resp. `t = 22`, in contradiction with `20 / 25`.  The closed form
`7 + ⌈cost/630⌉` therefore *depends* on the coupling proved in §4 (pop 3 is not
reachable before step 18), not on a global per-step maximum of 630. -/
example : 8000 ≤ 735 * 11 := by decide

example : 11000 ≤ 735 * 15 := by decide

end Civ6Verify.Bounds.MvpArithmetic
