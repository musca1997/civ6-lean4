# LOWER-BOUND.md — analytic lower bound for `M_MVP` (CONDITIONAL, model-internal)

Scope: `mvp/RULE-CONTRACT.md` v2.1, σ = `sigma-capital-4tiles-v1`, claim tag
**CONDITIONAL (not a Civ6 fact)**. This file owns only the lower-bound half of
`OptimalAt`; it does not touch `Civ6Verify/Model/Mvp.lean`, the contract, the
fixture, or the search code.

**Claim discipline.** Nothing here is evidence about the game. `[V] = 0`, no
build is pinned, and every constant is the contract's `[C]`/`[D*]`/`[A]`/
`[ASSUME]`/`[SCENARIO]` value. The result is: *if* a Lean model implements
§4 of the contract exactly, *then* no legal play completes a Settler before
step 20 (cost 80) / step 25 (cost 110). At the time of writing a model module
`Civ6Verify/Model/Mvp.lean` exists but is owned by another agent and still in
progress (it proves the witnesses and `noEarlier_one/two`, not the bound), so
the reduction remains a **bridge obligation** (§7), not a theorem. The
arithmetic core *is* kernel-checked (`Civ6Verify/Bounds/MvpArithmetic.lean`),
and it deliberately does **not** import the in-progress model.

---

## 0. Result

Let `N(θ)` be the exact-step first-completion time of `M_MVP(θ, σ)` (contract
§3–§4), and let `Θ_MVP` be the 128-combination box (§6).

> **Theorem LB-80 (proved modulo bridge).** For every `θ ∈ Θ_MVP` with
> `θ.settlerCost = 80`, every legal play satisfies `trained t = 0` for all
> `t ≤ 19`. Hence `N(θ) ≥ 20`; the witness of §5 gives `N(θ*) = 20`.
>
> **Theorem LB-110 (proved modulo bridge).** For every `θ ∈ Θ_MVP` with
> `θ.settlerCost = 110`, every legal play satisfies `trained t = 0` for all
> `t ≤ 24`. Hence `N(θ) ≥ 25`; the witness of §5 gives `N(θ*) = 25`.

Both bounds are **θ-uniform**: the caps used in §3 hold for all 128 axis
combinations (C2–C7 can only lower a yield or delay a growth, never raise a
cap). Only the cost axis changes the horizon. This is stronger than contract
O7 needs; O7 still governs the *upper* bounds `N(θ) ≤ 20 / 25` and the
certified argmin/argmax `OptimalAt`.

The lower bound is *not* `7 + ⌈cost/630⌉` "because 630 is the per-step
maximum". That reading is false: pop 3 credits up to 735/step. The formula is
a *consequence* of the food ladder (§6). The contract's `handBoundWarning`
(`18 + ⌈(cost−6930)/735⌉ = 24`) is a v1 artefact (banked 6930 at t=18) and is
replaced here; `N = 7 + ⌈cost/630⌉` is exact for this σ, and §6 gives the
counterexample that shows why it is a theorem about σ, not about 630.

**Contract v2.1 §10(iii) is discharged (modulo the bridge).** The contract
lists the pop-3 branch as *unproved* and asks for "an LP/dominance lemma over
the 2-citizen assignments showing every pop-3 line completes no earlier". §3
Lemma 3 + §4.2 is exactly that certificate: the dual `11q + 21e ≤ 9240`
(with `(630,0)` and `(420,220)` both tight) bounds every pop-2 non-growth
step, and the food ladder `Σe ≥ 3900` charges the pop-3 detour. The branch is
dominated with room to spare (`5889` vs `8000` at `t = 19`).

---

## 1. Inputs actually used (and the clauses that are load-bearing)

Everything is read from contract §3–§4. The proof uses only:

1. **No production banking, and no queue carry.** `prog` increases only by
   `CREDIT(q)` with `build = SETTLER`; IDLE steps and every preturn-pop-1 step
   leave `prog` unchanged (R-SET-9, `CREDIT`, A8), and an unmodelled build's
   overflow is **not** carried into the settler (contract §8.1/§12 "idle/queue
   carry": a `≤ 525` carry gives 19/24, review B3b, so this restriction is
   load-bearing here). *This is what makes the pop-1 prefix a pure food rush
   and makes `t = 8` the first possible credited step.*
2. **Prerequisite timing.** `SETTLER` is legal only when the **pre-turn**
   `pop ≥ 2`; same-step growth never retro-legalises it (A8). Equivalently:
   the 1→2 growth step itself credits nothing.
3. **Extra is not a ghost.** `extra` production is added only when a growth
   event fires, and `extra ∉ work`. The totalised form required by the
   semantic review (B1) is
   `extraGain := match a.extra with | none => 0 | some t => prod t`,
   applied **only** inside the `pop1 > pop` branch. §6 shows this clause is
   load-bearing: applying `extraGain` unconditionally (a ghost-output bug)
   moves the optimum to 18 / 22.
4. **Initial state** `pop = 1, food = 0, prog = 0, trained = 0` (A4).
5. **Thresholds** `T(1) = 1500`, `T(2) = 2400`; `T(3) ≥ 3300` is never needed
   (and never crossed here). Growth multipliers: `110` happy, `100` content;
   production multipliers: `105` happy, `100` content, `95` displeased.
6. **σ yields**: centre 2F/1P free + palace +2P (A1) ⇒ base `F₀ = 200`,
   `P₀ = 300`; tiles `G = (2F,0P)`, `GH = (2F,1P)`, `PH = (1F,2P)`,
   `P = (1F,1P)` in units of 1/100; one citizen per tile, no duplicates.
7. **Growth bookkeeping**: `grow` subtracts exactly `T(pop)` when it fires,
   `basket ∈ {zero, subtract}`; surplus `d < 0` is illegal (starvation).
   Neither choice of basket affects this proof (§3 Lemma 4 only needs that the
   generated food covers every threshold).

Not used: O1's layer enumeration, the `[19,25]` variants of semantic review
B3, A1/A2 sensitivity rows (B5), or the starving-relaxation question (B6).
The starvation restriction is not load-bearing for this bound (§4.6).

---

## 2. Exact σ arithmetic

Units: 1/100 fixed point. For a work set `W` and population `p`:

```
F = 200 + Σ_{t∈W} food(t)      P = 300 + Σ_{t∈W} prod(t)
d = F − 200·p                  dpts = d/100 = 2 + f − 2p     (f = Σ food/100)
e = 110·dpts                   (baseline happy tier; ≤ 110·dpts over Θ)
q = 105·(3 + ppts)             (baseline happy, exact rounding; ≤ over Θ)
ppts = Σ prod/100              (P = 100·(3 + ppts))
```

All of `F, P, d` are multiples of 100, so `e` and `q` are integers: no
rounding is hidden. Under `trunc10` `q` is smaller; under content `q = 100·(3+ppts)`;
the caps below use the largest value in Θ.

### 2.1 Tile table (points; multiply by 100 for contract units)

| tile | food | prod | `2·food + prod` |
|---|---|---|---|
| `G`  | 2 | 0 | 4 |
| `GH` | 2 | 1 | 5 |
| `PH` | 1 | 2 | 4 |
| `P`  | 1 | 1 | 3 |

The only tile that exceeds 4 in `2·food + prod` is `GH` (by 1), and there is at
most one `GH`. This single fact is the whole combinatorial input:

```
2·f + ppts ≤ 4·|W| + 1          (per-assignment budget)
```

### 2.2 Work-set frontier (all legal `|W| ≤ p`; dominated rows omitted)

**pop 1** (`|W| ≤ 1`, `d = 100·f`, `e = 110·dpts`):

| W | F | P | d | e | q (uncredited) |
|---|---|---|---|---|---|
| ∅ | 200 | 300 | 0 | 0 | 315 |
| G | 400 | 300 | 200 | **220** | 315 |
| GH | 400 | 400 | 200 | **220** | 420 |
| PH | 300 | 500 | 100 | 110 | 525 |
| P | 300 | 400 | 100 | 110 | 420 |

**pop 2** (`|W| ≤ 2`, `d = 100·(f−2)`):

| W | F | P | d | e | q |
|---|---|---|---|---|---|
| G,GH | 600 | 400 | **200** | **220** | 420 |
| G,PH | 500 | 500 | 100 | 110 | 525 |
| G,P | 500 | 400 | 100 | 110 | 420 |
| GH,PH | 500 | 600 | 100 | 110 | **630** |
| GH,P | 500 | 500 | 100 | 110 | 525 |
| PH,P | 400 | 600 | 0 | 0 | **630** |

Frontier: `(e,q) ∈ {(220,420), (110,630), (110,525), (110,420), (0,630)}`
plus dominated points. **Max e = 220 ⇔ q = 420; max q = 630.**

**pop 3** (`|W| ≤ 3`, `d = 100·(f−4)`):

| W | F | P | d | e | q |
|---|---|---|---|---|---|
| G,GH,PH | 700 | 600 | **100** | **110** | 630 |
| G,GH,P | 700 | 500 | 100 | 110 | 525 |
| G,PH,P | 600 | 600 | 0 | 0 | 630 |
| GH,PH,P | 600 | **700** | 0 | 0 | **735** |

Frontier: `(110,630)` and `(0,735)`; **max e = 110, max q = 735.**

**pop 4** (all four tiles): `F = 800, P = 700, d = 0, e = 0, q = 735`. (pop 4
is unreachable in the horizons used below; the caps still hold if it were.)

**Growth steps.** When growth fires, the new citizen's `extra` tile may add
production to `P` before `q` is computed. Since `extra ∉ work` and tiles are
distinct, `work ∪ {extra}` is a set of distinct tiles, hence
`ppts(work) + prod(extra)/100 ≤ 4` and `q ≤ 105·(3+4) = 735`. Food never
includes `extra`, so `e` is still the `work`-set surplus: `e ≤ 220` at old
pop ≤ 2, `e ≤ 110` at old pop 3.

Consequences used below (`C = 8000` or `11000`):

```
(C1)  credited q ≤ 735 on every step;  q_cred = 0 when pre-turn pop = 1
(C2)  e ≤ 220 on every step  (pop 1,2: 220; pop 3: 110; pop 4: 0)
(C3)  pop 2, no growth this step  ⇒  q ≤ 630
(C4)  pop 2 or 3, no growth       ⇒  11·q + 21·e ≤ 9240   (dual, §3)
```

---

## 3. Four lemmas

### Lemma 1 — no credit before pop 2; earliest pop 2 is `t = 7`

By A8/`PrereqPopulation = 2`, a step with pre-turn `pop = 1` cannot have
`build = SETTLER`, so `CREDIT = 0` and `prog` is unchanged (clause 1).
At pop 1, `d = 100·f ≤ 200` for every work set, so `e ≤ 220` (clause C2).
Starting from `food = 0`, after six steps `food ≤ 6·220 = 1320 < 1500 = T(1)`.
Growth is automatic when the basket fills, so pop 2 cannot occur before step 7,
and the first step whose pre-turn pop is ≥ 2 is step 8. (In particular `n ≥ 7`
for the step `n` at which pop becomes 2.)

### Lemma 2 — caps C1–C3

Immediate from the tables of §2.2. `q` is the *credited* amount, i.e. `q = 0`
unless `build = SETTLER`. Note C3 is about the pre-turn population (`pop = 2`)
and the absence of a growth event in that step; a growth step may reach 735.

### Lemma 3 — dual inequality (the key coupling)

For a **non-growth** step with pre-turn `pop = 2` (and, separately, `pop = 3`):

```
11·q + 21·e ≤ 9240
```

*Proof (pop 2).* `q ≤ 105·(3+ppts)`, `e ≤ 110·(f−2)`, and the per-assignment
budget (§2.1) gives `2f + ppts ≤ 4·2 + 1 = 9`. Hence

```
11q + 21e ≤ 1155·(3+ppts) + 2310·(f−2)
          = 2310f + 1155·ppts − 1155
          ≤ 1155·9 − 1155 = 9240.
```

Equality is attained by both frontier extremes: `(q,e) = (420,220)` and
`(630,0)`. For pop 3 the same computation with `2f+ppts ≤ 13` and
`e ≤ 110·(f−4)` gives `≤ 9240` as well (extremes `(735,0)`, `(630,110)`).
The dual is *false* on a growth step at pop 2: the extra citizen can give
`(e,q) = (220,630)`, i.e. `11q+21e = 11550`. That is why the growth step is
budgeted coarsely at `q ≤ 735` and never enters a dual sum.

### Lemma 4 — the food ladder (pop 3 cannot be reached before `t = 18`)

Suppose pop 3 is reached at step `k`. Two growth events have occurred (1→2 and
2→3), each requiring its basket at the moment it fires. With `basket = subtract`
the generated food must cover both thresholds; with `basket = zero` the
leftovers are discarded, so it must cover them *a fortiori*:

```
Σ_{i=1..k} e_i ≥ T(1) + T(2) = 1500 + 2400 = 3900.
```

Each term is at most 220 (C2; the step `k` itself evaluates `e` at pop 2), so
`220·k ≥ 3900`, i.e. `k ≥ 18` because `17·220 = 3740 < 3900`.

---

## 4. Proof of Theorems LB-80 / LB-110

Fix `T = 19` (cost 80) or `T = 24` (cost 110). Let a play be given. Define the
**cumulative credit** `credit_t` as the sum of the credited `q`'s of steps
`1..t` (on a completion step, `q` is the credit *before* subtracting the cost).
As long as no completion has occurred, `prog_t = credit_t`; a completion at
step `g` requires `credit_g ≥ C`. So it suffices to prove

```
credit_t < C    for every t ≤ T.
```

Apply the argument to the prefix of length `t` (which has no completion before
step `t`; if step `t` completes, its credit is still counted).

Let `n ≥ 7` be the step at which pop becomes 2 (Lemma 1). If pop 2 is never
reached in the prefix, no step is credited and `credit_t = 0 < C`; assume
henceforth that it is reached at step `n`. Steps `1..n` credit nothing, so
only steps `n+1..t` can contribute.

### 4.1 Case A — pop never reaches 3 in the prefix

Then every credited step has pre-turn pop 2 and no growth (pop 3 never occurs),
so by C3 each credits `q ≤ 630`. There are at most `t − n ≤ T − 7` such steps:

```
prog ≤ 630·(T − 7).
```

At `T = 19`: `630·12 = 7560 < 8000`. At `T = 24`: `630·17 = 10710 < 11000`.

### 4.2 Case B — pop reaches 3 at step `k ≤ t`

By Lemma 4, `18 ≤ k ≤ T`. Split the credited steps:

* **middle** steps `n+1 .. k−1`, count `m = k−1−n`: pre-turn pop 2, no growth,
  each satisfying the dual of Lemma 3. Let `Emid = Σ_{i=n+1..k−1} e_i`.
* **growth step** `k`: credited `q_k ≤ 735` (C1).
* **late** steps `k+1 .. t`: pre-turn pop ≥ 3, each credited `q ≤ 735` (C1);
  there are at most `t−k ≤ T−k` of them.

Food bookkeeping: `Σ_{i=1..k} e_i ≥ 3900` (Lemma 4), `Σ_{i=1..n} e_i ≤ 220n`,
`e_k ≤ 220`, hence

```
Emid ≥ 3900 − 220n − 220 = 3680 − 220n.                     (F)
```

Dual summation over the middle steps (Lemma 3, summed; kernel lemma
`Step.sum_dual`) gives

```
11·Σ_middle q + 21·Emid ≤ 9240·m.                           (D)
```

Therefore, using `m = k−1−n` and the coarse `q ≤ 735` on `1 + (t−k) ≤ 1 + (T−k)`
steps,

```
11·prog ≤ 9240·(k−1−n) − 21·Emid + 8085·(1 + T − k)
        ≤ 9240·(k−1−n) − 21·(3680 − 220n) + 8085·(1 + T − k)      [by (F)]
        = 1155·k − 4620·n + (8085·T − 78435).                       (∗)
```

Substituting (F) into (D) is valid because the coefficient of `Emid` is
negative: `Emid ≥ 3680 − 220n` implies `−21·Emid ≤ −21·(3680 − 220n)`. All
arithmetic is in `ℤ`, so no truncated subtraction appears.

Maximise (∗) over the constraints `n ≥ 7`, `18 ≤ k ≤ T` (coefficient of `k` is
`+1155 > 0`, coefficient of `n` is `−4620 < 0`):

```
T = 19:  11·prog ≤ 1155·19 − 4620·7 + 75180 = 64785  < 88000 = 11·8000
         ⇒ prog ≤ 5889 < 8000.
T = 24:  11·prog ≤ 1155·24 − 4620·7 + 115605 = 110985 < 121000 = 11·11000
         ⇒ prog ≤ 10089 < 11000.
```

(In `MvpArithmetic.lean`: `caseB_19` and `caseB_24` prove exactly these two
numeric implications from hypotheses `(F)` and `(D)`.)

### 4.3 Completion timing

The bound is on the cumulative credit through step `t`, including the credit of
a hypothetical completing step `g ≤ T`. A completion at `g` requires
`credit_g ≥ C`, which §4.1/§4.2 exclude. Hence `trained_t = 0` for all
`t ≤ T`. ∎

### 4.4 What the case split buys

Case A is exactly tight: the witness (§5) attains `prog = 630·(t−7)` at every
`t = 8..19`. Case B is far from tight (`5889` proved, `5670` measured at
`t = 19`; `10089` proved, `9870` measured at `t = 24`), because it charges the
full food ladder against progress. The split is essential: see §8.

### 4.5 Uniformity over Θ

Replacing each axis value by its worst case for this proof:

| axis | worst case | effect on the proof |
|---|---|---|
| C1 cost | 80 / 110 | horizon `T` |
| C2 turn order | `production_first` | same caps; credit is computed at pre-turn pop, so `q ≤ 630` at pop 2 even on growth steps |
| C3 new citizen | `best` | only growth steps; absorbed by `q ≤ 735` |
| C4 amenity stock | 1 ⇒ content at pop 3 | `e ≤ 100`, `q ≤ 700`: caps C1–C4 still hold |
| C5 basket | `zero` | discards carry: Lemma 4 unchanged (generated food must still cover 3900) |
| C6 rounding | `exact` | largest `q`; `trunc10` only lowers it |
| C7 `T(3)` | 3300/3383 | affects pop 4 only (≥ 30 further steps); caps hold at pop 4 anyway |

So both lower bounds hold for every θ with the stated cost (128/128 given the
cost), and no inertness lemma for C2–C7 is needed *for this half* of `OptimalAt`.

### 4.6 Starvation restriction is irrelevant here

Even if actions with `d < 0` were allowed, `e` would only decrease (with
`e < 0` the inequality `11q + 21e ≤ 11q ≤ 6930 ≤ 9240` still holds at pop 2),
`q` still satisfies C1/C3, and Lemma 4 still requires `Σe ≥ 3900` at the
moment pop 3 is reached. The conclusion is unchanged; the restriction is *not*
load-bearing for this lower bound (it is for the achievability witness, which
is idle- and starvation-free). The model's `legal_surplus` enforces `e ≥ 0`,
so this is only a robustness remark, not a case the Lean statements cover.

---

## 5. Tightness: the witness (regenerated, not hand-edited)

Baseline θ* (cost 80, happy, growth_first, `newCitizen = best`, zero basket,
exact rounding). `GH` yields `(F,P) = (400,400)`, `d = 200`; `GH+PH` yields
`(500,600)`, `d = 100`.

| steps | pre-pop | work | build | e | q | food | prog |
|---|---|---|---|---|---|---|---|
| 1–7 | 1 | `GH` | IDLE (extra `⊥`) | 220 | 420 (uncredited) | 220→1540 at t=7, growth, basket → 0 | 0 |
| 8–19 | 2 | `GH,PH` | SETTLER | 110 | 630 | 0 → 1320 | 0 → 7560 |
| 20 | 2 | `GH,PH` | SETTLER | 110 | 630 | 1430 | 8190 ≥ 8000 ⇒ **goal**, pop → 1 |

At `t = 19` the witness has exactly `630·12 = 7560` progress, matching the
case-A bound. For cost 110 the same prefix continues `GH,PH` through step 25:
`17·630 = 10710 < 11000` at `t = 24`, `18·630 = 11340 ≥ 11000` at `t = 25`.

The table is the contract-v2.1 canonical line: `build = IDLE ⇒ extra = ⊥`, so
the growth row also has `q = 420` (525→420 was the B1 fix). The basket is
emptied (`zero`), discarding the 40 overflow, so the settler phase starts from
`food = 0`. The Lean model currently uses a different (equally uncredited)
canonicalisation: its legality requires `extra` to be present *iff* the step
grows, so its growth row takes `extra = P` and `q = 525`; it proves
`witness_growth_q = 525`, `witness_settler_q = 630` and
`witness_after_nineteen = (pop 2, food 1320, prog 7560, trained 0)`. The
difference is an uncredited row under both action sets, so `N` is unaffected.

---

## 6. The closed form and why "630 globally" is invalid

**Correct statement.** For this σ, the search enumeration reports
`N(θ) = 7 + ⌈cost/630⌉` for all 128 θ (`20` for cost 80, `25` for cost 110).
What is *proved* here is the `≥` half for every θ (§4) and the `=` for the
baseline θ* (§5 witness); the upper bounds for the other 127 θ remain per-θ
witness obligations (O5) or search estimates. The formula's proof is not a
per-step maximum:

* `630` is only the maximum **credited** `q` at pop 2 without growth. Pop 3
  credits **735** (`GH,PH,P`: `F = 600, d = 0, P = 700`), and a growth step can
  credit 735 via `extra` as well.
* The naive "if 735 were available from step 8" model completes at
  `7 + ⌈8000/735⌉ = 18` (cost 80) and `7 + ⌈11000/735⌉ = 22` (cost 110):
  `735·11 = 8085 ≥ 8000`, `735·15 = 11025 ≥ 11000`. So a per-step maximum of
  735 would **falsify** `20/25`. The formula survives only because of the food
  ladder: pop 3 is unreachable before step 18 (Lemma 4), and reaching it costs
  3900 food, which forces the low-production frontier.
* Equivalently: the closed form is *not* valid under the weakened premise
  "`q ≤ 735` from the first credited step"; `MvpArithmetic.lean` records
  `8000 ≤ 735·11` and `11000 ≤ 735·15` as the explicit counterexample numbers.
  (A concrete rule change with the same effect: `T(2) = 0`, so pop 3 is
  immediate. Then 18/22 are achievable, and `7 + ⌈cost/630⌉` is wrong.)

**Why the case-B branch cannot be ignored.** The analytic case-B bound is
5889 at `t = 19` and 10089 at `t = 24`; the measured maxima over pop-3 lines
are 5670 and 9870 (search estimate, §10). Both are dominated by case A
(7560 / 10710), but only because 3900 food is very expensive at this frontier:
the food-max assignment `G,GH` yields `q = 420`, while the production-max
assignment `GH,PH` yields only `e = 110`.

**Stale hand-bound (contract §10).** The paragraph
`18 + ⌈(cost−6930)/735⌉ = 24` reuses v1's *banked* 6930 at `t = 18`. Under v2
`prog = 0` until step 8 and pop 3 cannot appear before step 18, so no path
carries 6930 at `t = 18` except the no-pop-3 max-production line, which is
already case A. The "missing coupling" the old paragraph inferred does not
exist; (∗) is that coupling. Replace it with §4 and the closed form above
(semantic review B2).

**Load-bearing semantics.** Each row drops/changes one clause of contract v2.1;
the numbers are first-completion steps (cost 80 / 110).

| dropped clause | first completion (80 / 110) | source |
|---|---|---|
| R-SET-9 / A8 (banking across the pop-2 gate) | 15 / 20 | v1; void, contract FIX-1 |
| A8 build chosen after growth | 19 / 24 | semantic review B3a |
| `extraGain` applied without a growth event (ghost output) | **18 / 22** | this document, exact-step enumeration |
| one-item queue carry into the settler (`≤ 525`) | 19 / 24 | review B3b; contract §12 |
| no starvation restriction | 20 / 25 (unchanged) | review B6; §4.6 argument |

The third row is the reason the contract's FIX-3/B1 totalisation must be
implemented as "`extra` contributes nothing unless a growth event fires", not
merely as "`extraGain` is total". The fourth row is the "no queue carry"
restriction of §8.1: it is a *restriction* (it can only raise `N`), so the
lower bound is conditional on it. The current model does the third correctly:
`production s a = baseProd a + (if wouldGrow s a then extraProd a else 0)`.

---

## 7. Bridge obligations (model lemmas that turn §3–§4 into a Lean theorem)

The arithmetic is proved. The missing link is a Lean model `M_MVP` (owned by
the model agent) plus the following lemmas. Suggested shapes (namespace
`Civ6Verify.Model.Mvp`; adapt to the actual API):

**B-1 (credit rule).** `prog` changes only by credited `q` on `SETTLER` steps;
on IDLE steps and on all pre-turn-pop-1 steps it is unchanged, and `trained`
is monotone. The current API is total (`step : Params → State → Action →
State`), and already provides `step_idle_prog`, `step_idle_trained`,
`goal_step`, `step_trained_ge`; what remains is the pop-1 case:

```lean
theorem credit_zero_of_prePop_lt_two (p : Params) {s : State} {a : Action}
    (hl : legal s a) (hpop : s.pop < 2) : credit a (qOf s a) = 0
-- proof: a.build = .idle from legal_settler_pop (contrapositive), then `credit`
theorem prog_step (p : Params) (s : State) (a : Action) :
    (step p s a).prog = s.prog + credit a (qOf s a) ∨
    ((step p s a).prog + p.cost = s.prog + credit a (qOf s a) ∧
      (step p s a).trained = s.trained + 1)
```

**B-2 (extra totalisation).** `extra` contributes only on a growth event, and
only if unworked. In the current model this is structural:
`production s a = baseProd a + (if wouldGrow s a then extraProd a else 0)`,
`extraProd ⟨_, none, _⟩ = 0`, and legality gives `extraUnworked a = true`
(`extraUnworked_spec`, `legal_extra_not_work`). The model's canonicalisation
`wouldGrow s a = true ↔ a.extra.isSome = true` is *stronger* than the contract
(it forces an extra on growth steps and forbids one otherwise); it removes
actions, so it preserves a lower bound and structurally blocks the ghost-extra
failure mode of §6.

**B-3 (per-step caps).** For every reachable `s` and legal `a` with successor
`s'`, writing `e := growthAmount s a` and `q := credit a (qOf s a)` (the
credited amount, so `q = 0` for `idle`):

```lean
theorem q_le_735 : q ≤ 735
theorem e_le_220 : e ≤ 220
theorem q_le_630_of_noGrowth : s.pop = 2 → wouldGrow s a = false → q ≤ 630
theorem dual2 : s.pop = 2 → wouldGrow s a = false → 11*q + 21*e ≤ 9240
theorem dual3 : s.pop = 3 → wouldGrow s a = false → 11*q + 21*e ≤ 9240
```

Suggested derivations against the current API:

* `q_le_735`: `production s a ≤ 700` because `work ∪ {extra}` is a set of at
  most four distinct tiles with total production 400 (`workTiles` is a
  duplicate-free mask list, `legal_extra_not_work`), and `prodMult ≤ 105`;
  then `qOf s a ≤ 700·105/100 = 735`.
* `e_le_220`: `legal_surplus` gives `200·pop ≤ baseFood`, and at pop ≤ 2
  `baseFood ≤ 600`, so `surplus ≤ 200`; `growthMult ≤ 110`.
* `q_le_630_of_noGrowth`: at pop 2 and no growth, `legal_no_growth_extra`
  gives `a.extra = none`, so `production = baseProd ≤ 600`; `prodMult ≤ 105`.
* `dual2`/`dual3`: instantiate `Assign.dual_pop2/3` after mapping the mask
  `a.work.val` to the four indicators (`Nat.testBit`) and reading off
  `workFood/100 = Assign.food`, `workProd/100 = Assign.prod`,
  `workCount = Assign.count`; then `qOf ≤ 105·(3+prod)` and
  `growthAmount ≤ 110·(food−2)` resp. `110·(food−4)` on non-growth steps.

`MvpArithmetic.Assign` covers **all** `|work| ≤ pop`, including the idle-citizen
relaxation, so no legal mask can escape the caps. I re-checked the first three
against the current model snapshot by kernel evaluation in a scratch file
(read-only): for all `16 × 5` mask/extra pairs with `extraUnworked`,
`baseProd + extraProd ≤ 700` and `(baseProd + extraProd)·105/100 ≤ 735`, and
concretely `qOf (pop 2) (GH,PH) = 630`, `qOf (pop 3) (GH,PH,P) = 735`,
`growthAmount (pop 2) (G,GH) = 220`, `qOf (pop 2, food 2200) (G,GH + extra PH) = 630`.

**B-4 (food ladder).** In the current API `foodAfter s a = 0` on a growth step
(basket zero) and `foodAfter s a = s.food + growthAmount s a` otherwise, and
`wouldGrow` is `s.food + growthAmount s a ≥ threshold s.pop`. Consequence:

```lean
theorem credit_free_prefix : ∀ t ≤ 6, ∀ s, Reachable t s → s.pop = 1
theorem pop2_time : ∀ s, Reachable n s → s.pop = 2 → 7 ≤ n
theorem pop3_food : pop3 reached at k → 3900 ≤ Σ_{i≤k} e i
theorem pop3_time : pop3 reached at k → 18 ≤ k
```

**B-5 (accounting identities).** `credit_t = Σ_{i≤t} q_i` while `trained = 0`;
a first completion at `g` implies `credit_g ≥ cost`; `m = k−1−n` middle steps
and `1 + (t−k)` late steps; `Emid` as in §4.

**B-6 (assembly).** Case split on "pop 3 reached in the prefix". Case A:
`Nat` multiplicity bound + `caseA_19`/`caseA_24`. Case B: `Step.sum_dual`
(§3) + `(F)` + `caseB_19`/`caseB_24`. Then:

```lean
theorem no_goal_before_20 (p : Params) (hcost : p.cost = 8000) :
    ∀ t ≤ 19, ∀ s, Reachable (model p) t s → s.trained = 0
theorem no_goal_before_25 (p : Params) (hcost : p.cost = 11000) :
    ∀ t ≤ 24, ∀ s, Reachable (model p) t s → s.trained = 0
```

The current `Params` only parameterises `cost`; C2–C7 are fixed at the baseline
values in `Mvp.lean`, so these two theorems are the immediate targets, and the
θ-uniform statement of §4.5 remains a statement about the contract family
until the model parameterises the other axes (or variant models are built).

`MvpArithmetic.lean` is deliberately free of any model import, so B-1..B-6 can
be proved against the model without touching this file (and without a
circular dependency on an in-progress module). A completeness check for B-3 is
worth doing: `MvpArithmetic.Assign` covers all `|work| ≤ pop` (idle citizens
included), so no enumeration branch can escape the caps; the only model-side
gap would be a *ghost* `extra` (see §6), which the current model's
`production` definition rules out by construction.

---

## 8. Invariant candidate, and why a single scalar potential fails

The formal proof is a **disjunctive invariant** on the prefix:

```
INV(t)  :=  (pop ≤ 2 throughout  ∧  11·prog ≤ 11·630·(t − n))
        ∨   (pop 3 at k ≥ 18       ∧  11·prog + 21·Emid ≤ 9240·(k−1−n)
                                     ∧  … and prog's late part ≤ 735·(1+t−k))
```

Both disjuncts are inductive: case A is preserved because a non-growing pop-2
step credits ≤ 630 and a pop-2→3 growth switches to case B; case B is preserved
by the dual (middle steps), the 735 cap (growth/late steps) and the food
ladder.

A *single* scalar potential with a uniform per-step cap does **not** prove both
costs. For the family

```
Φ_λ = 11·prog + λ·(food + 1500·[pop ≥ 2] + 2400·[pop ≥ 3])
```

the growth/consumption terms cancel exactly, so `ΔΦ_λ = 11q + λe`; over the
pop-2 non-growth frontier the cap is `c₂(λ) = 6930 + 110λ` for `0 ≤ λ ≤ 21`
(attained at `(e,q) = (110,630)`), the growth/pop-3 cap is
`c_H(λ) = 8085 + 220λ`, and pop-1 steps satisfy `ΔΦ_λ ≤ 220λ`. At `T = 24`
this gives

```
case A (n = 7):       11·prog ≤ 117810 + 1910λ
case B (k = 18):      11·prog ≤ 125895 +  280λ
```

Case B already exceeds `121000 = 11·11000` at `λ = 0` (`11445`), while the
dual weight `λ = 21` needs `157920` in case A (`14356`); both expressions
increase in `λ`, and `λ > 21` only raises `c₂`, so no member of the family
closes both cases at cost 110. The split is what makes the bound uniform:
pure counting (`λ = 0`, i.e. `q ≤ 630`) is sharp in case A, and the dual
(`λ = 21`, i.e. `11q + 21e`) is sharp only on the pop-2 non-growth steps of
case B, where the food lower bound `Emid ≥ 3680 − 220n` can be charged against
progress. (For cost 80, `λ = 0` happens to suffice for both branches
`12·630 + 2·105 = 7770 < 8000`; the obstruction is a cost-110 phenomenon.)

Hence the formal proof uses the disjunctive invariant above rather than a
single potential.

---

## 9. Lean artifact and verification

`Civ6Verify/Bounds/MvpArithmetic.lean` (new, owned by this task; no model
import, no edits elsewhere):

* `Tile`, `foodPts`, `prodPts`, `per_tile_budget` : `2·food + prod ≤ 4 + [t=GH]`;
* `Assign` with `budget`, `food_le_pop1..pop4`, `prod_le_pop2/pop3`,
  `dpts_pop2/pop3/pop4`, `q_le_630`, `q_le_735`, `e_le_220`, `e_le_110`,
  `budget_pop2/3`, `dual_pop2/3`;
* `Step.sum_dual` : per-step dual facts sum over a play;
* `pop2_not_before_seven`, `pop3_not_before_eighteen`;
* `caseA_19/24`, `caseB_19/24` : the exact numeric endpoints of §4;
* the tightness/counterexample numbers of §5–§6.

Trust: no `sorry`, no custom axioms, no `native_decide`; the project axiom
audit passes with only `propext` and `Quot.sound`. No root/lakefile edit was
needed: `Civ6Verify.lean` and `lakefile.toml` are untouched, and the new
module is picked up by the `Civ6Verify` library globs (`lake build` builds it;
`scripts/audit-axioms.py` audits it).

```bash
scripts/lean-env lake build Civ6Verify.Bounds.MvpArithmetic   # 2 jobs, OK
python3 scripts/audit-axioms.py                               # PASS
```

The audit's public-theorem count includes the concurrently landing
`Civ6Verify/Model/Mvp.lean`; it was ≈475 at the time of writing and changes as
that module grows. This module contributes its ~30 theorems with no extra
axioms.

---

## 10. Independent cross-check (search estimate, untrusted)

Not a certificate and not part of the proof. An independent exact-step
enumeration of contract §3–§4 (baseline θ, full powerset action set, `|work| ≤
pop`, `extra ∈ tiles \ work ∪ {⊥}`) reproduces:

| quantity | value |
|---|---|
| max `prog` at `t = 19` (cost 80, no completion) | **7560** (= case-A bound, attained) |
| max `prog` at `t = 19`, pop-3 lines only | 5670 (analytic bound 5889) |
| max `prog` at `t = 24` (cost 110, no completion) | **10710** (= case-A bound) |
| max `prog` at `t = 24`, pop-3 lines only | 9870 (analytic bound 10089) |
| first completion, cost 80 / 110 | 20 / 25 |
| ghost-`extra` variant (outside contract) | 18 / 22 |
| A8-false variant (outside contract) | 19 / 24 (review B3a) |
| starvation allowed (`d < 0`) | 20 / 25 (review B6) |

Minimal reproduction (state = `(pop, food, prog, trained)`, layers deduplicated):

```python
from itertools import combinations
T = [("G",200,0),("GH",200,100),("PH",100,200),("P",100,100)]
def actions(pop):
    for r in range(pop+1):
        for W in combinations(range(4), r):
            for e in [None]+[i for i in range(4) if i not in W]:
                yield W, e
def step(st, act, cost=8000, basket="zero"):
    pop, food, prog, done = st; W, e = act
    for build in (0, 1):
        if build == 1 and pop < 2: continue
        if build == 0 and e is not None: continue
        F = 200 + sum(T[i][1] for i in W); P = 300 + sum(T[i][2] for i in W)
        if F < 200*pop: continue
        ef = (F - 200*pop)*110//100
        p1, f1 = (pop+1, 0) if food+ef >= {1:1500,2:2400,3:3383}.get(pop, 4420) else (pop, food+ef)
        if e is not None and p1 > pop: P += T[e][2]          # extra only on growth
        q = P*105//100
        prog1 = prog + (q if build == 1 else 0)
        if build == 1 and prog1 >= cost:
            yield (p1-1, f1, prog1-cost, done+1); continue
        yield (p1, f1, prog1, done)
# BFS layers 0..H, report max prog per layer and first layer with done>=1
```

This agreement is a consistency check on the *arithmetic*, not a proof and not
game evidence; the contract's O7 labels it a search estimate.

---

## 11. What this does not claim, and what would falsify it

* **Not a Civ6 fact.** `[V] = 0`, no build pinned: 80/110, palace `+2P`, the
  Happy tier table, `T(1) = 15`, `req(pop)`, `PrereqPopulation = 2` all remain
  `[C]/[D*]/[A]`. The statement is an interval in a restricted model, never an
  "earliest Settler in Civ 6" answer.
* **Conditional on the v2.1 semantics *and* its restrictions.** §6 lists the
  counterexamples for dropping no-banking, A8, the no-ghost-`extra` clause or
  the no-queue-carry restriction; each moves the optimum by 1–5 steps. The
  lower bound is *not* robust to those changes; in particular a `≤ 525`
  queue carry makes 19 achievable, so the honest width without that
  restriction is the review's `[19, 25]`.
* **Falsifiers of the lower bound itself:** a model bug that credits `q` on
  IDLE/pop-1 steps (v1: 15/20), applies `extra` without a growth event
  (18/22), chooses the build after growth (A8 false: 19/24), carries queue
  overflow into the settler (19/24), or has `T(1) < 7·220` (pop 2 too early).
  A1 palace `+0/+1` and A2 tiles-only multipliers do **not** falsify the lower
  bound — they only lower `q`, so `N ≥ 20/25` still follows. They do falsify
  the *matching upper bound* and the exact closed form (`q = 615` ⇒ `21/25`),
  and A1 `+0/+1` pushes the horizon to `27/33` and `23/28` (why contract v2.1
  raised `H` to 34). A1 palace `+3` is the opposite: `q` at pop 2 rises to
  `735` (`GH,PH` with `P = 700`), the dual fails, and the contract's own
  sensitivity row gives `18/22` — exactly the "735 from step 8" counterexample
  of §6. A1 is therefore load-bearing for the lower bound, not just for `N`.
* **What remains for a certified `OptimalAt`:** the upper bounds (witnesses,
  O5) and the per-θ model instantiation (bridge B-1..B-6). The lower bound
  itself is uniform over Θ, so it does not need the 128 per-θ enumeration; the
  enumeration is needed only for the *exact* `N(θ)` claims and the envelope.

---

## Appendix A — algebra of (∗), for audit

```
11·prog ≤ 9240(k−1−n) − 21·Emid + 8085(1+T−k)
Emid ≥ 3680 − 220n
⇒ 11·prog ≤ 9240k − 9240 − 9240n − 77280 + 4620n + 8085 + 8085T − 8085k
            = 1155k − 4620n + 8085T − 78435
T = 19: 8085·19 − 78435 = 75180
        1155·19 − 4620·7 + 75180 = 21945 − 32340 + 75180 = 64785 < 88000
T = 24: 8085·24 − 78435 = 115605
        1155·24 − 4620·7 + 115605 = 27720 − 32340 + 115605 = 110985 < 121000
```

`64785/11 = 5889.5…`, `110985/11 = 10089.5…`; both endpoints are integers, so
`prog ≤ 5889` resp. `≤ 10089` in `ℕ`.

## Appendix B — mapping document ↔ Lean

| document | `MvpArithmetic.lean` |
|---|---|
| §2.1 budget | `per_tile_budget`, `Assign.budget` |
| §2.2 pop-2/3 frontier caps | `food_le_pop2/3`, `prod_le_pop2/3`, `dpts_pop2/3` |
| C1/C2/C3 | `q_le_735`, `e_le_220`, `q_le_630` |
| Lemma 3 dual | `budget_pop2/3`, `dual_pop2/3` |
| Lemma 4 ladder | `pop2_not_before_seven`, `pop3_not_before_eighteen` |
| §4.1 | `caseA_19`, `caseA_24` |
| §4.2 (D)+ (F) summation | `Step.sum_dual` |
| §4.2 (∗) endpoints | `caseB_19`, `caseB_24` |
| §5 tightness | examples `630*12 < 8000 ≤ 630*13`, likewise 110 |
| §6 counterexample | examples `8000 ≤ 735*11`, `11000 ≤ 735*15` |
