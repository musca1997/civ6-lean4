# EXECUTABLE.md — `M_MVP` v2.1 executable and frozen candidate

> **Status: untrusted executable check, not a Lean proof, not a Civ6 fact.**
> This file describes `search/mvp.py`, which implements the step relation of
> `mvp/RULE-CONTRACT.md` (v2.1) for the frozen scenario σ and candidate box Θ. The
> Python search is a candidate generator: Lean remains the authority. Every `N`
> below is model-internal and conditional on A1–A8 and the §8 restrictions.
> There is no claim about the real game, no build pin, no `[V]` claim, and no
> certificate. The only files owned by this work are `search/mvp.py`,
> `fixtures/mvp-baseline.json`, and this document.

---

## 1. Inputs and scope

| item | value used here |
|---|---|
| rule fixture | `fixtures/mvp-rule-candidates.json` (`version: "2.1"`) |
| scenario | `sigma-capital-4tiles-v1` |
| initial state | `s0 = (pop=1, food=0, prog=0, trained=0)` |
| goal | `trained ≥ 1` (monotone history counter) |
| θ box | 7 binary axes, `|Θ| = 128` |
| numeric scale | integers in 1/100 units; no float/Fraction anywhere |
| **execution horizon** | **H = 27** (the task's cap) |
| contract horizon | **H = 34** (v2.1); see limitation `L-HORIZON` in the fixture |

The contract was updated while this executable was written: v2.1 uses `H = 34`
and an `O6b horizonOk` obligation. The task for this executable explicitly caps
the search at `H ≤ 27`. All minimality searches here use `H = 27`; every one of
the 128 θ reaches the goal by `N ≤ 25`, so this cap does not affect any reported
`N`. The `H = 34` guard/sensitivity envelope is **not** checked here.

σ (scenario data, not a game-fact claim):

| element | value (1/100) |
|---|---|
| city centre | `2.00 F / 1.00 P`, free, never assignable |
| palace | `+2.00 P`, `+1` housing, `+1` amenity |
| tiles | `G 2F/0P`, `GH 2F/1P`, `PH 1F/2P`, `P 1F/1P` |
| tile capacity | 1 citizen/tile, no duplicates, centre excluded |
| thresholds | `T(1)=1500`, `T(2)=2400`, `T(3)=3300` (floor) or `3383` (exact), `T(4)=4420` (defined, never reached) |
| settler cost | `C = 8000` (axis 80) or `11000` (axis 110), 1/100 P |
| baseline θ | `(80, growth_first, best, 2, zero, exact, exact)` |
| cost-110 twin | same θ with `settlerCost=110` |

---

## 2. Exact step equations

Notation: `W = a.work` is a finite set of tiles, `p = s.pop`, `b = s.food`,
`r = s.prog`, `tr = s.trained`. `f_t`, `p_t` are tile food/production (the step's production credit is `q`).
`A = θ.amenityStock`.

### 2.1 Derived yields and tier

```
req(p)      = max(0, floor((p-1)/2))
tier(p)     = Happy       if A - req(p) in {1,2}
              Content     if A - req(p) = 0
              Displeased  if A - req(p) in {-2,-1}
              (Ecstatic / below-Displeased are outside the MVP table and raise)
growthMult(p) = 110 (Happy) | 100 (Content) | 85 (Displeased)   # per cent
prodMult(p)   = 105 (Happy) | 100 (Content) | 95 (Displeased)   # per cent

F  = 200 + sum_{t in W} f_t                    # extra NEVER contributes food
P0 = 300 + sum_{t in W} p_t                    # 300 = centre 100 + palace 200
extraGain(e) = 0 if e = none else p_e          # TOTAL (v2.1 / B1)
```

### 2.2 Finite actions and legality

The literal finite action box is

```
actionBox(p) = { (W, e, build) :
                 W in powerset(tiles), |W| <= p,
                 e in {none} ∪ tiles,
                 build in {SETTLER, IDLE} }
```

Capacity/occupancy/structure (`structuralLegal`):

```
|W| <= p
e = none  or  (e in tiles  and  e notin W)
build = IDLE     => e = none
build = SETTLER  => p >= 2                 # PRE-TURN population, not post-growth
```

`step` additionally returns `none` when the relevant post-modifier surplus is
negative. Therefore:

```
legal(s,a)  :=  (step(s,a)).isSome
```

This is the contract's `O2b`. The raw box and the structural filter are both
exposed because the contract also writes `O2` as `a ∈ allActions`:

| population | full product | capacity-filtered box | structuralLegal | idle-free structural |
|---:|---:|---:|---:|---:|
| 1 | 160 | 50 | 5 | 4 |
| 2 | 160 | 110 | 50 | 24 |
| 3 | 160 | 150 | 62 | 12 |

`full product` is the literal `powerset(16 masks) × 5 extra options × 2 builds
= 160` used by the Lean porter's `allActions`; the capacity filter is applied by
`legalGuard` there. `actionBox(pop)` in this executable applies the capacity
filter while constructing the enumerable box (50/110/150). The contract's
`≤ 62 actions/state (pop 3)` is the **structural** count. A Lean porter may take
`allActions := full product` or the structural box and `legal := step.isSome`;
starving tuples then have `step = none`. Alternatively define
`allActions := box.filter (fun a => (step θ s a).isSome)` to make O2 literal.

### 2.3 Growth and rounding

```
grow(b, p) = (p+1, 0)          if b >= T(p) and basket = zero
             (p+1, b - T(p))   if b >= T(p) and basket = subtract
             (p, b)            otherwise

round10(x) = x                 if productionRounding = exact
             10 * floor(x/10)  if productionRounding = trunc10
CREDIT(q)  = q                 if build = SETTLER
             0                 if build = IDLE
```

Only one growth per step is performed (`G3`). `T(3)` is `3300` for
`thresholdRounding=floor`, `3383` for `exact`; `T(1)`, `T(2)`, `T(4)` are fixed.

### 2.4 `growth_first`

```
d = F - 200*p
require d >= 0                                  # otherwise step = none
e = d * growthMult(p) / 100                     # exact division enforced
(p1, b1) = grow(b + e, p)

P = P0
if p1 > p and θ.newCitizen = best:
    P = P + extraGain(a.extra)                  # 0 for none; never food

q    = round10(P * prodMult(p1) / 100)
prog1 = r + CREDIT(q)

if build = SETTLER and prog1 >= C:
    (p1 - 1, b1, prog1 - C, tr + 1)
else:
    (p1, b1, prog1, tr)
```

### 2.5 `production_first`

The normative pseudocode has **no new-citizen term** in this branch; `extra` is
therefore unused here.

```
q     = round10(P0 * prodMult(p) / 100)
prog1 = r + CREDIT(q)
done  = (build = SETTLER and prog1 >= C)
p1    = p - (if done then 1 else 0)
prog1 = prog1 - (if done then C else 0)

d = F - 200*p1
require d >= 0                                  # otherwise step = none
e = d * growthMult(p1) / 100                    # exact division enforced
(p2, b2) = grow(b + e, p1)

(p2, b2, prog1, tr + (if done then 1 else 0))
```

Food is not reset by completion (`R-SET-8`). `prog` is settler-specific; IDLE
and all pop-1 steps leave it unchanged. Selection is fixed at the pre-turn state,
so a growth event cannot retro-legalise `SETTLER` (`A8`).

### 2.6 Exact-step reachability and optimality

```
reach(0)   = {s0}
reach(t+1) = ⋃_{s ∈ reach(t)} ⋃_{a ∈ allActions(s)} step(s,a)
Goal(s)    = (s.trained >= 1)

OptimalAt(θ, n) :=
    (∃ s ∈ reach(n), Goal(s))
  ∧ (∀ t < n, ∀ s ∈ reach(t), ¬ Goal(s))

N(θ) = the least n ≤ H with OptimalAt(θ,n), or none if unreached
```

Deduplication is inside a layer only; the parent map is per layer. The search
stops at the first goal layer, so the certificate's `no_goal_before` obligation
is true by construction and is re-checked by the replay tests.

All multipliers are applied once per step to that step's yield; the state only
accumulates by integer addition. The implementation raises `ExactnessError` if
`d * growthMult` or `P * prodMult` is not divisible by 100, instead of silently
flooring. With the frozen σ/Θ, `F`/`P` are multiples of 100 and every live
`d` is a multiple of 100, so `e` and the pre-rounding `q` are integers.

---

## 3. API for a Lean porter

Suggested surface (names only; this is not a second contract):

```lean
inductive Build | SETTLER | IDLE
structure Action where
  work  : Finset Tile
  extra : Option Tile
  build : Build

structure State where
  pop food prog trained : Nat

structure Theta where
  settlerCost        : Nat          -- 8000 | 11000
  turnOrder          : TurnOrder    -- growth_first | production_first
  newCitizen         : NewCitizen   -- best | none
  amenityStock       : Nat          -- 2 | 1
  basketOnGrowth     : Basket       -- zero | subtract
  productionRounding : Rounding     -- exact | trunc10
  thresholdRounding  : Threshold    -- exact | floor

def actionBox        : Nat -> Finset Action          -- powerset × Option Tile × Build
def structuralLegal  : Nat -> Action -> Bool         -- §2.2
def step             : Theta -> State -> Action -> Option State
def legal            : Theta -> State -> Action -> Prop := (step θ s a).isSome
def successors       : Theta -> State -> Finset State
def reach            : Theta -> Nat -> Finset State
def Goal             : State -> Prop := 1 <= s.trained
def OptimalAt        : Theta -> Nat -> Prop
def N                : Theta -> Option Nat           -- none = unreached within H

theorem step_total :
  legal θ s a -> ∃ s', step θ s a = some s'

theorem goal_monotone :
  legal θ s a -> (step θ s a).getD s |>.trained >= s.trained

def mulDiv100 (x m : Nat) (h : 100 ∣ x * m) : Nat := x * m / 100
-- e and the pre-rounding q are defined through this divisibility obligation.
```

Cross-walk to the existing `mvp/LEAN-MODEL.md` / `Civ6Verify.Model.Mvp`
names (the Lean module is the porter; this table is only a naming aid):

| executable | Lean module |
|---|---|
| `action_box(pop)` (capacity-filtered) | `allActions` (full 160) filtered by `legalGuard`; `legalActionsFor` |
| `structurally_legal(pop,a)` | `legalGuard s a` without its surplus conjunct (structural clauses only) |
| `step(theta,s,a)` | `step? p s a`; total core `step p s a` |
| `legal(theta,s,a)` | `Model.legal` / `legalGuard s a` / `(step? p s a).isSome` (growth_first surplus included) |
| `successors` | `legalActions` |
| `goal(s)` | `goal` |
| `witness_rows` / `verify_witness` | `witness`, `witness110`, `LegalPath` |

Porter notes:

1. **`allActions` vs `legal`.** The contract's §3 has both `legal ↔ a ∈
   allActions` (O2) and `legal := step.isSome` (O2b). Use the structural box for
   `allActions` and `step.isSome` for `legal`; starving tuples are in the box but
   map to `none`. If O2 must be literal, `allActions` is the filtered viable set.
   The raw/structural/viable counts are all reported in the fixture.
2. **`prod(extra)` is total.** `extra = none` gives `extraGain = 0`; the old
   "extra exists by legality" sentence is not used.
3. **`newCitizen` is only a `growth_first` term.** `production_first` is exactly
   the pseudocode, with no extra/new-citizen production.
4. **No carry.** IDLE credits nothing and there is no unmodelled-item overflow
   carry into the settler; this is the contract's no-carry restriction, not a
   claim about real games.
5. **Starvation.** A negative phase surplus is not an action. This is a
   restriction; the executable also tests that allowing it does not change
   `N` for the two certified-target θ.
6. **Keep certified and estimated separate.** Only the argmin/argmax θ are Lean
   certification targets. The 128-combination table here is a search estimate.

---

## 4. Observed results (untrusted)

### 4.1 Baseline and cost-110 twin

Baseline θ* = `(80, growth_first, best, 2, zero, exact, exact)`:

```
N = 20
goal state = (pop=1, food=0, prog=190, trained=1)
reach layer sizes (t=0..20):
  1, 3, 5, 7, 9, 11, 13, 15, 24, 55, 109, 185,
  283, 403, 545, 709, 895, 1103, 1355, 1586, 1809
```

Canonical frozen witness (full 20 rows in the JSON): `G` ×7 with IDLE
(`F=400, P=300, d=200, e=220, q=315` discarded, `prog` stays 0), growth at
`t=7` (`1320+220=1540 ≥ 1500`, basket emptied); then `PH,P` ×13 with SETTLER
(`F=400, P=600, d=0, e=0, q=630` credited; food stays 0); at `t=20`,
`prog=7560+630=8190 ≥ 8000`, so post-state `(1,0,190,1)`.

The canonical witness is **idle-free** (`|work| = pop` at every step) and has
`prog=0` before the first pre-turn pop ≥ 2. The contract's §10-style witness
instead uses `GH` ×7 (q=420 discarded) and `GH,PH` ×13 (q=630, food 110/step),
ending at `(1,1430,190,1)`; it replays to the same `N=20`. Both are legal
choices; the food path is not unique.

Cost-110 twin (`settler_cost=11000`, all other axes fixed):

```
N = 25
goal state = (pop=1, food=0, prog=340, trained=1)
canonical witness: same G/IDLE prefix, then PH,P ×18 SETTLER
```

### 4.2 Finite action counts

| pop | full product | capacity-filtered box | structural legal | idle-free structural |
|---:|---:|---:|---:|---:|
| 1 | 160 | 50 | 5 | 4 |
| 2 | 160 | 110 | 50 | 24 |
| 3 | 160 | 150 | 62 | 12 |

### 4.3 Guards at H = 27 (all reachable / no-goal)

| θ | max pop | max food pop2 | max food pop3 | max prog | max layer (all / no-goal) | states visited (all / no-goal) | pop4? | T3 crossed? |
|---|---:|---:|---:|---:|---:|---:|---|---|
| baseline (cost 80) | 3 | 2310 | 990 | 7980 | 2991 / 2411 | 26435 / 24340 | no | no |
| cost 110 | 3 | 2310 | 990 | 10920 | 3487 / 3301 | 28740 / 28333 | no | no |

`allReachable` expands goal states to H; `noGoal` excludes `trained >= 1`
states. Housing left at max pop is `6-3=3 ≥ 2`, so G2's factor is 1.00. `T(3)`
is never crossed (`990 < 3383`), so C7 is inert here; pop 4 is never reached.

Cost × basket guard variants (max food at pop 3, H=27 all-reachable):

| variant | max food pop3 | max layer |
|---|---:|---:|
| cost80 zero | 990 | 2991 |
| cost80 subtract | 1050 | 3469 |
| cost110 zero | 990 | 3487 |
| cost110 subtract | 1050 | 3581 |

### 4.4 All 128 θ (search estimate)

* 128/128 reached the goal within H=27; no `none`.
* Distinct `N`: `{20, 25}` — 64 combinations each.
* Envelope: `[20, 25]` (search estimate, **not certified**).
* All six non-cost axes are strictly inert over the full box:
  `turnOrder`, `newCitizen`, `amenityStock`, `basketOnGrowth`,
  `productionRounding`, `thresholdRounding`.
* Per-axis marginal `N` sets:
  `settlerCost 80 -> {20}`, `110 -> {25}`; every other axis
  `-> {20,25}` for each value.
* 0 disagreements with the analyst `predictedN` table (128/128 compared only
  **after** the independent search).
* Prefix extrema up to the first goal layer, over all θ: max pop 3,
  max food pop2 2350, max food pop3 830, max layer 25495.
* Formula observed but not proved: `N(θ) = 7 + ceil(C/630)` for this box
  (20 or 25); the pop-3 branch remains unproved, as the contract says.

### 4.5 Resources and wall time

Measured on the project machine (AMD Ryzen 7 8700G, Python 3.13.12):

| run | wall time | notes |
|---|---:|---|
| `--self-test` (28 tests) | 23.7 s | all pass |
| default baseline+cost+guards | 30.3 s | no 128 run |
| `--guards` | 8.7 s | baseline + cost 110, H=27 |
| `--all` (128 θ) | 212.5 s | exact-step, H=27 |
| `--write-fixture` | 242.2 s | full report; max RSS 43,544 KB |

Largest observed per-layer count in the goal-prefix search: 25495 (all θ,
H=27); baseline all-reachable H=27: 2991. The contract's `2.1·10^4`
states/layer line is a contract-side figure; this executable reports its own
observed counts rather than assuming it.

---

## 5. Explicit discrepancies / limitations (no silent semantic repair)

The current v2.1 fixture differs from the earlier v2 draft in exactly the ways
the contract changelog records. The executable was updated to the current shape:
it reads `version: "2.1"`, `predictions.interval`, `scale.maxLayerObserved`,
and the total `extraGain`. It does **not** copy analyst `predictedN` values as
results.

| id | fixture value | executable observation | interpretation |
|---|---|---|---|
| `D-SCALE-maxLayerObserved` | `20972` | baseline H=27: `2991`; all-128 goal-prefix max layer `25495` | The fixture value is an analyst 128-combo/H=34 measurement, not a baseline H=27 measurement. Different experiment; no N effect. The executable does not tune to it. |
| `D-SCALE-maxFoodPop3` | `{cost80: {zero:100, subtract:170}, cost110: {zero:600, subtract:670}}` | `{cost80:{zero:990, subtract:1050}, cost110:{zero:990, subtract:1050}}` | Re-derived by H=27 all-reachable enumeration. The analyst block is explicitly labelled "per-combo measurements are O8-owned" and uncertified; O8 must own the maxima. No N effect. |
| `D-AMEN-P4` | `rules.R-AMEN-3.value.p4 = 2` | `max(0, floor((4-1)/2)) = 1` | The executable follows the normative §4 formula. Pop 4 is unreachable under G1, so this parameter-table inconsistency cannot change any reported N or guard. Recorded, not silently repaired. |

Additional limitations:

* **L-HORIZON.** Task execution cap `H=27`; current contract/fixture uses
  `H=34` and `O6b horizonOk`. All θ minima here are ≤25, so minimality is
  unaffected; the H=34 sensitivity envelope (palace +0/+1/+3, A2 tiles-only)
  is outside this run and is not claimed.
* **L-ALLACTIONS.** O2's `legal ↔ a ∈ allActions` and O2b's
  `legal := step.isSome` are both present in the contract. The executable
  reports raw box / structural / viable counts; a Lean porter must pick one
  encoding. Starving structural tuples are the difference.
* **L-EXTRA.** `prod(extra)` is totalized to 0 for `none`; the contract's old
  "extra exists by legality" justification is not used.
* **Tier table.** Ecstatic and below-Displeased multipliers are not in the
  contract's table. `tier` raises for them rather than inventing values; with
  `amenityStock ∈ {1,2}` and reachable `pop ≤ 3` they do not occur.
* **No-carry / queue carry.** The executable implements the contract's no-carry
  restriction; the `≤ q` carry variant (19/24 in the contract's note) is not
  searched or claimed.
* **Starvation** is a restriction, not a relaxation. The executable's test
  suite shows that allowing `d < 0` does not change N for the baseline and
  cost-110 θ, but this is an observed invariant, not a proof for all σ.
* **No real-game claim.** All numbers are conditional on the model, σ and
  A1–A8. No Civ6 build is pinned; no fixture was run in the game.

For comparison, the older v2 draft's `q = 525` at pop 1 `GH` was stale: with
`F=400, P=400, prodMult=105`, `q=420`. The current v2.1 fixture already records
420; the executable computes 420. The canonical witness uses `G` (q=315
discarded) instead, which is legal and has the same `e=220`; the `GH`-style
replay is included as `contractStyleWitness` and ends at `(1,1430,190,1)`.

---

## 6. Tests run

`python3 search/mvp.py --self-test` → **28 tests, OK** (23.7 s). Coverage:

1. Fixture version/shape/axis product, θ validation, state validation.
2. `actionBox` is the literal powerset product; capacity 1; no duplicate tile;
   extra not in work; IDLE has no extra.
3. Pre-turn SETTLER legality and the selection-timing test: a pop-1 growth step
   cannot legalise SETTLER.
4. IDLE credits nothing (all reachable IDLE actions); a legacy banking variant
   is detectably faster and is not the model.
5. Ghost extra: no growth ⇒ extra is inert; growth + `newCitizen=best` ⇒ extra
   production only then; `newCitizen=none` and `production_first` make it inert;
   extra never contributes food.
6. Nonnegative surplus legality; starvation relaxation is N-inert on both
   target θ.
7. Goal terminality/no-goal-before-N; exact-step layers and parent replay.
8. Baseline `N=20`, cost-110 `N=25`; idle-free witness replay for both.
9. Contract-style `GH`/`GH,PH` witness replay to `(1,1430,190,1)`.
10. Guards: max pop 3, max food pop2 2310, max food pop3 990, no pop 4, T3 not
    crossed, housing left ≥2.
11. Exactness/integer-only checks (`q_raw % 100 = 0`,
    `d*growthMult % 100 = 0`), determinism, and a tier-indexing regression.
12. Analyst prediction compared only after the independent result.

`python3 search/mvp.py --check-fixture` replays the frozen fixture's baseline
and cost-110 witnesses and compares `N`; it returns
`{ok:true, baselineN:20, cost110N:25}`.

---

## 7. Fixture machine schema (`fixtures/mvp-baseline.json`)

Top level (compact, simple, no nested proof objects):

```json
{
  "fixtureId": "mvp-baseline-v1",
  "version": 1,
  "kind": "mvp-executable-baseline",
  "untrusted": true,
  "gameFactClaim": false,
  "contractPath": "mvp/RULE-CONTRACT.md",
  "ruleFixturePath": "fixtures/mvp-rule-candidates.json",
  "ruleFixtureVersion": "2.1",
  "semantics": { "...": "step semantics summary" },
  "scenario": { "id": "...", "tileIds": ["G","GH","PH","P"],
                "thresholds": {"1":1500,"2":2400,"3Floor":3300,"3Exact":3383,"4":4420},
                "initialState": [1,0,0,0], "goal": "trained >= 1" },
  "thetaAxes": ["settlerCost","turnOrder","newCitizen","amenityStock",
                "basketOnGrowth","productionRounding","thresholdRounding"],
  "actionCounts": { "1": {"fullProduct":160,"box":50,"structuralLegal":5,"idleFreeStructural":4}, "...": {} },
  "horizon": 27,
  "contractHorizon": 34,
  "baseline": { "theta": {}, "n": 20, "goalState": [1,0,190,1],
                "layerSizes": [], "stats": {}, "witness": [], "witnessChecks": {} },
  "cost110": { "...": "same shape" },
  "contractStyleWitness": { "n": 20, "finalState": [1,1430,190,1], "...": {} },
  "guards": { "baseline": {"allReachable":{},"noGoal":{}}, "cost110": {}, "variants": {} },
  "execution": { "totalSeconds": 242.2, "maxRssKb": 43544, "all128Seconds": 212.5 },
  "all128": { "count": 128, "envelope": {"min":20,"max":25,"distinctValues":[20,25]},
              "perAxisMarginal": {}, "inertAxes": [], "argminThetas": [], "argmaxThetas": [],
              "unreached": [], "prefixExtrema": {}, "predictionComparison": {},
              "results": [ {"theta": [80,"growth_first","best",2,"zero","exact","exact"],
                            "n":20,"goalState":[],"maxPop":3,"maxFoodPop2":2310,
                            "maxFoodPop3":220,"maxLayerSize":1809} ] },
  "discrepancies": [],
  "limitations": []
}
```

Witness row schema (one object per step; `pre`/`post` are
`[pop,food,prog,trained]`):

```json
{ "t": 20,
  "pre": [2,0,7560,0],
  "action": {"work": ["PH","P"], "workMask": 12, "extra": null, "build": "SETTLER"},
  "F": 400, "P": 600, "d": 0, "e": 0, "grew": false,
  "q": 630, "credited": 630, "completed": true, "extraProd": 0,
  "post": [1,0,190,1] }
```

The machine-readable `all128.results` uses compact rows:
`theta = [costAxis, turnOrder, newCitizen, amenityStock, basketOnGrowth,
productionRounding, thresholdRounding]`, followed by `n`, `goalState`,
`maxPop`, `maxFoodPop2`, `maxFoodPop3`, `maxLayerSize`. Per-θ layer lists are
deliberately omitted to keep the fixture small; the baseline/cost-110 witnesses
and guard reports retain their full layers.

---

## 8. Reproduction

```bash
python3 search/mvp.py                  # baseline + cost-110 + guards report
python3 search/mvp.py --self-test      # 28 tests
python3 search/mvp.py --guards         # H=27 guard enumeration
python3 search/mvp.py --all            # all 128 θ (about 3.5 min)
python3 search/mvp.py --check-fixture  # replay frozen baseline/cost-110 witnesses
python3 search/mvp.py --write-fixture  # regenerate fixtures/mvp-baseline.json (about 4 min)
```

No git push, no contract edits, and no changes to `search/synthetic.py` or
`fixtures/synthetic-v0.json` are part of this work.

---

## 9. What is not claimed

* Not a Civ6 fact: no build hash, no in-game fixture, no `[V]` claim; `80 vs
  110`, palace `+2 P`, Happy tiers, `T(1)=15`, `PrereqPopulation=2` remain
  `[C]/[D*]/[A]`.
* Not a Lean proof: `OptimalAt`/`N` here are untrusted search results. Only the
  argmin/argmax θ are certification targets in the contract.
* Not the H=34 envelope: this run is capped at H=27; outside-box A1/A2
  sensitivities are not searched.
* Not a real-game lower bound: the model uses the §8 restrictions (no carry,
  starvation illegal) and excludes X1–X17, X20; only the explicitly named
  relaxing choices could carry a real-game lower bound, and they are not
  claimed here.
