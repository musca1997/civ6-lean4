# RULE-CONTRACT.md — MVP v2.1: BASE Civ6, one city, first trained Settler (CONDITIONAL)

Owner: MVP rule-selection task. Machine-readable twin: `fixtures/mvp-rule-candidates.json` (`version: 2.1`).
Evidence corpus (not contract): `RULES.md`, `research/RULES-RESEARCH.md`. Adversarial check: `mvp/SEMANTIC-REVIEW.md`.

> **Claim discipline.** Every `N` below lives inside `M_MVP(θ, σ)`. **Certified** (the only Lean theorems required):
> `OptimalAt(θ, σ, N(θ))` for argmin and argmax θ. **Search estimate** (untrusted Python): the other 126 θ and hence
> the interval. The reported interval `[20, 25]` is *conditional on the baseline assumptions* A1/A2/A8 and on the
> no-carry restriction (§8.1); it is **not** widened to cover variants outside Θ (§12). **Not** a Civ6 fact:
> `[V] = 0`, no build pinned, no fixture run.

Tags: `[D*]` community game-data export, build unknown · `[A]` 2K manual/Civilopedia · `[C]` community prose ·
`[I]` derived · `[U]` unresolved · `[ASSUME]` model choice · `[SCENARIO]` σ data, not a rule claim.

## 0. Baseline interface (frozen — implementers must not fork this)

```
M_MVP(θ, σ) := (State, Action, step : State → Action → Option State, legal s a := (step s a).isSome,
                Goal s := trained s ≥ 1, allActions s : Finset Action)
BASELINE θ* := {settlerCost 80, turnOrder growth_first, newCitizen best, amenityStock 2,
                basketOnGrowth zero, productionRounding exact, thresholdRounding exact}
BASELINE σ  := sigma-capital-4tiles-v1 (§2)   scale 1/100   H = 34   horizonOk: N(θ) ≤ H for every θ
Frozen: pre-turn selection (A8) · extra = ⊥ under IDLE · extraGain(⊥) = 0 · no progress before pop 2 or on IDLE
  (R-SET-9) · starvation illegal · housing ×1.00 (G2) · pop ≤ 3 (G1)
Deliver: step / legal / allActions → reach layers → witness for θ* → OptimalAt for θ* and the cost-110 twin →
  per-θ table for all 128 θ **labelled estimate** (mixing certified with estimated numbers = defect).
```

## 1. Version pin and settings (σ metadata)

| field | value | tag | note |
|---|---|---|---|
| ruleset · speed | Base (vanilla), no R&F / no GS · Standard (`CostMultiplier=100`) | `[U]`/`[D*]` | R-VER-1; `Module:Data/Civ6/Base/GameSpeeds` |
| difficulty / civ / leader | Prince, generic, no ability or human-side modifier modelled | `[U]` | A5, FX-DIFF, R-VER-5 |
| DLC / mods / modes / era · build id + XML hashes | none, Ancient · **not pinned** | `[U]` | R-VER-8, blocker K0 / FX-VER |

Time unit = **settlement step**, not UI turn; `t=0` is the founding snapshot before any settlement (founding turn out
of scope, FX-FOUND). Minimality needs layers `0..N`; `H = 34` is a horizon bound, not a claim.

## 2. Scenario σ (`sigma-capital-4tiles-v1`)

Scale: integers in **1/100** (sufficiency argument in G6).

| element | value | tag |
|---|---|---|
| city centre (free, never assignable) | 2.00 F / 1.00 P | `[D*]` `YIELD_*_CITY_TERRAIN_REPLACE` |
| palace | +2.00 P, +1 housing, +1 amenity | `[C]` P (A1), `[D*]` housing/amenity |
| fresh water | yes ⇒ housing `5+1 = 6`; growth ×1.00 while `housing−pop ≥ 2` (tiers 1⇒×0.50, 0..−4⇒×0.25, ≤−5⇒×0) | `[D*]` `CITY_POPULATION_RIVER_LAKE=5` |
| tiles (fixed, no border growth) · capacity | `G` 2F/0P · `GH` 2F/1P · `PH` 1F/2P · `P` 1F/1P · 1 citizen/tile, no duplicates, centre excluded | `[SCENARIO]`/`[D*]+[A]` |
| initial state · goal | `t=0, pop=1, food=0, prog=0, trained=0` · `Goal s := trained s ≥ 1` (`[A]`, monotone counter) | `[C]` pop, `[ASSUME]` food |

Why these numbers: (a) `G/GH/PH` is the non-dominated base-terrain food/production frontier, `P` adds a realistic tile
giving a zero-surplus max-production pair at pop 2; (b) fresh water keeps housing inert (G2); (c) `T(1)=15`, `T(2)=24`
are **exactly integral**, so the mandatory growth is rounding-free; (d) the pop-1 start makes the food allocation
structurally load-bearing: `PrereqPopulation=2` forces one growth event and **nothing is credited before pop 2** (§4).
Preconditions (violation voids the contract): fresh-water capital; flat centre; no resource/feature/river/wonder/tribal
village on or beside the 4 tiles.

## 3. State, action, legality

```
S = (pop, food, prog, trained)                 -- pop ∈ {1..3} (G1); prog = settler-specific progress
A = (work, extra, build)                       -- work ⊆ tiles, extra : Option Tile, build : {SETTLER, IDLE}
legal s a := (step s a).isSome                 -- single source of truth (O2b); it is some iff:
   |a.work| ≤ s.pop · (a.extra = ⊥ ∨ a.extra ∉ a.work) · (build = SETTLER ⇒ s.pop(pre-turn) ≥ 2)
   · (build = IDLE ⇒ a.extra = ⊥) · (post-modifier surplus ≥ 0, evaluated inside §4 per branch)
```

`extra` is the tile the *new* citizen would work: a real unworked tile of σ, used **only** on an actual growth event —
otherwise it yields nothing (no ghost output). `allActions s` comes from `Finset.powerset` (work × extra × build),
never hand-listed: ≤ 62 actions/state (pop 3), ≤ 2.1·10⁴ states/layer.

## 4. Normative step (the single definition of `M_MVP`)

```
F = 200 + Σ_{work} food        P = 300 + Σ_{work} prod         -- extra NEVER feeds F
tier(p) = f(θ.amenityStock − req(p)), req(p) = max(0, ⌊(p−1)/2⌋)
growthMult: happy 110 | content 100 | displeased 85    prodMult: happy 105 | content 100 | displeased 95
grow(b, p) = (p+1, basket(b − T(p))) if b ≥ T(p) else (p, b)     -- one growth per step (G3)
T(1)=1500  T(2)=2400  T(3)= 3300 (θ.thresholdRounding=floor) | 3383 (exact)   [T(4)=4420 defined, never reached: G1]
round10(x) = x (θ.productionRounding=exact) | ⌊x/10⌋·10 (trunc10)   basket(v) = 0 (zero) | v (subtract)
extraGain(a.extra) = 0 if a.extra = ⊥ else prod(a.extra)          -- TOTAL in both branches (B1)
CREDIT(q) = q if build = SETTLER else 0                           -- R-SET-9: IDLE credits nothing

growth_first:    d = F − 200·pop ; require d ≥ 0 ; e = d·growthMult(tier(pop))/100
                 (pop1, food1) = grow(food + e, pop)
                 if pop1 > pop ∧ θ.newCitizen = best then P += extraGain(a.extra)   -- 0 when ⊥/IDLE
                 q = round10(P·prodMult(tier(pop1))/100) ; prog1 = prog + CREDIT(q)
                 if build = SETTLER ∧ prog1 ≥ cost → (pop1−1, food1, prog1−cost, trained+1)
                 else (pop1, food1, prog1, trained)
production_first: q = round10(P·prodMult(tier(pop))/100) ; prog1 = prog + CREDIT(q)
                 done = (build = SETTLER ∧ prog1 ≥ cost) ; pop1 = pop − done ; prog1 = prog1 − cost·done
                 d = F − 200·pop1 ; require d ≥ 0 ; e = d·growthMult(tier(pop1))/100
                 (pop2, food2) = grow(food + e, pop1) ; (pop2, food2, prog1, trained+done)
```

Growth is automatic when the basket fills; the only way to avoid it is to work lower-food tiles. **Selection timing**:
`build` is chosen against the pre-turn state, so a settler cannot be selected at pop 1 and cannot be retro-legalised by
a same-step growth (A8). **No progress is credited before pop 2 and none on idle steps**; per-item overflow
(`prog1 − cost`) is carried but is post-goal here. `build` is weakly dominated at pop ≥ 2 (progress can only help), so
an implementation may drop it after proving the dominance (B8); the contract keeps it for completeness.

## 5. Constants: verified public data vs assumptions

Public data (`[D*]`/`[A]`; per-rule sources in JSON `rules`): food per citizen 2 · centre 2F/1P, free · palace +1
housing, +1 amenity (+2 P is A1) · 1 citizen per tile · threshold `15+8(n−1)+(n−1)^1.5` with the **surplus** (not the
threshold) multiplied · `req(p)=max(0,⌊(p−1)/2⌋)`, tier from `stock−req`: `1–2` Happy (`+10% growth / +5% non-food`),
`0` Content · settler `PrereqPopulation=2`, cost per C1, `PopulationCost=1`, no tech · progress is per item (R-SET-9).
**Assumptions are load-bearing, each falsifiable:**

| id | assumption | tag | falsifier | impact if false |
|---|---|---|---|---|
| A1 | palace gives **+2 production** (its XML has only housing/amenity) | `[C]` | FX-CAL | every N changes → v3 (§10 sensitivities) |
| A2 | Happy `+5%` multiplies the **whole** city production | `[I]` | FX-CAL | cost-80 N: 20 → 21 at tiles-only scope |
| A3 | `T(1)=15`, `T(2)=24` are the exact in-game requirement | `[C]+[D*]` | FX-TH | ≤ +1 step |
| A4 | basket starts at 0; founding settlement out of scope | `[ASSUME]` | FX-FOUND | shifts t by 1 |
| A5 | no difficulty/civ modifier on the modelled quantities | `[U]` | FX-DIFF | capability exclusion |
| A6 | the 4 tiles carry no resource/feature/bonus | `[SCENARIO]` | map check | different σ |
| A7 | the city keeps growing while a settler is built (no Civ5 freeze) | `[C-weak]` | FX-SG | **structural** rewrite |
| A8 | build target fixed at the step's start; a same-step growth never retro-legalises SETTLER | `[ASSUME]` | FX-ORD-a | N only smaller (outside Θ, §12) |

## 6. Candidate box Θ_MVP (finite, named, 2⁷ = 128; unchanged in v2.1)

| axis | values | why unresolved | falsifier | predicted effect |
|---|---|---|---|---|
| C1 `settlerCost` | 80 \| 110 | wiki formula counts the free starting settler (⇒110); two first-hand reports say 80 | FX-SET-BASE | **5 steps** |
| C2 `turnOrder` | growth_first \| production_first | no authoritative intra-turn source exists | FX-ORD-a/b | none predicted |
| C3 `newCitizen` | best \| none | new citizen's same-turn output asserted then retracted | FX-ORD-c | none predicted |
| C4 `amenityStock` | 2 \| 1 | release-era text says 1; current Base export is free 1 + palace 1; patch notes moved it | FX-AM3 | none predicted |
| C5 `basketOnGrowth` | zero \| subtract | manual says "emptied"; harvest anecdotes say overflow kept | FX-BASKET | none predicted |
| C6 `productionRounding` | exact \| trunc10 | `9→9.4` seen on a MOD map; `9×1.05=9.45` sits on the boundary | FX-PROD-FRAC | none predicted |
| C7 `thresholdRounding` | 3300 (floor) \| 3383 (exact) | `T(3)=33.8284` is non-integral | FX-TH | **none — inert by G1 proof** |

All 128 combinations must be searched; predicted `N` per combination is in JSON `predictions.nByCombo` and must be
**reproduced or reported as a discrepancy** (O10). Per-θ results are estimates, not certificates (O7).

## 7. Guards (each must be re-derived, not trusted)

- **G1 threshold & population ceiling** (labels corrected): the model *defines* `T(3)`/`T(4)`; the claim is that neither
  is reached. Earliest pop 2 = `t=7` (`⌈1500/220⌉`), earliest pop 3 = `t ≥ 7 + ⌈2400/220⌉ = 18`; at pop 3 max surplus
  is `100` (`F ≤ 700`, consumption `600`) ⇒ `e ≤ 110`/step, so at `t ≤ H=34` pop-3 food `≤ 110·(34−18) + 219 = 1979 <
  3300`. So `T(3)` is never crossed ⇒ **C7 inert by proof** (in Θ, not "active"), pop 4 (`t ≥ 48`) unreachable.
- **G2 housing inert**: `6 − pop ≥ 3 ≥ 2` for `pop ≤ 3` (and `= 2` for pop 4) ⇒ growth factor 1.00.
- **G3 one growth per step**: max surplus `220` < `T(1)=1500`. **G4 ceiling `pop ≤ 3`**: as G1, via O8. **G5 idle**:
  `|work| < pop` enlarges the action set (safe for bounds) and IDLE only forfeits progress ⇒ witness must be idle-free.
- **G6 scale (premises added)**: multipliers act once per step on that step's yield, never on accumulated state. Given
  G2 and tier ∈ {Happy, Content} for `A ∈ {1,2}` (`req(p) ≤ 1` for `p ≤ 3`): `d ∈ {0,100,200}` ⇒ `e ∈ {0,110,220}`;
  `P ∈ {300,…,700}` (`Σprod ≤ 400`) ⇒ `P·21/20 ∈ {315,…,735}`; all integers in 1/100, closed under addition. A
  Displeased tier with a 0.50 housing factor (`e = 42.5`) would break the grid — excluded by G2/G3 and `A ∈ {1,2}`.

## 8. Restrictions and exclusions (repeat in every certificate header)

1. **Starvation is illegal** — a *restriction* class: it removes actions, so it can only raise `N` and cannot carry a
   real-game lower bound. Inert here only because every cut action is dominated (at pop 1–3 the max-production
   assignment is food-neutral or better: `PH` d=100, `PH+P` d=0, `GH+PH+P` d=0; pop 4 has no legal action) — O8.
   **No overflow carry across an idle step** is a second restriction of the same class (§12): `≤ q` carry ⇒ 19/24.
2. **Idle** stands for "building something else"; its legitimacy **depends on X4–X7**, which remove real side effects.
3. Capability exclusions (real play could be *faster*, so the bound does not transfer): X1 purchase, X3 chop,
   **X5 `Urban Planning` +1 P / `Colonization` +50 % settler P**, X6 civics, X7 builders, X8 pantheon (Religious
   Settlements gifts a settler), X9 villages, X10 border growth (tiles frozen), X11 movement / second city (goal is
   "trained", not "settled"), X12 trade, X13 city-states, X14 great people, X15 wonders, X16 modes, X17 abilities, X20 era.
4. Relaxation exclusion (safe): X18 barbarians/enemies/disasters/pillaging.

## 9. Obligations for the implementation agent

- **O1** `reach 0 = {s0}`, `reach (t+1) = ⋃_{s∈reach t} ⋃_{a∈allActions s} step s a`, dedup inside a layer only.
- **O2** completeness `legal s a ↔ a ∈ allActions s`, generated from `powerset`; **O2b** `legal := step.isSome` and
  `step_total : legal c s a → ∃ s', step c s a = some s'`; **O3** `reach` sound + complete against `ReachableAt`;
  **O4** `no_goal_before : ∀ t < N, ∀ s ∈ reach t, trained s = 0`.
- **O5** witness playout of length `N`, every step legal, `trained ≥ 1`, **idle-free**, with `prog = 0` until the first
  step whose pre-turn pop is ≥ 2.
- **O6** `OptimalAt θ N` per certified θ; **O6b** `horizonOk : ∀ θ ∈ Θ, N(θ) ≤ H = 34`; `#print axioms` clean (no
  `sorryAx`; `native_decide` only with the `RULES.md §10.5` disclosure).
- **O7** **certified: argmin and argmax θ only** (one cost-80, one cost-110). Every other θ and any interval statement
  is a *search estimate*; an interval proof needs all 128 θ or an inertness lemma for C2–C7.
- **O8** re-derive G1/G4 **and both §8.1 restriction-inertness claims** by enumeration per certified θ; own every
  measured maximum (max pop, max pop-3 food, layer sizes) — the contract states only analytic ceilings.
- **O9** report per-axis marginal `N` sets, name every inert axis, keep certified and estimated numbers apart.
- **O10** any disagreement with §10 stops the work and is reported; no silent contract edits.

## 10. Predictions (analyst-side, recomputed under v2.1; unverified)

Baseline θ* (§0) → **N = 20**: witness `GH` ×7 IDLE (`prog` stays 0), growth at t=7 (`1540 ≥ 1500`), `GH,PH` ×13 SETTLER.

| t | pre-pop | work | build | F | P | e | q | food | prog |
|---|---|---|---|---|---|---|---|---|---|
| 1–7 | 1 | `GH` | IDLE | 400 | 400 | 220 | 420 (not credited) | 220→1540 ⇒ pop 2 at t=7, basket → 0 | 0 |
| 8–19 | 2 | `GH`,`PH` | SETTLER | 500 | 600 | 110 | 630 | 110→1320 | 630→7560 |
| 20 | 2 | `GH`,`PH` | SETTLER | 500 | 600 | 110 | 630 | 1430 | 8190 ≥ 8000 ⇒ **goal**, pop→1, overflow 190 |

Cost 110: same prefix, `GH,PH` ×18 → `N = 25` (`10710` at t=24, `11340` at t=25). **Observed closed form over all 128
θ: `N(θ) = 7 + ⌈cost/630⌉`** (20, 25). Intended proof — *not* asserted; O8 owns the numbers: (i) `prog = 0` for
`t ≤ 7` (SETTLER illegal below pop 2; pop 2 needs `⌈1500/220⌉ = 7` steps); (ii) at pop 2 `q ≤ 630`, so
`N ≥ 7 + ⌈cost/630⌉`; (iii) the **pop-3 branch is unproved** — reaching pop 3 costs `≥ 11` steps at pop 2 where food
and production compete for the same two citizens (`G+GH`: food 220, `q = 420`; `GH+PH`: food 110, `q = 630`), so a
closed form needs an LP/dominance lemma over the 2-citizen assignments showing every pop-3 line completes no earlier
(the "22/26" figure in `SEMANTIC-REVIEW.md` is consistent, not evidence, and must not be quoted as proof).
Interval (**search estimate**, conditional on A1/A2/A8): `{20, 25}`; `settlerCost` is the only non-inert axis.
Outside-Θ sensitivities (**not** interval width, all within `H = 34`): palace `+1 P` ⇒ 23/28, `+0` ⇒ 27/33, `+3` ⇒
18/22 (re-run); A2 tile-yields-only (`q = 615`) ⇒ 21/25 (closed form, not enumerated). **Invalidated:** v1's `15 / 16 / 20`, its witness and its `handBoundWarning`
(its `6930` was v1's *banked* progress, which no v2 line holds) — no v1 number is reusable.

## 11. Falsifiers and refutation protocol

Every axis carries its own falsifier in §6; after the build pin (K0) the decisive, cheapest one is `FX-SET-BASE`
(80/110). Refutations follow `RULES.md §12.4`: record, mark `[V-refuted]`, invalidate dependents, bump the version.

## 12. Unresolved design choices (named; all outside Θ, none widens the interval)

- **A8 false** (build chosen after the growth phase): measured 19/24 — excluded from Θ by name; adopting it is a new
  contract version, not a wider interval.
- **Idle/queue carry** (an unmodelled build's overflow reaching the settler, `≤ q`): measured 19/24 — excluded by the
  no-carry restriction (§8.1, which follows R-PROD-3, but still a restriction: it can only raise `N`).
- **Progress at pop < 2** uncredited · **`T(3)`** only the two C7 readings · **turn↔step offset** (FX-FOUND) unclaimed.

## 13. Changelog

| version | change |
|---|---|
| v1 | first contract; credited settler progress during IDLE and pop-1 steps (**invalid**) |
| v2 | R-SET-9 `CREDIT`, pre-turn selection (A8), `extra` rules, C7 added, 128 combinations, interval relabelled estimate |
| v2.1 | totalised `extraGain` (⊥ ⇒ 0) and witness `q` 525→420 (B1); `handBoundWarning` replaced by the closed form plus an explicitly unproved pop-3 branch (B2); measured food maxima replaced by analytic ceilings, C7 relabelled inert-by-proof (B4); `H` 27→34 + `horizonOk` + A1/A2 sensitivities (B5); starvation classified as a restriction with an inertness obligation and no-carry named (B6); G6 premises added, `P ≤ 700` (B7); `legal := step.isSome` + `step_total` (B9); §0 baseline interface frozen |

## 14. Non-claims

Not a Civ6 fact (`[V]=0`); not the real-game earliest settler; every `N` is model-internal and conditional on A1–A8;
the bound holds only for the restricted action set (X1–X17, X19, X20) and the §8.1 restrictions; `IDLE` legitimacy
depends on X4–X7; nothing about a second settler, second city or other map. Allowed sentence: "In model `M_MVP(θ, σ)`
with θ = …, the first trained Settler completes at step `N = …` (certified); the search-estimated interval over `Θ_MVP`
(128 combinations, 8 assumptions) is `[20, 25]`."
