# SEMANTIC-REVIEW.md — adversarial review of `mvp/RULE-CONTRACT.md` (v2) + `fixtures/mvp-rule-candidates.json`

Scope: this file only; no edits to contract/fixture/Lean, no git, no fixtures run, no `[V]` claim.
Method: independent re-implementation of §4 from the text, powerset enumeration of Θ. **v1 reproduced 64/64**
(all `nByCombo`, marginals, `[15,20]`, baseline 15), which localised v1's defect to semantics, not arithmetic.
Contract v2 + fixture v2 landed while this review ran; **v2 now reproduces exactly too: my independent run matches
all 128 `nByCombo` values, the `{20,25}` envelope, both certified targets and both witnesses' crossings**
(`t=20`, `t=25`, food 1430/1980 < `T(2)`). So the remaining list is short, and four figures do not match my run.
Units: 1/100 integers, same σ/Θ, `H=27` unless marked.

## 0. Verdict

- **The v1→v2 fix is correct and verified.** R-SET-9 + `CREDIT(q)` + A8 remove the banking; `N = 20 / 25` is right
  for every C1–C6 combination (C7 cannot fire, B4), and the pop-1 phase is now honestly a food rush.
- **Four figures do not reproduce:** `q=525` on the witness's `GH` rows (it is 420); "max pop-3 food = 720" (900–1050
  depending on θ); and §10's `handBoundWarning`, which still reuses v1's banked `6930` and its "24" — no v2 path is
  worth 6930 at `t≥18` (measured best pop-3 completion: 22/26). `maxLayerAtH27=21366` and `maxFoodPop2=2350` **do**
  reproduce (my superset run: 21417 and 2350).
- **One partial function is now reachable in the canonical witness:** §3 forces `extra=⊥` under `IDLE`, and the
  witness's growth step (t=7) is `IDLE + newCitizen=best`, so `P += prod(extra)` is applied to `⊥` there.
- **Width:** A8-false and the §12.2 "kept in some city pool" variant each give 19/24, so the honest reportable
  interval is `[19,25]` unless both are excluded by name. A1/A2 sensitivities break `H=27`.

## 1. Blockers

**B1 — `prod(extra)` is partial at the witness's own growth step.** §3: `(build = IDLE ⇒ extra = ⊥)`; §4:
`if pop1 > pop ∧ newCitizen = best then P += prod(extra)` with the comment "extra exists by legality". At t=7 the
witness is IDLE, `newCitizen=best`, growth fires, `extra=⊥` ⇒ the step function is undefined exactly where §10's
trace runs (v1's witness happened to pass a concrete `extra=PH`, so the hole was invisible; v2 makes `extra=⊥`
*mandatory* under IDLE, so the same formula now hits it). Fix — total, no prose:
`extraGain := match a.extra with | none => 0 | some t => prod t`, applied only when growth fires. Consequence in the
same table: `work = GH` at pop 1 gives `P = 300+100 = 400 ⇒ q = 420`, not `525` (525 is `PH`'s q; `e=220` needs
`GH`, `q=525` needs `PH` — the row mixes the two). q is uncredited on those rows so `N` is unaffected, but a
hand-edited trace in a document whose §4 is "the single definition" is a reproducibility defect: regenerate the
table from the model (S7) and let O8 own the numbers.

**B2 — §10's `handBoundWarning` is the last v1 residue, and its conclusion is false.** It claims the split gives
"`18 + ⌈(cost−6930)/735⌉ = 24` for cost 110, where the enumeration says 25", inferring that a coupling is missing.
`6930` is v1's *banked* progress at t=18; under v2 `prog = 0` until t=8, so no path has it. Measured under v2: the
best completion with pop 3 at the completing step is **22 (cost 80) / 26 (cost 110)** — both worse than 20/25 — and
`N = 7 + ⌈cost/630⌉` is **exact** for both costs over all 64 C1–C6 combinations. So replace the paragraph with:
(i) the closed form as a theorem about this σ; (ii) the dominance bound "every pop-3 line is ≥ 22, hence dominated".
Delete "coincidence": 20 is the optimum, not a numerical accident. This matters beyond cosmetics — O7/O9 lean on
"the enumeration is necessary because a hand bound disagrees", and that premise is the v1 artefact.

## 2. High

**B3 — reportable width `[19,25]`, not `[20,25]`.** Two documented alternatives each move both endpoints by one
step and both sit outside Θ:
(a) A8 false (build chosen after the growth phase): measured **19 / 24**; §12.1's "N can only get smaller" is right,
but the published interval keeps the upper endpoint as if it could not move.
(b) §12.2's "kept in some city pool": real Civ6 carries at most one item's overflow into the next build
(`≤ q = 525`), so `⌈(8000−525)/630⌉ = 12` ⇒ **19/24** as well. Note this follows from the contract's own R-PROD-3
("overflow into the next item"): "no banking at all" is a **restriction** (it can only raise N), not a faithful
reading — so §4's "there is therefore no production banking" overstates what is established.
Either promote `queueTiming`/`idleCarry` to axes, or widen §0/§13 to **`[19,25]`** and name the two excluded
variants. A one-step-wide claim resting on two unlisted choices is the v1 failure mode in miniature.

**B4 — O8's pop-3 figure; and C7 can be retired by proof instead of doubling Θ.** §7 G1 reports "max pop-3
food = 720". My enumeration over Θ (`H=27`) gives max pop 3, **max pop-2 food 2310 (zero) / 2350 (subtract)**, and
**max pop-3 food 900 (amenityStock=1) / 990 (zero) / 1050 (subtract)** — 720 matches no (θ, basket) pair I can
generate; either re-derive it or state the quantity (e.g. "at the moment of reaching pop 3"). The conclusion is
untouched: `T(3) ≥ 3300` is never crossed, with a margin ≥ 2250, so C7 is **provably** inert and can be retired by
an enumeration lemma — which also resolves the internal tension in G1 calling C7 "an active axis" while its own
ceiling argument proves it cannot fire. (Keeping C7 is harmless; calling it active is not.)

**B5 — `H=27` still fails for plausible A1/A2 readings.** Palace `+0/+1/+3` ⇒ **27/33, 23/28, 18/22**: at cost 110
the goal is *not* reached within `H` for `+0` (33) and `+1` (28). A2 tiles-only (`q=615` instead of 630) ⇒ **21/25**:
`13×615 = 7995 < 8000` misses by 5/100, so a `[I]`-grade scope choice costs a step at cost 80 while §5's impact
column ("−0.15…−0.30 P/step") hides it. Either `H ≥ 34` plus an explicit `HorizonOk : ∀ θ ∈ Θ, ∃ n ≤ H, OptimalAt θ n`,
or publish the A1/A2 rows as sensitivities in §10 (they are cheap and they strengthen the "conditional" framing).

## 3. Medium

**B6 — starvation is in the wrong exclusion class.** §8.1 calls it "a model restriction, not evidence" (right) but
files it outside both taxonomy classes, and §8.4 keeps "relaxation-safe" for X18 only. The direction matters: the
restriction *removes* actions, so it can only raise `N` and **cannot** carry a real-game lower bound. It is inert
here for a recordable reason: at `pop 1..4` the max-production assignment is food-neutral or better (`PH`: `d=100`;
`PH+P`: `d=0`; `GH+PH+P`: `F=600, d=0, q=735`), so only dominated actions are cut. Make "restriction inertness for
every θ" an obligation (my enumeration confirms `N` unchanged with `d<0` allowed).

**B7 — G6's `e ∈ {0,110,220}` enumeration is missing its premises.** It presumes `tier ∈ {happy, content}` *and*
housing factor 1.0. Cite G2 plus "`A=1` at pop 3 ⇒ Content" (C4's other value); say what would break it: Displeased
with housing `1/2` gives `0.85×0.5 = 17/40`, i.e. `e = 42.5` at `d=100` — non-integral, and §4 defines no rounding.
Also `P ≤ 700` (`Σprod ≤ 400`), not 800; the conclusion is unaffected.

**B8 — `build` can be deleted from the action space.** With R-SET-9, `SETTLER` weakly dominates `IDLE` whenever
`pop ≥ 2` (progress can only help; completion never hurts). Proving that dominance halves the action count
62 → ~31, removes the `IDLE ⇒ extra = ⊥` clause and with it B1, and leaves A8 as the only timing question.

**B9 — `legal` is still circular.** §3 defines `legal` through "surplus computed inside §4" and then asserts
`legal ⇔ step ≠ none`; surplus is branch-dependent (`production_first` evaluates `d` at `pop−1`). State
`legal := (step …).isSome` and prove `step_total : legal c s a → ∃ s', step c s a = some s'`; O2 then has content.
The "otherwise it yields nothing (no ghost output)" note is correct and worth keeping.

## 4. Verified (credit where due)

R-SET-9/`CREDIT`, `prog` on build switch, per-item progress, **62 actions/state** (I get exactly 62 at pop 3), O5's
`prog = 0`-before-pop-2 clause, O7's certified-vs-estimated split, §12's unresolved list, G5's citizen-idle
relaxation with an idle-free witness, G4's pop ceiling, `T(1)/T(2)` integrality, `maxFoodPop2 = 2350` (my subtract
run: 2350) and `maxLayerAtH27 = 21366` (my superset action set, `trunc10`: 21417 — a subset action set cannot exceed
it, so the figure is sound). The v1 numbers are correctly marked void (`invalidated.v1Predictions`, `supersedes`).

## 5. Numbers (my enumeration; v2 semantics; `H=27`, `H=45` where marked)

| configuration | N(80) | N(110) | note |
|---|---|---|---|
| v2 as published | **20** | **25** | `7 + ⌈cost/630⌉`, exact; C1–C6 all inert |
| v1 (banking) | 15 | 20 | void; fixture v1 reproduced 64/64 |
| completion requires pop 3 | 22 | 26 | best pop-3 line; dominated |
| A8 false (queue after growth) | 19 | 24 | outside Θ; B3a |
| one-item overflow carry (`≤525`) | 19 | 24 | §12.2 variant; B3b |
| A2 scope = tiles only (`q=615`) | 21 | 25 | `13×615 = 7995 < 8000`; B5 |
| A1 palace +0 / +1 / +3 | 27/23/18 | 33/28/22 | `H=27` fails at 110 for +0,+1; `H=45` |
| GS-style amenity table | 22 | 27 | `> H` at 110 |
| C4/C5/C6/C7, any value | 20 | 25 | C7 inert by ≥ 2250 food units |

## 6. Model vs game (keep conditional)

- Provable now: `N ∈ {20,25}` over C1–C6; `pop ≤ 3`; max pop-2 food 2310/2350; max pop-3 food 900–1050; `T(3)≥3300`
  never crossed; `T(4)` never evaluated; guards otherwise hold by enumeration.
- Game facts: **none** (`[V]=0`). 80/110, palace `+2 P`, the Happy tier table, `T(1)=15`, `req(pop)`,
  `PrereqPopulation=2` stay `[C]/[D*]/[A]`; `[20,25]` is an interval in a restricted model, never an
  earliest-settler answer.
- v2 is *restrictive* on three counts (IDLE accrual, queue precedence, starvation) and *relaxing* on two (citizen
  idling, `newCitizen=best`). Only the relaxing pair is safe for a real-game lower bound; the restrictive trio
  needs inertness proofs, not adjectives (B6).

## 7. Ordered next actions

1. Totalise `extraGain`; regenerate §10's trace from the model (fix `q=420`); let O8 own all figures (B1).
2. Replace `handBoundWarning` with the closed form + the pop-3 dominance bound (B2).
3. Decide `[19,25]` vs axes for A8/`idleCarry` (B3); add A1/A2 sensitivity rows and `H ≥ 34` or `HorizonOk` (B5).
4. Re-derive the 720 (B4); retire C7 by enumeration, or stop calling it active.
5. Rewrite `legal` as `step.isSome` + `step_total` (B9); add starvation restriction-inertness (B6); fix G6's
   premises (B7); optionally drop `build` by dominance (B8).
