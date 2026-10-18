# COST-FRONTIER.md — pop-2 vs pop-3 across settler cost (CONDITIONAL, untrusted search)

Scope: the exact-step model `M_MVP` of `search/mvp.py`, baseline candidate
`θ*` (`growth_first`, `newCitizen = best`, `amenityStock = 2`, `basket = zero`,
exact rounding), σ = `sigma-capital-4tiles-v1`. The settler cost is varied
*outside* the frozen contract box `Θ_MVP = {8000, 11000}` (`settlerCost ∈
{80, 110}`). This is a model-internal sensitivity study. **It is not a Civ6
fact, not a proof of a general strategy theorem, and not a contract claim.**
`[V] = 0`, no build is pinned.

Artifacts owned by this study:

* `search/cost_frontier.py` — the executable bounded search (standard library
  only, imports `search/mvp.py` read-only);
* `fixtures/cost-frontier.json` — frozen evidence (envelopes, grid rows,
  boundary witnesses, pop-4 side check, self-test);
* `Civ6Verify/Bounds/CostFrontier.lean` — an **achievability-only**
  kernel-checked witness at cost 13861 (no minimality claim);
* this document.

Reproduce:

```bash
python3 search/cost_frontier.py --self-test      # ~60 s
python3 search/cost_frontier.py --envelope        # M2/M3 envelope, ~8 s
python3 search/cost_frontier.py --cost 13861 --json
python3 search/cost_frontier.py --check-fixture   # replay frozen witnesses, ~9 s
scripts/lean-env lake build Civ6Verify.Bounds.CostFrontier   # ~0.3 s cached
python3 scripts/audit-axioms.py                   # PASS
```

---

## 1. Definitions (explicit)

A *play* is a legal exact-step sequence from `init = (1,0,0,0)`; completion at
step `g` means `trained` first becomes `≥ 1` at `g`. All comparisons cap the
population at 3 (the pop-4 caveat is §6).

* **Strict pop-2 class.** A play that never performs a growth event with
  target population `≥ 3`. Because `growth_first` resolves growth before
  production and before completion, this is exactly "forbid growing to pop 3".
  `N_p2(c)` is the least completion time in this class.
* **Pop-3 (growth-event reading).** A play that performs a growth event with
  target population `≥ 3` at some step on or before its completion. A SETTLER
  that completes on the very step that grows `2 → 3` counts: the step grows
  first, computes the credited `q` at population 3, and only then drops the
  citizen. `N_p3(c)` is the least completion time in this class.
* **Pop-3 (standing-state reading).** Same, but a *standing* population-3 state
  must exist strictly before the completing step. This is the stricter
  secondary reading; `N_p3^stand(c)`.
* The completion drop never sets a flag ("avoid drop after completion"): flags
  come from growth events (primary) or pre-states (secondary), never from the
  post-completion population.
* `pop3_helps(c) := N_p3(c) < N_p2(c)`.

Both readings answer the same way at the first crossing (§4), so the ambiguity
does not change the headline number.

### Method

`prepared_for_cost(c)` builds an `mvp.Prepared` from the validated baseline and
substitutes only `cost = c`; the step relation is **borrowed verbatim** from
`search/mvp.py` (`_step_prepared`). No rule is re-implemented, so the search
cannot drift from the frozen executable. The search is exact-layer BFS over
`(pop, food, prog, trained, flag)` with dedup *within* a layer (the same
convention as `mvp.frontier_search`). Horizons are bounded as follows:

* the frontier decision uses `H(c) = N2_upper(c) = 7 + ⌈c/630⌉`, the exact
  strict pop-2 completion time. If no pop-3 completion exists by then, then
  `N_p3(c) ≥ N_p2(c)`, so no larger horizon can change the verdict;
* a small fixed slack (`+8`) is used only when *reporting* `N_p3` above the
  strict pop-2 time;
* the global envelope (§3) uses one cost-free BFS to `H = 44`.

### Baseline pop-2 lower bound (elementary, model-internal)

Reaching pop 2 takes `≥ 7` steps (`mvp/LOWER-BOUND.md` Lemma 1: six pop-1
steps generate at most `6·220 = 1320 < 1500`). No step with pre-turn pop 1 can
credit progress, and at pop 2 without growth the maximum credit is `630`
(`GH+PH` or `PH,P`). Hence

```
N_p2(c) ≥ 7 + ⌈c/630⌉  ,   and  PH,P every step attains it  ⇒  N_p2(c) = 7 + ⌈c/630⌉.
```

This is the same case-A argument as `mvp/LOWER-BOUND.md` §4.1, extended to an
arbitrary cost. It is *not* yet a Lean theorem (see §7).

---

## 2. The frontier at the two contract costs (regression check)

| cost `c` | `N_p2` | `N_p3` (growth) | pop-3 helps? |
|---|---|---|---|
| 8000  | 20 | 22 | no |
| 11000 | 25 | 26 | no |

These match the documented `20/25` optima and the semantic review's `22/26`
pop-3 lines. Growing to pop 3 is *dominated* at both contract costs; the
crossover is a large-cost phenomenon.

---

## 3. Credit envelope (one cost-free BFS)

`credit_envelope` runs the step relation with a huge cost (completion never
fires) and records, per step `t`:

* `M2[t]` — max credited progress at step `t` for the strict pop-2 class
  (`= 630·(t−7)`, first credited step `t = 8`);
* `M3[t]` — max credited progress at a `SETTLER` step `t` for a play that
  reaches pop 3 (growth-event flag; the credited `q` is included).

Then `N_p2(c) = min {t : M2[t] ≥ c}` and `N_p3(c) = min {t : M3[t] ≥ c}`, so
the envelope determines the first helping cost **exactly** (no per-cost BFS).

```
 t   M2      M3(growth)  M3(standing)
18   6930      4830          0
19   7560      5670       5565
20   8190      6510       6405
21   8820      7350       7245
22   9450      8190       8085
23  10080      9030       8925
24  10710      9870       9765
25  11340     10710      10605
26  11970     11550      11445
27  12600     12390      12285
28  13230     13230      13125
29  13860     13965      13965   <-- first t with M3 > M2 on the same step
30  14490     14700      14700
31  15120     15435      15435
32  15750     16170      16170
33  16380     16905      16905
34  17010     17640      17640
35  17640     18375      18375
```

For each `t`, the costs whose pop-3 line completes at `t` are
`(M3[t−1], M3[t]]`, and pop 3 helps exactly on
`(max(M3[t−1], M2[t]), M3[t]]`.

---

## 4. Result: the first helping cost is 13861

```
first cost with N_p3 < N_p2  =  13861   (growth-event and standing readings agree)
first 100-quantum axis value =    139   (cost 13900)
last non-helping cost        =  13860   (N_p2 = N_p3 = 29)
```

Helping windows from the envelope (growth reading):

| completion `t` | costs `c` with `N_p3(c) = t < N_p2(c)` |
|---|---|
| 29 | 13861 … 13965 |
| 30 | 14491 … 14700 |
| 31 | 15121 … 15435 |
| 32 | 15751 … 16170 |
| 33 | 16381 … 16905 |
| 34 | 17011 … 17640 |
| 35 | 17641 … 18375 |
| … | (contiguous from 17011 onward inside the `H = 44` envelope) |

**There is no universal crossover interval.** The windows are narrow and
separated by non-helping gaps: pop 3 helps on `[13861, 13965]`, stops helping
on `[13966, 14490]`, helps again on `[14491, 14700]`, stops, and so on. The
first window is only 105 units wide. This is a consequence of the two step
functions `M2` (slope 630) and `M3` (slope ≈ 735, but with the pop-3 ramp-up):
`N_p3` and `N_p2` each jump at different costs, so `N_p3 < N_p2` holds only
while `N_p2` has just jumped and `N_p3` has not. Only once `M3` has opened a
persistent lead (from `c > 17010`) does the relation stay true in the sampled
range.

A 100-quantum grid (`fixtures/cost-frontier.json → gridWindow`) shows the same
non-monotonicity at readable resolution:

| cost | `N_p2` | `N_p3` | helps? |
|---|---|---|---|
| 13700 | 29 | 29 | no |
| 13800 | 29 | 29 | no |
| 13900 | 30 | 29 | **yes** |
| 14000 | 30 | 30 | no |
| 14100 | 30 | 30 | no |

Early and late spot grids are in the fixture (`gridEarly` all `no`,
`gridLate` all `yes` from 17011).

### Candidate witnesses at the first crossing

Both readings of "pop-3" produce a 29-step witness at cost 13861, and in both
the strict pop-2 class needs 30.

**Growth-event witness** (pop 3 first appears *within* the completing step):

| steps | pre-pop | work | extra | build | note |
|---|---|---|---|---|---|
| 1–7 | 1 | `G` | ⊥ | IDLE | grow to pop 2 at step 7 (food 1540 → basket 0) |
| 8–28 | 2 | `GH,PH` | ⊥ | SETTLER | `e = 110`, `q = 630` each; at step 28 food 2310, prog 13230 |
| 29 | 2 | `GH,PH` | `P` | SETTLER | `d = 100` ⇒ grows `2 → 3`; extra adds 100P ⇒ `P = 700`, `q = 735`; `prog = 13965 ≥ 13861` ⇒ completes, post `(2, 0, 104, 1)` |

**Standing-state witness** (pop 3 exists for a full step before completion):

| steps | pre-pop | work | extra | build | note |
|---|---|---|---|---|---|
| 1–7 | 1 | `G` | ⊥ | IDLE | as above |
| 8–27 | 2 | `GH,PH` | ⊥ | SETTLER | at step 27 prog 12600 |
| 28 | 2 | `G,GH` | `PH` | SETTLER | `d = 200` ⇒ grows to pop 3; `P = 600`, `q = 630`; post `(3, 0, 13230, 0)` |
| 29 | 3 | `GH,PH,P` | ⊥ | SETTLER | `d = 0`, `P = 700`, `q = 735`; `prog = 13965 ≥ 13861` ⇒ completes, post `(2, 0, 104, 1)` |

**Strict pop-2 witness** (`N_p2 = 30`, growth to pop 3 never performed):
`G × 7` IDLE, then `GH,PH`/`PH,P` SETTLER for 23 steps; at step 30
`prog = 13335 + 630 = 13965 ≥ 13861`, post `(1, 0, 104, 1)`. Its per-step
credits never exceed 630 and no step grows the city past pop 2.

`--check-fixture` replays every stored witness through the frozen step
relation and asserts: final `trained ≥ 1`; the pop-2 witness never grows to
pop 3; both pop-3 witnesses do.

---

## 5. What is and is not claimed

* **Claimed (within the model):** in the exact-step `M_MVP` baseline, under the
  population ≤ 3 cap and the definition of §1, the first settler cost at which
  a pop-3 growth line completes strictly earlier than every strict pop-2 line
  is `13861`; `13860` does not help; the relation is non-monotone and has no
  universal threshold or interval. The envelope of §3 makes this exact within
  its horizon `t ≤ 44` (costs up to `M3[44] = 24990`).
* **Not claimed:** any Civ6 statement; any statement for the other 127
  contract θ combinations; any exact `OptimalAt` certificate (no upper-bound
  witnesses for 127 θ, see `mvp/LOWER-BOUND.md` §7 and O5); any claim that
  13861 is special in the game or in Θ_MVP.
* The relation is *not* monotone, so "first helping cost" is a first-crossing
  statement only. Reporting it as a threshold would be wrong.

---

## 6. Pop-4 caveat (why the horizon cap matters)

`M_MVP` supports population 4 (threshold `T(4) = 4420`) and the model can reach
it at large horizons. The frontier comparison deliberately **forbids pop 4**
(`pop_cap = 3`) so the question stays exactly "pop 2 versus pop 3". The
`pop4SideCheck` entry in the fixture re-runs the *unrestricted* `pop ≤ 4` BFS
at the boundary costs and confirms that at `c = 13860/13861`, up to horizon 41
/ 42, population 4 is never reached and zero transitions are blocked by the
pop-3 cap. So the cap is not active at the crossing. It is still enforced
everywhere else, so a later pop-4 line cannot silently enter a pop-2 vs pop-3
comparison. No global pop-4 statement is inferred.

---

## 7. Lean artifact and the remaining blocker

`Civ6Verify/Bounds/CostFrontier.lean` kernel-checks, with the existing
cost-parameterised model `Civ6Verify/Model/Mvp.lean`:

```lean
def cost13861Params : Params := { cost := 13861 }
def witnessCost13861 : List Action :=
  List.replicate 7 aIdleG ++ List.replicate 21 aSettlerGHPH ++ [aSettlerGHPH_P]

theorem cost13861_achievable : AchievableAt (model cost13861Params) goal 29
```

It also checks the length (29), legality, the exact final state
`{pop := 2, food := 0, prog := 104, trained := 1}`, and two trace facts that
make the pop-3 growth kernel-visible: after 28 steps the state is
`(2, 2310, 13230, 0)`, and the final action satisfies `wouldGrow = true`. All
closed by `decide +kernel`. No Mathlib, no `sorry`, no `native_decide`, no
custom axiom; `audit-axioms.py` passes.

**This is achievability only.** To turn "pop 3 helps at 13861" into a theorem
one also needs the *strict pop-2 lower bound* `N_p2(13861) ≥ 30`. That is the
`mvp/LOWER-BOUND.md` bridge obligation (B-1 credit rule, B-5 accounting
identities, B-6 assembly), which is not yet formalised for arbitrary cost. No
general strategy theorem is claimed or faked here; the search document and the
Lean witness together give a reproducible candidate, not a certified
`OptimalAt`.

---

## 8. Trust summary

| item | status |
|---|---|
| step relation | borrowed verbatim from `search/mvp.py` (`_step_prepared`) |
| `mvp.py` modified? | no |
| `fixtures/cost-frontier.json` | generated by `--write-fixture`, replayed by `--check-fixture` |
| self-test | `ok = true` (model equivalence at 8000/11000, baselines 20/25, pop-3 lines 22/26, envelope and boundary checks) |
| search trust | **untrusted estimate**, `gameFactClaim = false` |
| Lean witness | kernel-checked achievability only; no minimality, no sorry/axioms |
| CI / root files | untouched (this study adds no root import; the library glob picks up the new module) |
