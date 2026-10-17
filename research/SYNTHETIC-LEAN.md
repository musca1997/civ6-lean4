# SYNTHETIC-LEAN.md — 合成基准 `synthetic-v0` 的 Lean 内核验证报告

> **本文件与 `Civ6Verify/Scenarios/Synthetic.lean` 是本轮的唯一产物（owned files）。**
> 未修改仓库内任何其他文件；`Civ6Verify/Reachability/Finite.lean` 与 `Civ6Verify.lean`
> 仅被 `import`（它们由另一个工作流维护，本轮在其重建后的版本上编译通过）。
>
> **这不是《文明 VI》。** 增长阈值 4/8、farm (3 粮, 1 产)、mine (0 粮, 2 产)、
> 移民费用 8、完成扣 1 人口，全部是为"证明工程"发明的整数常量。本文件、
> `Synthetic.lean` 中的任何数字与定理都**不是** Civ6 公式、数值或最优解，也不构成
> 对真实游戏的任何断言或证据。
>
> Python 侧（`search/synthetic.py`、`fixtures/synthetic-v0.json`、`research/SYNTHETIC.md`）
> 依旧是不受信任的候选生成器。本报告只说明：**Lean 内核**在一个独立重写的模型上
> 复核了同一组数字，并且证书是无 `sorry` / 无 `native_decide` / 无自定义公理的。

---

## 0. TL;DR

| 项 | 结果 | Lean 定理 |
|---|---|---|
| 合成最优 tick | **5** | `optimalAt_five : OptimalAt model goal 5` |
| 见证动作 | `(1,0),(1,0),(1,0),(1,0),(0,2)` | `witness`、`witness_legal`、`witness_run` |
| 见证逐 tick 状态 | 与 fixture `witnessStates` 逐项一致 | `witness_trace_eq` |
| 精确步数层大小 t=0..5 | **1, 2, 4, 7, 9, 10** | `frontier_counts` |
| BFS 距离层大小 t=0..5 | **1, 2, 4, 6, 7, 7** | `distLayer_counts` |
| 唯一目标态 | `pop=1;food=0;prod=0;done=1` | `reachable_goal_state`、`frontier_five_goal_unique` |
| 最短长度达成序列条数 | **1**（穷举全部合法 5 步序列） | `actionSequences_five_goals`、`optimalSequenceCount`、`unique_optimal_sequence` |
| 可达不同状态（t≤5） | **27** | `distinctStatesTotal` |
| BFS 展开的 (state, action) 对 | **41** | `expandedTransitions` |
| 笛卡尔上界 / 完成可达上界 | **192 / 97** | `cartesianStateUpperBound`、`completionReachableUpperBound` |
| 公理审计 | 仅 `[propext, Quot.sound]` | §7 |

---

## 1. 复现命令与输出

```bash
cd ~/.pi/civ6-lean4

# 1) 通用核心（只读依赖；本轮未修改）
scripts/lean-env lake build Civ6Verify.Reachability.Finite
#   Build completed successfully.

# 2) 场景模块
scripts/lean-env lake build Civ6Verify.Scenarios.Synthetic
#   Build completed successfully.  (约 2.5–3 s)

# 3) 单文件内核检查（#print axioms 会打印到 stdout）
scripts/lean-env lake env lean Civ6Verify/Scenarios/Synthetic.lean
```

`#print axioms` 的完整输出（31 条，全部只有标准核心公理，或 `[]`）：

```text
'Civ6Verify.Scenarios.Synthetic.legalActions_sound' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.legalActions_complete' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.initial_not_goal' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.semantics_growth_then_completion' does not depend on any axioms
'Civ6Verify.Scenarios.Synthetic.witness_legal' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.witness_run' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.step_done_ge' depends on axioms: [propext]
'Civ6Verify.Scenarios.Synthetic.reachable_pop_bounds' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.witness_trace_eq' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.frontier_counts' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.checkCertificate_five' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.optimalAt_five' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.optimalAt_five'' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.no_legal_path_below_five' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.distLayer_counts' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.distLayer_no_goal_below_five' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.distLayer_no_goal_below_five'' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.distLayer_goal_flags' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.distLayer_subset_frontier' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.exact_step_not_distance' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.exact_step_not_distance_five' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.frontier_five_goal_unique' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.reachable_goal_state' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.completion_state_only_from_five' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.mem_sequencesFrom' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.legalSequences_five_count' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.actionSequences_five_goals' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.optimalSequenceCount' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.unique_optimal_sequence' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.distinctStatesTotal' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Scenarios.Synthetic.expandedTransitions' depends on axioms: [propext, Quot.sound]
```

没有 `sorryAx`、没有 `Lean.ofReduceBool`（`native_decide`）、没有 `Classical.choice`、
没有自定义 `axiom`、没有 Mathlib。

除上述 27 条以外，还对**全部 84 条定理**逐一做了 `#print axioms` 临时探针复核
（探针不写入仓库）：全部只含 `propext` / `Quot.sound` 或不含任何公理，没有
`sorryAx`、`Classical.choice`、`Lean.ofReduceBool`。

**关于 `decide +kernel`：** 所有数值型判定都用 `decide +kernel`。它把可判定命题
**交给内核归约**（`mkDecideProof` + 内核检查辅助引理），不是 `native_decide`：不生成
编译代码、不引入 `Lean.ofReduceBool`。文件里没有出现 `native_decide`。之所以不用默认
`decide`（elaborator 归约），是因为它在 `Frontier 5` 上超出 2,000,000 heartbeats；
`decide +kernel` 在 1 秒内完成且公理审计干净。这是纯性能/信任路径选择，不改变语义。

---

## 2. `Model` 实例：fixture 语义 → Lean

`Synthetic.lean` 完全不依赖 Python，独立重写 fixture 的规则。

### 2.1 类型与规则常量

| fixture / Python | Lean |
|---|---|
| `State = (pop, food, production, settlersCompleted)` | `structure State`（4 个 `Nat` 字段，`deriving DecidableEq, Repr`） |
| `Action = (citizensOnFarm, citizensOnMine)` | `structure Action`（`farm`, `mine : Nat`） |
| `popMin/popMax = 1/2` | `def popMin / popMax` |
| `foodPerCitizenPerTick = 2` | `def foodPerCitizen` |
| farm `(food 3, production 1)` | `def farmFood`、`def farmProd` |
| mine `(food 0, production 2)` | `def mineFood`、`def mineProd` |
| settler `cost 8 / popCost 1 / prereqPop 2 / progressCap 7` | `def settleCost / settlePopCost / prereqPop / progressCap` |
| `T(1)=4, T(2)=8` | `def growthThreshold p := 4 * p`（故 `foodCap 1 = 3`、`foodCap 2 = 7`，见 `foodCap_one/two`） |
| `initialState = (1,0,0,0)` | `def init` / `model.init` |
| `goal = settlersCompleted >= 1` | `def goal s := 1 ≤ s.done`，`goalB`，`goalB_spec` |
| `initialGoal = false` | `initial_not_goal` |

### 2.2 转移函数 `step`（逐条对应 round order）

`step` 是 Python `step` 的逐行转录：

```text
storedAfterFood s a = (s.food + 3*a.farm + 0*a.mine) - 2*s.pop   -- Nat 截断减法 == max(0, ·)
foodPhase pop F     = (growthLoop 2 pop F |>.1,
                       if p' = 2 then min f' 7 else f')          -- 生长循环 + 满人口封顶
raw                 = s.prod + (1*a.farm + 2*a.mine)
if 2 ≤ p' then
  if 8 ≤ raw then { pop := p' - 1, food := 0, prod := 0, done := s.done + 1 }
  else            { pop := p', food := f', prod := raw, done := s.done }
else              { pop := p', food := f', prod := min raw 7, done := s.done }
```

生长循环按冻结常量展开（`popMax = 2`，循环最多触发一次，且只在 `pop = 1`）：

```lean
def growthLoop : Nat → Nat → Nat → Nat × Nat
  | 0, pop, food => (pop, food)
  | fuel + 1, 1, food => if 4 ≤ food then growthLoop fuel 2 (food - 4) else (1, food)
  | _, pop, food => (pop, food)
```

`step` 对**非法**动作也是全函数（返回某个状态）；所有定理只对 `legal` 动作量化，
`illegal` 分支的取值无关。这一点与 Python `step` 抛 `IllegalAction` 的差别是刻意的，
已在此记录。

### 2.3 逐 tick 语义复核（fixture 自己的断言）

`Synthetic.lean` §5 用内核把这些语义钉死（全部 `decide +kernel`，公理 `[]` 或 `[propext]`）：

| 定理 | 内容 | 对应 Python 测试 |
|---|---|---|
| `semantics_growth_then_completion` | `(1,3,7,0) + farm → (1,0,0,1)`：同 tick 既增长又完成 | `test_growth_then_production_order` |
| `semantics_prereq_gate_pop_one` | `(1,0,7,0) + mine → (1,0,7,0)`：前置未满足不能完成 | `test_prereq_gate_caps_progress` |
| `semantics_prereq_gate_pop_two` | `(2,0,7,0) + 2 mines → (1,0,0,1)` | 同上 |
| `semantics_food_floor` | `(2,0,0,0) + 2 mines → (2,0,4,0)`：净粮 −4 压到 0 | `test_food_floor_and_max_pop_cap` |
| `semantics_food_cap` | `(2,5,0,0) + 2 farms → (2,7,2,0)`：满人口粮食封顶 7 | 同上 |
| `semantics_growth_overflow` | `(1,3,0,0) + farm → (2,0,1,0)`：增长清零，farm 也存 1 产能 | 同上 |
| `semantics_progress_cap` / `_at_cap` | pop=1 时产能封顶 7，溢出丢弃 | `test_progress_cap_while_prereq_unmet_wastes_production` |

---

## 3. 合法性与动作枚举（独立定义 + sound/complete）

```lean
def legal (s : State) (a : Action) : Prop := s.done = 0 ∧ a.farm + a.mine = s.pop

def legalActions (s : State) : List Action :=
  if s.done = 0 then (List.range (s.pop + 1)).map (fun k => ⟨k, s.pop - k⟩) else []
```

* `legal` **不是**用列表成员定义的：它是独立谓词（"每个市民恰好上一个地块" +
  "目标态无动作"），与枚举之间的双向联系是**定理**：
  * `legalActions_sound : a ∈ legalActions s → legal s a`
  * `legalActions_complete : legal s a → a ∈ legalActions s`
  * `mem_legalActions_iff : a ∈ legalActions s ↔ legal s a`
* `Model` 实例字段 `legalActions_sound/complete` 填的就是上面两条，因此通用核心的
  下界定理（`NoEarlier` 量化在 `Reachable` 上，而 `Reachable` 只用 `legal`）无法被
  "漏枚举一个动作"削弱。
* 目标态（`done = 1`）的 `legalActions = []`，与 fixture "terminal: goal states have no
  outgoing actions" 一致；`legal_not_goal` 与 `goal_monotone` 把它表达为定理。

---

## 4. 精确步数层 vs BFS 距离层（本基准最关键的口径区别）

* **精确步数层**（通用核心 `Frontier M t`，权威口径）："恰好 t 步可达"，允许在更晚
  tick 再次到达先前状态 → 每个重复到达都是新成员。
* **BFS 距离层**（`search/synthetic.py` 的 `L_t`）：保留全局 visited，"最短距离恰为 t"。

本文件两种都实现并**分别**证明，避免把二者混用：

| t | `Frontier model t` 大小 | `distLayer t` 大小 |
|---|---|---|
| 0 | 1 | 1 |
| 1 | 2 | 2 |
| 2 | 4 | 4 |
| 3 | **7** | **6** |
| 4 | **9** | **7** |
| 5 | **10** | **7** |

定理：

* `frontier_counts : (List.range 6).map (fun t => (Frontier model t).length) = [1,2,4,7,9,10]`
* `distLayer_counts : ... = [1,2,4,6,7,7]`
* `distLayer_subset_frontier : s ∈ distLayer t → s ∈ Frontier model t`（一般 t，归纳证明）
* `exact_step_not_distance`：`(1,0,4,0) ∈ Frontier 3` 但 `∉ distLayer 3`（距离 2）
* `exact_step_not_distance_five`：`(1,0,7,0) ∈ Frontier 5` 但 `∉ distLayer 5`（距离 4）
* `distLayer_no_goal_below_five`：**所有** t=0..4 的距离层都不含目标态
  （`(List.range 5).all (fun t => !((distLayer t).any goalB)) = true`）。
  注意极性：弱化的 `all (fun t => (distLayer t).any goalB) = false` 只表示
  "并非每层都有目标"（t=0 无目标就已成立），不表达该性质，已弃用。
* `distLayer_no_goal_below_five'`：逐点形式 `∀ t < 5, (distLayer t).any goalB = false`
* `distLayer_goal_flags`：`(List.range 6).map (fun t => (distLayer t).any goalB) =
  [false, false, false, false, false, true]`（0..4 全 false，仅 5 为 true）
* `distLayer_five_goal`：t=5 的 BFS 层含目标态

**最优性证明用的是精确步数口径**（`checkCertificate` → `NoEarlier` → 对**所有**合法
动作序列量化），这正是 PLAN 要求的"不能漏分支"的口径；距离层只作为交叉核对与
解释性对照，不参与下界。

夹具中的 `exactStepFrontiers` / `reachableLayers` 是**排序后的规范键列表**，Lean 里
给出的是**枚举顺序**的 `State` 列表；两者集合相同（下面的定理逐层固定了内容），
层大小完全一致。`layerDigests` / `rulesDigest` 是 Python 侧 `sha256` 的 16 位摘要，
Lean 不复现 hashlib（见 §8 已知缺口）。

逐层内容定理：`frontier_{zero,one,two,three,four,five}_eq`、
`distLayer_{zero,one,two,three,four,five}_eq`、`frontier_invariants_upto_five`
（`1 ≤ pop ≤ 2`、`food ≤ T(pop)-1`、`prod ≤ 7`、`done ≤ 1`）。

---

## 5. 最优性 = 5

### 5.1 证书路径（主证明）

```lean
theorem checkCertificate_five : checkCertificate model goalB 5 = true := by decide +kernel

theorem optimalAt_five : OptimalAt model goal 5 :=
  optimalAt_of_checkCertificate (M := model) goalB goalB_spec checkCertificate_five
```

`checkCertificate` 是通用核心的"一遍布尔检查"：`Frontier 0..4` 无目标 **且**
`Frontier 5` 有目标。`optimalAt_of_checkCertificate` 把它转成

```text
OptimalAt M goal 5 = AchievableAt M goal 5 ∧ NoEarlier M goal 5
```

`NoEarlier` 的定义是 `∀ t < 5, ∀ s, Reachable M t s → ¬ goal s`，而 `Reachable` 由
权威 `legal` 谓词构造，因此它覆盖**全部**合法动作序列。扫描形式
（`earliestGoalTick? model goalB 8 = some 5`）给出第二份独立证书 `optimalAt_five'`。

### 5.2 显式合法见证

```lean
def witness : List Action := [(1,0), (1,0), (1,0), (1,0), (0,2)]

theorem witness_legal  : LegalPath model init witness
theorem witness_run    : run model init witness = (1,0,0,1)
theorem witness_trace_eq : witnessTrace = witnessStates   -- 与 fixture 的 6 个状态逐项相同
theorem achievable_at_five : AchievableAt model goal 5     -- AchievableAt.of_legalPath
```

`witnessTrace` 是 `k = 0..5` 的前缀重放状态列表；`witness_trace_eq` 内核确认它就是
fixture 的 `expected.witnessStates`（含 t=4 的 pop=2 过渡态 `(2,0,4,0)`）。

### 5.3 下界的多种表述

* `no_goal_below_five : ∀ t < 5, ∀ s ∈ Frontier model t, goalB s = false`
* `no_legal_path_below_five : as.length < 5 → LegalPath model init as → ¬ goal (run model init as)`
  （直接用通用核心的 `noEarlier_iff_all_legalPaths`，覆盖所有合法序列）
* `not_achievable_below_five : ∀ t < 5, ¬ AchievableAt model goal t`
* `completion_state_only_from_five`：唯一完成态只能在 `t ≥ 5` 到达

---

## 6. 单调完成与完成态唯一

* `step_done_ge : s.done ≤ (step s a).done`（对**所有**动作，不只合法）
* `step_done_le_succ : (step s a).done ≤ s.done + 1`
* `reachable_done_le_one : Reachable model t s → s.done ≤ 1`
* `legal_not_goal` / `goal_monotone`：目标态无合法动作；目标一旦成立不会被合法步撤销
* `reachable_pop_bounds`：可达状态 `1 ≤ pop ≤ 2`（Python `check_state` 的不变量在 Lean
  里对可达状态证明；`step` 本身是全函数，不对任意状态承诺不变量）
* `step_goal_shape`：使 `done` 增长的步必是完成分支（`pop'=2`、`raw ≥ 8`），输出
  `(1,0,0,1)`
* **`reachable_goal_state`：任何可达目标态都恰好是 `(pop=1, food=0, prod=0, done=1)`**
  （fixture `completionStateKey` / `goalStatesAtOptimum` 的唯一性）

---

## 7. 穷举合法序列：`optimalSequenceCount = 1`

`search/synthetic.py` 报告最短达成序列唯一。为了让它不只是"枚举器认为唯一"，Lean 里
先证明枚举器**无遗漏**，再穷举：

```lean
def sequencesFrom (s : State) : Nat → List (List Action)
  | 0 => [[]]
  | t + 1 => (legalActions s).flatMap
      (fun a => (sequencesFrom (step s a) t).map (fun rest => a :: rest))

theorem mem_sequencesFrom : as ∈ sequencesFrom s t ↔ as.length = t ∧ LegalPath model s as
theorem mem_actionSequences : as ∈ actionSequences as.length ↔ LegalPath model init as

theorem legalSequences_five_count : (actionSequences 5).length = 33      -- decide +kernel

theorem actionSequences_five_goals :
    (actionSequences 5).filter (fun as => goalB (run model init as)) = [witness]   -- decide +kernel

theorem optimalSequenceCount :
    ((actionSequences 5).filter (fun as => goalB (run model init as))).length = 1

theorem unique_optimal_sequence :
    as.length = 5 → LegalPath model init as → goal (run model init as) → as = witness
```

`actionSequences 5` 共 33 条（4 个 tick 后共有 16 条前缀，其中 15 条处于 pop=1
（每步 2 个动作），唯一到达 pop=2 的前缀 `(1,0)^4` 有 3 个动作：15·2+3 = 33），
内核枚举后只有 `witness` 达成目标。`unique_optimal_sequence` 把"枚举完整"接上"唯一性"，
因此该结论对**全部**合法 5 步序列成立，而不只是对被枚举的那些。

---

## 8. 夹具字段 ↔ Lean 结果对照

| `fixtures/synthetic-v0.json` 字段 | 值 | Lean 对应 |
|---|---|---|
| `expected.syntheticEarliestGoalTick` | 5 | `optimalAt_five`、`optimalAt_five'` |
| `expected.witness` | `[[1,0],[1,0],[1,0],[1,0],[0,2]]` | `witness` |
| `expected.witnessStates` | 6 个状态 | `witnessStates`、`witness_trace_eq` |
| `expected.layerCounts` / `reachableLayers` | `1,2,4,6,7,7` | `distLayer_counts`、`distLayer_*_eq` |
| `expected.distanceLayerCounts` | `1,2,4,6,7,7` | 同上 |
| `expected.exactStepFrontierCounts` | `1,2,4,7,9,10` | `frontier_counts`、`frontier_*_eq` |
| `expected.distinctStatesTotal` | 27 | `distinctStatesTotal` |
| `expected.expandedTransitions` | 41 | `expandedTransitions` |
| `expected.goalStatesAtOptimum` / `goalStateKeysAtOptimum` | 唯一 `(1,0,0,1)` | `frontier_five_goal_unique`、`reachable_goal_state` |
| `expected.optimalSequenceCount` | 1 | `optimalSequenceCount`、`unique_optimal_sequence` |
| `expected.completionStateKey` | `pop=1;food=0;prod=0;done=1` | `reachable_goal_state` |
| `expected.cartesianStateUpperBound` | 192 | `cartesianStateUpperBound` |
| `expected.completionReachableUpperBound` | 97 | `completionReachableUpperBound` |
| `growthThresholds` / `maxFood` | 4,8 / 3,7 | `growthThreshold`、`foodCap_one/two` |
| `initialGoal` | false | `initial_not_goal` |
| `expected.layerDigests` / `rulesDigest` | sha256 前 16 hex | **未在 Lean 复现**（见下） |

### 已知缺口（不影响上述结论）

1. **SHA-256 摘要**：`layerDigests`、`exactStepFrontierDigests`、`rulesDigest` 是 Python
   的 `hashlib.sha256` 截断值；Lean 不实现 hashlib，也没有必要——Lean 直接比较
   `State` 列表/集合与层大小（上面逐层等式），比摘要更强。摘要仍只作为 Python 侧
   交叉核对。
2. **`expandedTransitions = 41`** 的 Lean 定义复刻 Python 的计数口径（对距离层
   `0..4` 的每个状态累加 `|A(s)|`，目标层 5 不展开）。它是记账事实，不是游戏内容。
3. **不变量只在可达状态上证明**：与 Python 的 `check_state` 一样，`step` 对任意状态
   是全函数；`reachable_pop_bounds` 等定理的前提是 `Reachable`。
4. **`step` 的非法动作分支**取值任意（Python 抛异常）。所有规范/证书定理只经过
   `legal` 动作（`Reachable` / `LegalPath` 的定义如此），因此不影响任何结论。
5. **没有 Civ6 内容**：没有真实增长曲线、宜居度、住房、政策、费用递进、回合内
   结算顺序；这些在 fixture 中被显式列为排除项，Lean 侧同样不建模。v0 的"5"只对
   这组人为常量成立（`research/SYNTHETIC.md` §12/§14 的敏感性说明同样适用）。

---

## 9. 与通用核心的接口（未修改，无需改动）

本场景只用 `Civ6Verify.Reachability.Finite` 的公开 API，**没有修改它**，也没有需要
它新增的接口：

```text
class Model (State) (Action)          -- init, step, legal, legalDec, legalActions, sound, complete
Reachable / ReachableFrom            -- 恰好 t 步（只走 legal）
run / LegalPath                      -- 见证格式
Frontier                             -- 精确步数层（dedup 跨 tick 不去重）
AchievableAt / NoEarlier / OptimalAt
checkCertificate / optimalAt_of_checkCertificate
earliestGoalTick? / optimalAt_of_earliestGoalTick?
noEarlier_iff_no_goal_in_frontier / noEarlier_iff_all_legalPaths
successors / mem_successors / mem_frontier_iff / dedup / mem_dedup
witnessAt / witnessAt_spec
```

额外的场景侧工具（距离层、序列枚举、不变量）都定义在 `Synthetic.lean` 内，不进入
通用核心。若核心未来演进，本文件需要的**仍是**上表这些名字/签名；当前版本
（本轮重建后的 `Finite.lean`）编译通过。核心新增的
`AchievableAt.of_mem_frontier`、`optimalAt_of_noGoalBelow_and_witness` 未被依赖，
但也不需要。

---

## 10. 结论（限定在合成基准内）

在**完全合成**的 v0 规则下，Lean 内核检查了：

1. 合法性谓词与动作枚举互相 sound & complete；
2. `step` 忠实复刻 fixture 的 round order（逐 tick 语义断言全部复核）；
3. 精确步数层大小 `[1,2,4,7,9,10]`、BFS 距离层大小 `[1,2,4,6,7,7]`，并显式证明二者
   不同（`exact_step_not_distance`、`exact_step_not_distance_five`）；
4. **合成最早达成 tick = 5**（`OptimalAt model goal 5`），带显式合法见证与逐 tick 状态；
5. 完成计数单调、完成态唯一；
6. 全部合法 5 步序列中恰有 1 条达成目标，且就是见证。

再次强调：**这些都不是《文明 VI》的结论，也不是游戏证据。** v0 的全部常量都是
为证明形态而发明的；真实规则的 Lean 化必须另建显式标注"非合成"的 fixture 与模块。

---

## 11. 评审修复记录（2026-10-17，针对 `research/REVIEW.md`）

本轮只改了本报告与 `Civ6Verify/Scenarios/Synthetic.lean`；通用核心、root、Main、
Python/fixture 均未改动。评审指出的两项场景侧问题已修复：

### 11.1 REVIEW S3-1（`distLayer_no_goal_below_five` 陈述与名字不符）

原陈述

```lean
(List.range 5).all (fun t => (distLayer t).any goalB) = false
```

只表示"并非每一层都有目标"（t=0 无目标即已成立），不表达"0..4 全部无目标"。
现改为真正的全称形式，并补上逐点形式与显式 flag 列表：

```lean
theorem distLayer_no_goal_below_five :
    (List.range 5).all (fun t => !((distLayer t).any goalB)) = true := by
  decide +kernel

theorem distLayer_no_goal_below_five' (t : Nat) (ht : t < 5) :
    (distLayer t).any goalB = false := by
  have h := (List.all_eq_true.mp distLayer_no_goal_below_five) t (List.mem_range.mpr ht)
  exact (not_eq_true_iff_eq_false _).mp h

theorem distLayer_goal_flags :
    (List.range 6).map (fun t => (distLayer t).any goalB) =
      [false, false, false, false, false, true] := by
  decide +kernel
```

`#eval` 复核：0..4 的 `any goalB` 为 `[false,false,false,false,false]`，
`!((distLayer t).any goalB)` 的 `all` 为 `true`，0..5 的 flags 为
`[false,false,false,false,false,true]`。原弱陈述没有被任何证明使用，因此改动不影响
`optimalAt_five` 及其下界论证（下界一直来自精确步数口径的 `no_goal_below_five` /
`checkCertificate`）。

### 11.2 REVIEW S4-1（合法 5 步序列条数：原 docstring 少算 1，实际 33 条）

实际为 **33**：15 个 pop=1 的 4 步前缀 × 2 个动作 + 唯一全 farm 的 pop=2 前缀 × 3 个动作
= `15*2 + 3 = 33`。已把 docstring 改为 33，并把条数本身做成内核定理，防止文档漂移：

```lean
theorem legalSequences_five_count : (actionSequences 5).length = 33 := by
  decide +kernel
```

`actionSequences_five_goals`（唯一达成目标者是 `witness`）与
`optimalSequenceCount = 1`、`unique_optimal_sequence` 不变。

### 11.3 复核结果

* `scripts/lean-env lake build Civ6Verify.Reachability.Finite Civ6Verify.Scenarios.Synthetic`
  → `Build completed successfully`（通用核心快照 md5 `e6f68ffa530704547d4500ed453f8840`
  未变；本场景修复前 md5 `c3f2fbfdc6c50be08a79c14669d8ae63`，修复后
  `9510cf77bff2376ff234ea5c93adcdba`）。
* `scripts/lean-env lake env lean Civ6Verify/Scenarios/Synthetic.lean` → 0 error / 0 warning。
* `#print axioms`：全部新增/修改定理仍只含 `[propext, Quot.sound]`；对全部定理的
  临时探针复核仍无 `sorryAx` / `Classical.choice` / `Lean.ofReduceBool`。
* `python3 search/synthetic.py --check-fixture`：修复完成时（约 22:10）为 `OK`。
  随后 Python 侧 owner 并发修复 review S3-2/S4-2：`search/synthetic.py`
  （md5 `8ec52a2c7cc68284a632a1c6b485921e` → `047bdbf0f016f04711fc549f407447b1`）
  与 `fixtures/synthetic-v0.json`
  （`ce6a2fc523f93a374845ae6d3d800f61` → `d70c4dc0777f44bc32dcc38633874ab1`，
  22:11:59 重新生成）都被更新，`coverageModelling` 文字与 `rulesDigest`
  （`421cef786f6128e4` → `fdd5a616d46320a5`）随之改变。22:12:25 复核：
  `--check-fixture` → `OK`（语义/解析 JSON 相等）。**这些外部改动没有触及本模块**：
  逐项核对 fixture 的语义字段仍是 earliest 5、exact counts `[1,2,4,7,9,10]`、
  distance counts `[1,2,4,6,7,7]`、witness `(1,0)^4,(0,2)`、27 states / 41 transitions、
  `optimalSequenceCount = 1`、`completionStateKey = pop=1;food=0;prod=0;done=1`。
* 本文件与场景文件**不是** Civ6 结论；修复不改变这一限定。
