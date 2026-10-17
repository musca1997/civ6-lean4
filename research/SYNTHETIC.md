# SYNTHETIC.md — 合成 Tiny City 基准（v0）：规则、穷举层与 Lean 复现说明

> 归属：本文件与 `search/synthetic.py`、`fixtures/synthetic-v0.json` 是本轮的唯一产物（owned files）。
> 未修改仓库内其他任何文件。Python 3.13，仅标准库。
> 参考但**不依赖**：`research/RULES-RESEARCH.md`（真实规则仍有大量未决项）、`research/ENVIRONMENT.md`（本机无 Civ6）、`research/TOOLCHAIN.md`（Lean 4.25 已在 `.tools/`）。

---

## 0. TL;DR 与免责声明

**这是一个完全合成（synthetic）的极小回合制基准，不是《文明 VI》。**

- 人口增长阈值、地块产出、移民费用、回合内顺序**全部是人为发明的整数常量**，目的是给 Lean 侧一个状态空间极小、可完全穷举、规则无歧义的证明靶子。
- 本文件与生成器中的任何数字都**不是** Civ6 公式、Civ6 数值或 Civ6 最优解；它们不构成对真实游戏的任何断言，也**不可**作为真实规则参数使用。
- Python 搜索是**不受信任的候选生成器**。它只能说明"在这个合成模型里，按这份 Python 实现，最早第 5 tick 达成"；模型与实现的一致性由 `fixtures/synthetic-v0.json` + Python 内部测试 + 将来的 Lean 穷举各自独立检查。
- 真实 Civ6 的约束（浮点取整、宜居度乘数、住房、政策卡、费用递进、回合内结算顺序）在 v0 里一概不存在，见 `research/RULES-RESEARCH.md` §0/§6。本基准刻意绕开这些不确定项，好让"证明形态"可以先于"规则核实"推进。

候选结果（synthetic，未证明）：

| 项 | 值 |
|---|---|
| 合成最早达成 tick | **5** |
| 见证动作序列 | `(1,0), (1,0), (1,0), (1,0), (0,2)`（前 4 tick 单个市民上 farm，第 5 tick 两个市民上 mine） |
| 距离层状态数 t=0..5（BFS，最短路径层） | 1, 2, 4, 6, 7, 7（共 27 个不同状态，其中 26 个非目标） |
| 精确步数层状态数 t=0..5（Lean 核心 `Frontier`） | 1, 2, 4, 7, 9, 10（含重复到达的旧状态；见 §9.5） |
| 展开的 (state, action) 对 | 41 |
| 最短长度达成序列条数 | 1（唯一） |
| 目标状态（规范编码） | 唯一：`pop=1;food=0;prod=0;done=1` |
| Lean ↔ fixture 自动核对（只读） | 47/47 一致（最近核对时场景 md5 `9510cf77…`；见 §2.2 / §11.4） |

---

## 1. 为什么需要这个合成基准

PLAN.md 的 M1–M3 需要一条完整的"可达性 + 无更早方案"管道，但真实规则（M0）在本机被阻塞：没有 Civ6 安装，没有存档 fixture，增长阈值是浮点、宜居度乘数、结算顺序均未定。若先等真实规则，Lean 核心（状态/动作/合法性/结算/完成事件/逐层枚举）就无法开工。

v0 的定位：

| 目标 | v0 是否满足 |
|---|---|
| 状态空间极小且有限，可被 Lean `decide` 完全穷举 | 是（≤ 97 个状态可达上界，笛卡尔上界 192） |
| 1–2 市民的粮食 vs 生产权衡 | 是（pop ∈ {1,2}，2 个地块，每 tick 全量分配） |
| 明确的有限合法动作集，无隐式"其它选择" | 是（见 §6；排除项逐条列出） |
| 确定性回合顺序 | 是（见 §7） |
| 单调完成计数 + 人口前置 | 是（`settlersCompleted`，pop ≥ 2） |
| 精确整数运算（无浮点、无取整歧义） | 是 |
| 首个最优点 ≤ 8 tick | 是（5） |
| 与真实 Civ6 一致 | **否，且不打算一致** |

它服务的是"证明契约的形状"（`Goal`、`step`、逐层可达、`NoEarlier`），不是"Civ6 的事实"。真实规则核实后，v0 作为回归靶子保留，但**不得**把 v0 的定理改写成关于 Civ6 的定理。

---

## 2. 文件、命令、可复现性

```text
search/synthetic.py          # 规则契约/转移/动作枚举/BFS/见证/内部测试/CLI（stdlib only）
fixtures/synthetic-v0.json   # 冻结的规则 + 初态 + 目标 + 候选预期（由 --emit-fixture 生成）
scripts/check-synthetic.py   # 实际 Lean 输出 ↔ fixture 的交叉核对（stdlib only）
research/SYNTHETIC.md        # 本文件
```

```bash
python3 search/synthetic.py                  # 人类可读报告（层数、见证、逐 tick 表）
python3 search/synthetic.py --json           # 机器可读候选
python3 search/synthetic.py --emit-fixture   # 打印规范 fixture JSON（确定性输出）
python3 search/synthetic.py --check-fixture  # 语义比较冻结文件与当前实现
python3 search/synthetic.py --self-test      # 28 个内部测试（unittest）
python3 scripts/check-synthetic.py           # 实际 Lean 输出 vs fixture（47 项检查）
```

### 2.1 fixture 检查的精确语义

- `--check-fixture` 比较的是**解析后的 JSON 语义相等**：`fixtureId`、`version`、`kind`、`synthetic`、`civ6Model`、`disclaimer`、`purpose`、`timeModel`、`rules`、`roundOrder`、`growthThresholds`、`actionEnumeration`、`initialState`、`initialGoal`、`goal`、`expected` —— **全部 16 个顶层键**逐一比较，嵌套值递归比较；空白、缩进、键的顺序都无关。
- 它**不是字节比较**。当前 `--emit-fixture` 的输出恰好与冻结文件逐字节相同（确定性序列化，已验证），但这不是契约；重新格式化 fixture 不会让检查失败，改一个数值/文字才会。
- fixture 缺失、不是合法 JSON、或缺少必需字段 ⇒ `FixtureError`，`--check-fixture` 退出码 **2**，**不是**跳过（旧实现抛 `SkipTest`，导致没有 fixture 时测试仍显示 OK，已修复）。
- `test_fixture_file_matches_spec` 在 fixture 缺失时同样失败；`test_missing_or_corrupt_fixture_is_an_error` 固定这一行为。

### 2.2 Lean ↔ fixture 交叉核对（`scripts/check-synthetic.py`）

目的：把"Lean 场景里手抄的常量与层数"和冻结 fixture 之间的漂移变成**可执行检查**，而不是评审时的人工对读。

- **期望值全部来自 fixture，实际值全部来自运行 Lean**。脚本不内嵌任何预期数字（不硬编码 5、`[1,2,4,6,7,7]`、27、41 等），只从 fixture 读取时间视界 `N` 和见证动作注入探针。
- 实际值来自 `Civ6Verify.Scenarios.Synthetic` 的定义：`Frontier model t`（精确步数层）、`distLayer t`（距离层）、`checkCertificate`、`earliestGoalTick?`、`run`、`witnessStates`、`actionSequences`，以及场景重抄的规则常量。
- 共 **47 项检查**，分三类：
  1. **fixture 自洽**：`layerCounts == distanceLayerCounts == [len(reachableLayers[t])]`、`exactStepFrontierCounts == [len(exactStepFrontiers[t])]`、层 digest 重算、见证长度/首尾状态、`distinctStatesTotal == Σ 层数`、fixture 内 `progressCap == cost-1` 等；
  2. **规则常量**：Lean 的 `popMin/popMax/foodPerCitizen/farmFood/farmProd/mineFood/mineProd/settleCost/settlePopCost/prereqPop/progressCap/threshold1/threshold2/foodCap1/foodCap2` vs `fixture.rules`，并检查 Lean 侧 `progressCap == settleCost-1`；
  3. **语义**：`Frontier`/`distLayer` 的逐层**状态集合**、最早达成 tick、`checkCertificate N = true` 且 `N-1 = false`、用 fixture 动作重放后的终态、Lean 自带 `witnessStates`、目标序列数、`distinctStatesTotal`、`expandedTransitions`。
- 退出码：`0` 全部一致；`1` 语义不一致；`2` fixture 缺失/非法/缺字段；`3` Lean 工具链不可用；`4` Lean 构建或探针求值失败（场景可能正被其 owner 修改、或 API 改名）。
- 脚本**不修改**任何 Lean 文件：探针写在仓库外的临时目录；只有在源码比 `.olean` 新（或 `.olean` 缺失）时才执行 `scripts/lean-env lake build Civ6Verify.Scenarios.Synthetic`，因此可能写 `.lake/` 构建产物。`--no-build` 可强制复用现有 `.olean`。
- `Civ6Verify/Scenarios/Synthetic.lean` 归另一个任务所有，本轮**只读**。退出码 `4` 只表示"此刻无法核对"，既不是 BMK 失败，也不是 fixture 有错。

---

## 3. 规则集 v0（精确常量）

唯一真值来源：`search/synthetic.py` 的 `RULES_SPEC`；冻结副本在 fixture 的 `rules` 段，二者由 `--check-fixture` 强制一致。

| 常量 | 值 | 说明 |
|---|---|---|
| `popMin`, `popMax` | 1, 2 | 城市人口上下界；人口在 `[1,2]` 内 |
| `foodPerCitizenPerTick` | 2 | 每市民每 tick 消耗 2 食物 |
| farm | food 3, production 1 | 粮食地块（也产 1 产能，见 §7 可观测性） |
| mine | food 0, production 2 | 生产地块，不产粮食 |
| 增长阈值 `T(p)` | `T(1)=4`, `T(2)=8` | 线性 `T(p)=4p`，**刻意不是** Civ6 曲线 |
| 食物下限 | 0 | 净粮食为负时只把储粮压到 0；**无饥荒、无人口下降** |
| 食物上限 | `T(pop)-1` | 食物相结束时 `food ≤ T(pop)-1`；满人口（pop=2）时超出 7 的部分丢弃 |
| 移民费用 | 8 | 生产进度 0..7 |
| 移民人口代价 | 1 | 完成时人口 −1 |
| 前置人口 | 2 | 完成瞬间要求 `pop ≥ 2` |
| 前置未满足时的进度上限 | `cost−1 = 7`（**派生值**，不单独存储） | 进度可以攒，但满 8 也不能完成；见 §3.1 |
| 完成时食物/生产 | 0 / 0 | 完成后 `(pop-1, 0, 0, done+1)` |

### 3.1 规则契约（cap 单一来源 + 显式校验）

`Rules`（Python）与 fixture 的关系是"数据 + 契约"，不是"默认值 + 说明文字"：

1. **生产进度上限只有一个来源**：`progress_cap := settler_cost − 1`。Python 里它是只读 property（没有存储字段）；Lean 场景里 `progressCap` 必须满足同一等式（`scripts/check-synthetic.py` 会核对）。
   `step` 的封顶（`min(raw, progress_cap)`）与 `check_state` 的状态界（`prod ≤ max_progress()`）读同一个派生量，因此不可能再出现"step 产出 9、check_state 只允许 ≤7"的错位。
2. fixture 仍然**声明** `settler.productionProgressCap`（为了可读性），但 `Rules.from_spec` 会验证 `productionProgressCap == cost − 1`；不一致时抛 `RuleSpecError`，**不会**在两者中挑一个静默修正。
3. `Rules.to_spec()` 由**当前实例字段**重建规则块，不再返回全局 `RULES_SPEC`。`default_rules().to_spec() == RULES_SPEC` 成立；扰动后的规则（如 `farm_prod=0`、`cost=9`）会生成自己的块，`Rules.from_spec(r.to_spec()) == r`。
4. 其余契约由 `Rules.__post_init__` / `validate_rules` 强制（`dataclasses.replace` 也会触发）：
   - `1 ≤ pop_min ≤ pop_max`；增长阈值**恰好**覆盖 `pop_min..pop_max` 且严格为正；
   - 地块产出、每人消耗、`food_floor` 非负；
   - 地块集合**恰好**是 `{farm, mine}`（多余、改名、重复或缺失地块都被拒绝，不会静默忽略）；
   - `pop_min ≤ settler_prereq_pop ≤ pop_max`，且完成后人口仍在范围内：对每个可能完成的 `p`，`p − populationCost ≥ pop_min`；
   - 完成重置值落在结果状态的界内：`0 ≤ onCompleteFood ≤ max_food(p − populationCost)`、`0 ≤ onCompleteProduction ≤ progress_cap`；
   - 所有整数字段必须是**普通 int**（bool、字符串、浮点被拒绝）。

回归测试：`test_rules_contract_rejects_malformed_configurations`（20 种畸形配置）、`test_rule_contract_applies_to_dataclass_replace`、`test_progress_cap_has_a_single_source`、`test_to_spec_respects_instance_fields`（§13 #20/#22/#23/#26）。

被显式排除（fixture `actionEnumeration.excluded`）：闲置市民、金币/信仰购买、队列切换/其它建造项、砍伐、改良、贸易、蛮族、区域/建筑/奇观/政策效果、边界扩张、单位移动与建城。

**没有**建模的机制不作为"无影响"默认项：它们被列为排除项，任何"最早 5 tick"的结论只在这个受限模型内成立（与 PLAN.md §2.3 的要求一致）。

---

## 4. 状态空间

状态是四元组（全部为整数）：

```text
s = (pop, food, production, settlersCompleted)
```

| 分量 | 取值域 | 依据 |
|---|---|---|
| `pop` | `{1,2}` | `popMin..popMax` |
| `food` | `pop=1: 0..3`，`pop=2: 0..7` | `0 ≤ food ≤ T(pop)-1` |
| `production` | `0..7` | `0 ≤ production ≤ cost-1` |
| `settlersCompleted` | `{0,1}` | 单调；搜索把目标态当终止态 |

初态（fixture `initialState`）：

```text
s0 = (pop=1, food=0, production=0, done=0)    # t = 0
```

### 4.1 基数

- 笛卡尔上界：`(4 + 8) × 8 × 2 = 192`。
- 更强上界：完成事件只会产生 `(pop-1, 0, 0, done+1)`，而 `pop-1 = 1`，故目标态只有唯一一个 `(1,0,0,1)`；于是可达上界 `96 + 1 = 97`。
- 实际在 t ≤ 5 内可达的不同状态：**27**（其中非目标 26、目标 1）。远小于"几百个状态"的预算，Lean 侧用 `decide`/`Finset` 穷举无压力。

### 4.2 规范编码

```text
pop=<p>;food=<f>;prod=<q>;done=<d>
```

层 digest = `sha256`（对层内规范编码排序后逐行拼接，取前 16 个 hex 字符）。digest 只是**Python 侧交叉核对**用途；Lean 不必复现 hashlib，直接比较状态集合或状态数即可。

---

## 5. 转移函数（精确数学定义）

记规则常量如上。给定状态 `s = (p, f, q, d)` 与动作 `a = (α, β)`（α = 上 farm 的市民数，β = 上 mine 的市民数），合法条件为 `α, β ≥ 0`、`α + β = p`、`d = 0`。

### 5.1 产出（按**增长前**的人口计算）

```text
N(α, p) = 3α + 0·β − 2p = 3α − 2p        （净粮食）
G(α, p) = 1α + 2β = 2p − α               （本 tick 产能增量）
```

用到的具体值：

| p | 动作 (α,β) | N | G |
|---|---|---|---|
| 1 | (0,1) mine | −2 | 2 |
| 1 | (1,0) farm | +1 | 1 |
| 2 | (0,2) | −4 | 4 |
| 2 | (1,1) | −1 | 3 |
| 2 | (2,0) | +2 | 2 |

### 5.2 食物相与增长

```text
F0 = max(0, f + N)
```

- 若 `p = 1`：
  - `F0 ≥ 4`  ⇒  `p' = 2`, `f' = F0 − 4`
  - 否则      ⇒  `p' = 1`, `f' = F0`
  （因 `f ≤ 3` 且 `N ≤ 1`，此时 `F0 ≤ 4`，所以增长后 `f' = 0`，不存在溢出。）
- 若 `p = 2`：
  - `p' = 2`, `f' = min(F0, 7)`（满人口，超出阈值−1 的粮食被丢弃）

即：**先用本 tick 的分配与增长前人口算净粮食，再做（至多一次的）增长，再封顶。**

### 5.3 生产相与前置门

```text
R = q + G
```

- 若 `p' = 1`（前置未满足）：
  `q' = min(R, progress_cap)`（即 `min(R, cost−1)`），`d' = d`，状态为 `(1, f', q', d)`。
  —— 进度可以累积（上限 7），但**不可能完成**。
- 若 `p' = 2`：
  - `R ≥ 8` ⇒ `d' = d + 1`，状态为 `(1, 0, 0, d')`（人口 −1，食物与进度清零；超出 8 的产能丢弃）
  - `R < 8` ⇒ `(2, f', R, d)`

### 5.4 不变量（Python 中由 `check_state` 强制，Lean 侧应作为定理）

对任意合法 `s` 与合法 `a = step(s,a) = (p', f', q', d')`：

1. `1 ≤ p' ≤ 2`
2. `0 ≤ f' ≤ T(p') − 1`
3. `0 ≤ q' ≤ 7`
4. `d' ∈ {0,1}` 且 `d' ≥ d`（完成计数单调不减）
5. `d' = d + 1` 仅当 `p' = 2` 且 `R ≥ 8`；且此时结果恒为 `(1,0,0,1)`

Python 的内部测试对全部可达状态检查了 1–4；`test_witness_replay`、`test_progress_cap_while_prereq_unmet_wastes_production` 覆盖 5 的两个分支。

---

## 6. 动作枚举（显式、有限、全量）

对 pop = p 的非目标状态：

```text
A(p) = { (k, p−k) : 0 ≤ k ≤ p }        按 k 升序枚举
|A(1)| = 2,  |A(2)| = 3,  |A(目标态)| = 0
```

- **全量分配**：每个市民恰好工作一个地块，不存在"闲置"这一隐含选项；两个市民可以同地块（合成规则，允许）。
- 枚举顺序（`k` 升序）是规范顺序，BFS 与见证选择都依赖它，从而端到端确定。
- `step` 以 `IllegalAction` 拒绝：人数和为负、人数和 ≠ pop、非二元组、非整数、bool、以及目标态上的任何动作。`test_legal_action_enumeration_is_total_and_exact` 对 pop ∈ {1,2} 穷举了 `(α,β) ∈ [−1..p+1]²`，确认"枚举内 ⇔ 可执行"。

> Lean 对应物：`LegalAction s a ↔ a ∈ enumerate s`，且 `enumerate` 无遗漏——这正对应 PLAN.md M1 的"动作枚举与合法性定义的一致性/完备性"通过条件。

---

## 7. 回合顺序（确定性）与顺序可观测性

一个 tick 的固定顺序：

1. 读入本 tick 的市民分配（依据 tick 开始时的状态）；
2. 用**增长前**人口算出 `N`、`G`；
3. 食物相：`F0 = max(0, f + N)`；
4. 增长相：`while pop < 2 ∧ F0 ≥ T(pop)`，减阈值、加人口；随后若 `pop = 2` 则 `food = min(food, 7)`；
5. 生产相：`R = q + G`；
6. 前置门：`pop < 2` ⇒ 进度封顶 7，禁止完成；
7. 完成结算：`pop ≥ 2 ∧ R ≥ 8` ⇒ `done += 1`, `pop -= 1`, `production = 0`, `food = 0`。

**为什么顺序是可观测的（不是装饰）**：farm 故意给 1 产能，使"同一 tick 内既增长又完成"可达。
例：`s = (1, 3, 7, 0)`，动作 `(1,0)`（farm）：`F0 = max(0, 3+1) = 4 ⇒ 增长到 pop 2`，`q' = 0`，`R = 7 + 1 = 8 ≥ 8` ⇒ 完成，结果 `(1, 0, 0, 1)`。
若先做生产判定（用增长前 pop），则 `min(R,7) = 7`，本 tick 不会完成——两种语义结果不同。`test_growth_then_production_order` 固定了本模型的语义。

同理，`test_prereq_gate_caps_progress` 固定了前置门的语义：`(1,0,7,0)+mine` 仍是 `(1,0,7,0)`（攒到 7 也被卡住），而 `(2,0,7,0)+2 mines` 直接完成。

---

## 8. 目标与单调完成标记

```text
Goal(s)  ⇔  s.settlersCompleted ≥ 1
```

- 目标只看**历史完成计数**，不看当前队列或生产进度（PLAN.md §2.1 的要求）。
- 计数单调：`step` 中只增不减；Python `step` 内显式断言不得下降。
- 目标态是**终止态**：`legal_actions` 返回 `[]`，因此搜索中 `done` 恒为 0 或 1。
- 初态不是目标（`test_initial_state_is_not_goal`；fixture `"initialGoal": false`）。
- 完成后的唯一状态是 `(1,0,0,1)`（§5.4 第 5 条），这让 Lean 的下界证明可以退化成"某个具体状态不在前 N 层"。

---

## 9. 穷举搜索：定义、精确性、候选结果

### 9.1 定义（距离层）

```text
L₀ = { s₀ }
L_{t+1} = ∪_{s ∈ L_t} { step(s,a) : a ∈ A(s) }  \  (L₀ ∪ … ∪ L_t)      # 目标态不展开
最早达成 T* = min { t : L_t 中存在目标态 }
```

`L_t` 是**最短距离恰为 t** 的状态集（"距离层"）。它与"恰好 t 步可达"不同：后者允许回到距离更小的状态，见 §9.5；Lean 核心的 `Frontier` 用的是后者。

- **无任何剪枝**：不删动作、不做支配/启发式剪枝、不限制分配组合。唯一的"去重"是 `state → 最早层`，并且
  若 `s` 在第 `t₁ < t₂` 层都可达，则从 `(s,t₂)` 能到的东西从 `(s,t₁)` 也能到（转移是马尔可夫的），因此丢弃更晚的重复**不改变**最短达成长度。这是"去重"而不是"剪枝"，论文式地写出来是为了让 Lean 侧不复刻错语义。
- 找到第一个含目标态的层后停止（这就是"最早目标"搜索，而不是继续铺满整个时间轴）。因此 fixture 只记录 `t ≤ T*` 的层。
- 见证选择：在 `L_{T*}` 的目标态中取路径动作序列的字典序最小者。v0 中最短序列本来唯一，但选择规则是确定性的。

### 9.2 独立校验（Python 内部）

`brute_force_sequences` 穷举**所有**长度 t 的动作序列（不跨长度去重），`brute_force_distance_layers` 用 `dist(s) = min{t : s 在恰好 t 步可达}` 独立重建距离层，再与 BFS 层逐层比较（`test_bfs_is_exact_against_bruteforce`，t = 0..6），并另外验证"恰好 t 步可达集合 ⊆ 距离 ≤ t 的并集"。最早达成 tick 也由暴力枚举独立复算。

这是**实现之间**的差异测试，不是模型正确性证明，更不是 Civ6 一致性证据。注意：该 oracle 复用同一 `step`/`legal_actions`，只独立于 BFS 的"去重/层记账"，因此它能发现记账与覆盖错误，但**不能**发现转移语义本身的错误；后者需要 Lean 交叉核对（§11.4）或独立复实现。

### 9.3 逐层数据（候选，untrusted）

```text
t | 距离层 | 精确步数层 | 目标数 | 距离层 digest(16 hex) | 距离层状态（pop,food,prod,done）
--+--------+------------+--------+-----------------------+--------------------------------------
0 |   1    |     1      |   0    | 6f3078e295c37a2d      | (1,0,0,0)
1 |   2    |     2      |   0    | 0ecc2157f5727424      | (1,0,2,0) (1,1,1,0)
2 |   4    |     4      |   0    | a3c7b293f185b687      | (1,0,3,0) (1,0,4,0) (1,1,3,0) (1,2,2,0)
3 |   6    |     7      |   0    | d1439f3d864c93e8      | (1,0,5,0) (1,0,6,0) (1,1,4,0) (1,1,5,0) (1,2,4,0) (1,3,3,0)
4 |   7    |     9      |   0    | f7d8c2aafcc15066      | (1,0,7,0) (1,1,6,0) (1,1,7,0) (1,2,5,0) (1,2,6,0) (1,3,5,0) (2,0,4,0)
5 |   7    |    10      |   1    | a9b4f04653b430d8      | (1,0,0,1) (1,2,7,0) (1,3,6,0) (1,3,7,0) (2,0,6,0) (2,0,7,0) (2,2,6,0)
```

精确步数层 digest：前 3 层与距离层相同，之后为
`584a08d7227f8259`、`c9033f6aed9b4385`、`9e0e06713d16b44d`。

（编码中 `(pop,food,prod,done)`。完整字符串列表见 fixture 的 `expected.reachableLayers` 与 `expected.exactStepFrontiers`。）

规模：不同状态 27；展开的 `(state, action)` 对 41；最短达成序列 1 条。

### 9.4 见证（逐 tick）

| t | pop | food | prod | done | 动作 | 说明 |
|---|---|---|---|---|---|---|
| 0 | 1 | 0 | 0 | 0 | (初始) | |
| 1 | 1 | 1 | 1 | 0 | farm=1, mine=0 | 净粮 +1，产能 +1 |
| 2 | 1 | 2 | 2 | 0 | farm=1, mine=0 | |
| 3 | 1 | 3 | 3 | 0 | farm=1, mine=0 | 储粮到 3（pop=1 的上限） |
| 4 | 2 | 0 | 4 | 0 | farm=1, mine=0 | 4 ≥ T(1) ⇒ 增长，食物清零，产能 4 |
| 5 | 1 | 0 | 0 | 1 | farm=0, mine=2 | 4+4 = 8 ≥ 8 且 pop=2 ⇒ 完成；pop→1，计数 +1 |

动作序列：`(1,0), (1,0), (1,0), (1,0), (0,2)`（`(farm,mine)` 市民数）。

---

### 9.5 两种"层"必须区分（Lean 复现陷阱）

| 概念 | 定义 | t=0..5 状态数 |
|---|---|---|
| 距离层 `L_t`（本文件 BFS） | 最短距离恰为 t | 1, 2, 4, 6, 7, 7 |
| 精确步数层 `F_t`（`Civ6Verify/Reachability/Finite.lean` 的 `Frontier M t`） | 恰好 t 步可达（允许重复到达旧状态） | 1, 2, 4, 7, 9, 10 |

二者从 t=3 起分叉，多出来的正是"回到更短距离状态"的重复项：

```text
t=3: F₃ \ L₃ = { (1,0,4,0) }
t=4: F₄ \ L₄ = { (1,0,6,0), (1,1,5,0) }
t=5: F₅ \ L₅ = { (1,0,7,0), (1,1,7,0), (1,2,6,0) }
```

`F_t ⊇ L_t` 恒成立（恰好 t 步可达包含最短路径为 t 的那些状态）。搜索用 `L_t` 是因为去重后层数最小且对最短达成等价；而 Lean 核心的 `Frontier` 不去除跨层重复，所以用它复现时应期待 `[1,2,4,7,9,10]`，**不能**期待 `[1,2,4,6,7,7]`。`test_exact_step_frontiers_match_lean_frontier_notion` 固定了这个区别；fixture 同时记录两种数据。

---

## 10. 下界论证（合成模型内的手工版 + 穷举版）

### 10.1 手工界（可作为将来 M4 的解释性定理素材）

1. **增长不早于 t = 4**：pop=1 时 `f ≤ 3` 且每 tick `N ≤ +1`（唯一正净粮动作是 farm），所以增长发生在 tick t 需要 `f_{t−1} = 3`，而 `f` 每 tick 至多 +1 且从 0 起，故 `t−1 ≥ 3`，即 `t ≥ 4`。因此在 t ≤ 3 的所有状态里 `pop = 1`（与 §9.3 的层数据一致）。
2. **t ≤ 3 不可能完成**：完成要求 `pop ≥ 2`（前置门），与第 1 条矛盾。
3. **t = 4 不可能完成**：完成判定用的是 tick 4 开始时的状态（层 3）加本 tick 产出。层 3 全为 pop=1，要增长需 `f₃ = 3` 且动作必须是 farm（`G = 1`）；而 `f₃ = 3` 只能由 3 个连续 farm tick 达成，于是 `q₃ = 3`，`R = 3 + 1 = 4 < 8`。故 t=4 无目标态。
4. 因此 `T* ≥ 5`；配合 §9.4 的见证，`T* = 5`。

第 3 步其实已经要做"粮食与生产互相争用市民"的联合推理；直接分别取"最大粮食"和"最大生产"是错的（见 §12）。

### 10.2 穷举版（Lean 侧的目标形态）

`NoEarlier(5)` 只需：对 `t = 0..4` 的每一层验证 `Goal` 为假，并验证层递推覆盖（每个非目标状态的**全部**合法动作的后继都在下一层或更早层中）。

- 按距离层：1+2+4+6+7 = 20 个状态；
- 按 Lean 核心的精确步数 `Frontier`：1+2+4+7+9 = 23 个状态（`Frontier 0..4`）。

无论哪种口径，加上唯一完成态 `(1,0,0,1)`，规模都在"几十个具体状态"量级，`decide`/直接枚举即可，不需要任何启发式。

---

## 11. Lean 复现与自动核对（只读引用 Lean，不改其文件）

仓库里已有另一个工作流产出的通用核心 `Civ6Verify/Reachability/Finite.lean`（本文件只读引用，不修改、不依赖其当前细节；它可能继续演进）。其接口正好可以承载 v0：

```lean
class Model (State : Type u) (Action : Type v) where
  init : State
  step : State → Action → State            -- 全函数
  legal : State → Action → Prop            -- 权威合法性
  legalDec : (s) → (a) → Decidable (legal s a)
  legalActions : State → List Action       -- 可计算枚举
  legalActions_sound : ∀ s a, a ∈ legalActions s → legal s a
  legalActions_complete : ∀ s a, legal s a → a ∈ legalActions s
```

以及 `ReachableFrom`/`Reachable`（恰好 t 步）、`Frontier`（精确步数层）、`AchievableAt`、`NoEarlier`、`OptimalAt`、`checkCertificate`、`optimalAt_of_checkCertificate`、`earliestGoalTick?`、`witnessAt`。

### 11.1 v0 → `Model` 实例映射

| v0 概念（本文件） | Lean 落地 |
|---|---|
| `State = (pop, food, production, done)` | `structure State`（4 个 `Nat` 字段）+ `deriving DecidableEq` |
| 规则常量（§3） | 场景模块里的 `def`/`lemma`，**不是** `Model` 字段 |
| `legal_actions s = [(k, p−k) \| k ≤ p]` | `Model.legalActions s := (List.range (s.pop+1)).map (fun k => (k, s.pop−k))` |
| `_validate_action` | `Model.legal s a := a.1 + a.2 = s.pop ∧ s.done = 0`（`Nat` 保证非负；`legalDec` 用 `decide`） |
| `step`（非法输入抛异常） | `Model.step` 为全函数；非法输入取值任意（如原状态），所有定理只对 `legal` 量化，因此全函数化无害 |
| 枚举完备性（§6） | 需证 `legalActions_complete`：由 `α + β = p` 得 `α ≤ p` 且 `(α,β) = (α, p−α)` |
| `goal s := s[3] ≥ 1` | `goalB : State → Bool := fun s => s.done ≥ 1`，并证 `hspec : goalB s = true ↔ goal s` |
| `bfs` 的最早目标 | `checkCertificate M goalB 5 = true`，再用 `optimalAt_of_checkCertificate` 得 `OptimalAt M goal 5` |
| 见证（§9.4） | `run M M.init [(1,0),(1,0),(1,0),(1,0),(0,2)]` + `LegalPath`，或用 `witnessAt M goalB 5` |
| 生产进度上限 | `progressCap := settleCost - 1`（单一派生来源，见 §3.1） |
| 精确步数层 | `Frontier M t`（**注意：不是**本文 BFS 的距离层，见 §9.5） |

### 11.2 建议先证的小引理

1. `step_legal_invariants`：`legal s a → 后继满足 §5.4 的 5 条不变量`（含 `done` 单调）。
2. `completion_unique`：任何 `done = 1` 的可达状态都等于 `(1,0,0,1)`。
3. `goals_none_below_five`：`∀ t < 5, ∀ s ∈ Frontier M t, goalB s = false`。
4. `frontier_five_has_goal`：`∃ s ∈ Frontier M 5, goalB s = true`。
5. `optimal_at_five`：由 3、4 经 `checkCertificate` 组合。

### 11.3 数值对照（供 Lean 断言；候选，来自 fixture）

```text
|Frontier 0..5|      = [1, 2, 4, 7, 9, 10]     # 精确步数层（Lean 核心口径）
|L0..L5|（距离层）    = [1, 2, 4, 6, 7, 7]      # Python BFS 口径，仅供对照
展开边数 = 41；不同状态 = 27；完成态 = pop=1;food=0;prod=0;done=1
Frontier 5 含目标态 (1,0,0,1)，Frontier 0..4 不含任何目标态
```

**陷阱**：`Frontier` 不去除跨层重复，所以对 Lean 断言 `[1,2,4,6,7,7]` 会失败；`6` 是"最短距离层"数，不是 `Frontier` 的大小。`test_exact_step_frontiers_match_lean_frontier_notion`（§13 #3）专门锁住这个区别。

### 11.4 自动核对：`scripts/check-synthetic.py`（新增）

`Civ6Verify/Scenarios/Synthetic.lean`（另一 owner）已经把 v0 常量、`step`、`Frontier`、`distLayer`、`checkCertificate` 和见证都形式化了，并证明了 `OptimalAt model goal 5`。手工抄写会漂移，所以新增只读交叉核对脚本（§2.2）：

```bash
python3 scripts/check-synthetic.py            # 47/47 checks agree（本机实测）
python3 scripts/check-synthetic.py --json     # 机器可读
python3 scripts/check-synthetic.py --no-build # 复用现有 .olean
```

- 期望值：**只**来自 `fixtures/synthetic-v0.json`（含规则常量、两类层的计数与逐状态集合、见证、聚合量）；
- 实际值：**只**来自运行 Lean（探针导入场景模块，用其自身的 `Frontier`/`distLayer`/`checkCertificate`/`earliestGoalTick?`/`run`/`actionSequences` 计算）；
- 因而脚本里**没有**任何重复的期望数字，不存在"两处都写 5 所以永远通过"的问题。
- 当前状态：47/47 一致（最近核对时 `Civ6Verify/Scenarios/Synthetic.lean` 的 md5 为 `9510cf77…`）。该文件由其 owner 持续修改，**快照会过期**：以脚本退出码为准。退出码 4 表示"此刻无法核对"（构建失败/API 改名），不是 BMK 结论或 fixture 的错误。

注意：`decide`/`native_decide` 的额外信任负担按 PLAN.md §6 披露；本基准规模小（`Frontier 0..5` 最多 10 个状态），优先用可归约的 `decide` 或直接给出逐层 `Finset`/`List` 等式证明。场景当前使用 `decide +kernel`，不在本文件的所有权范围内。


---

## 12. 不要混淆"最大粮食"与"最大生产"

几种偷懒做法在 v0 上都会给出错误或不可辩护的答案：

| 朴素做法 | 得到的 tick | 为什么错 |
|---|---|---|
| 只算增长：4 tick 攒 4 粮（+1/tick），再按 pop=2 的最大产能 4/tick 造 8 | 4 + 2 = **6** | 把两个独立最优相加。farm tick 本身产 1 产能，4 个 farm tick 已存下 4 产能，因此只需 1 个 pop=2 的 mine tick（4+4=8），答案 5。 |
| 只算产能：8 / 4 = 2 tick | **2** | 忽略了 pop≥2 前置与"pop=1 时最多 2 产能/tick、且进度封顶 7"。 |
| 认为"储粮/产能更多永远更好，可以分别最大化" | — | pop=2 时食物超过 7 被丢弃，pop=1 时产能超过 7 被丢弃；两者还争用同一批市民，不能分别取最大再相加。 |

正确做法：在**联合状态**上枚举分配（本基准只有 2/3 个动作），而不是在边缘上分别取极值。这正是 PLAN.md §5（M4）与 §6 强调的点，v0 用一个 27 状态的例子把它做成可穷举的回归测试。

顺带一提：v0 的最优解**恰好**是"先纯 farm 再纯 mine"，但这是本组常量的巧合，不是一般规律；换常量（例如 `T(1)=6` 或 farm 产能 0）最优点会移动，不能把"先粮后产"当定理。

---

## 13. 内部测试清单（28 个，全部通过）

```text
python3 search/synthetic.py --self-test     # Ran 28 tests ... OK
```

| # | 测试（unittest 字母序） | 覆盖内容 |
|---|---|---|
| 1 | `test_all_successors_are_covered_by_layers` | 枚举完备性：层 t 的每个合法后继都落在 `d ≤ t+1` 的某层 |
| 2 | `test_bfs_is_exact_against_bruteforce` | BFS 距离层 = 全序列枚举重建的距离层（t ≤ 6）；最早达成 tick 独立复算 = 5 |
| 3 | `test_exact_step_frontiers_match_lean_frontier_notion` | 精确步数层 `[1,2,4,7,9,10]`、距离层 `[1,2,4,6,7,7]`、`L_t ⊆ F_t` |
| 4 | `test_farm_production_sensitivity_is_documented` | 参数扰动（farm 产能 0 ⇒ 最优 6）与 §14 一致；不属于冻结 fixture |
| 5 | `test_fixture_checker_detects_tampering` | 篡改 `expected`/`rules` 会被 `fixture_mismatches` 抓到 |
| 6 | `test_fixture_comparison_is_semantic_and_covers_every_key` | 全部 16 个顶层键参与比较；`disclaimer`/`purpose`/`timeModel`/额外键都能抓到；`first_difference` 给出嵌套路径 |
| 7 | `test_fixture_file_matches_spec` | 冻结 fixture 与当前实现语义一致；缺失即失败（不跳过） |
| 8 | `test_food_floor_and_max_pop_cap` | 负净粮压到 0；满人口食物封顶 7；增长溢出清零 |
| 9 | `test_goal_predicate_and_monotone_marker` | 目标谓词；BFS 边上 `done` 不下降；目标态无动作；`done ∈ {0,1}` |
| 10 | `test_growth_then_production_order` | 同 tick 增长+完成（顺序语义） |
| 11 | `test_horizon_shorter_than_optimum_finds_no_goal` | 视界 4 找不到目标；视界 5 与 8 结果一致 |
| 12 | `test_illegal_assignments_rejected` | 超配/少配/负数/错误元数/字符串/bool/目标态动作 |
| 13 | `test_illegal_states_rejected` | pop/food/prod/done 越界状态被拒绝 |
| 14 | `test_initial_state_is_not_goal` | 初态非目标、`done=0` |
| 15 | `test_legal_action_enumeration_is_total_and_exact` | 枚举 = `{(k,p−k)}`；枚举外动作全部被拒 |
| 16 | `test_missing_or_corrupt_fixture_is_an_error` | 缺文件 / 非法 JSON ⇒ `FixtureError`，**不是** `SkipTest` |
| 17 | `test_no_goal_before_optimum` | t < 5 各层无目标态 |
| 18 | `test_no_pruning_bounds` | 状态总数 ≤ 192；`|L₀| = 1` |
| 19 | `test_prereq_gate_caps_progress` | pop=1 进度封顶 7；pop=2 同样数据可完成 |
| 20 | `test_progress_cap_has_a_single_source` | cap = `cost−1`（property）；扰动 cost 后 step/`check_state` 同步；不存在可替换的 cap 字段 |
| 21 | `test_progress_cap_while_prereq_unmet_wastes_production` | 溢出产能被丢弃（不累积） |
| 22 | `test_rule_contract_applies_to_dataclass_replace` | `replace` 触发契约校验；合法扰动（cost=9）通过 |
| 23 | `test_rules_contract_rejects_malformed_configurations` | 20 种畸形规则（cap 冲突、cost 0、缺/零阈值、负产出、popCost 清空城市、字符串/bool 字段、改名/多余/重复地块、缺 tiles/settler）全部被拒 |
| 24 | `test_rules_roundtrip` | `Rules ↔ RULES_SPEC` 往返一致 |
| 25 | `test_step_is_deterministic` | 同输入同输出（全部可达状态） |
| 26 | `test_to_spec_respects_instance_fields` | `to_spec` 由实例字段重建；默认等于 `RULES_SPEC`；扰动实例往返一致；矛盾 cap 被拒 |
| 27 | `test_witness_replay` | 重放 = 记录状态序列；末态目标；见证为字典序最小最优序列 |
| 28 | `test_witness_tamper_detected` | 去掉最后一 tick 失败；弱化一步不达成；改第一步导致后续非法 |

另外：

- `python3 search/synthetic.py --check-fixture`：全部 16 个顶层键的语义比较（§2.1），缺失/非法 fixture 退出码 2；
- `python3 scripts/check-synthetic.py`：fixture ↔ **实际 Lean 输出** 47 项检查（§2.2 / §11.4）。

---

## 14. 边界、当前状态与下一步

### 14.1 本基准不建立的结论

- 不建立任何 Civ6 结论（最优回合、瓶颈、公式）；
- 本轮不新增 Lean 定理。`Civ6Verify/Scenarios/Synthetic.lean`（**另一 owner**）已证明 `OptimalAt model goal 5`，本文件只通过 `scripts/check-synthetic.py` **只读**核对其输出；该证明不是本文件的产物，也不能当作 v0/M0 或真实游戏结论（见 `SCOPE.md`）。
- 不建立"Python 与 Lean 完全等价"的证明：交叉核对是有限视界内的语义比较（47 项），不是外延相等的定理。
- 不建立"去重不会丢失更优解"以外的搜索保证（搜索正确性只对本模型的马尔可夫语义成立）。

### 14.2 本轮结束时的确切状态（2026-10-17）

| 检查 | 结果 |
|---|---|
| `python3 search/synthetic.py --self-test` | **28/28 OK**（0 skip、0 fail） |
| `python3 search/synthetic.py --check-fixture` | **OK**：16/16 顶层键语义一致（非字节比较） |
| `python3 scripts/check-synthetic.py` | **PASS 47/47**（fixture vs 实际 Lean 场景；最近核对 md5 `9510cf77…`，该文件由他人维护、可能继续变化） |
| `python3 search/synthetic.py` | 合成最早达成 tick **5**，唯一见证 `(1,0)×4,(0,2)`（候选，未证明） |
| 缺 fixture / 非法 JSON | `--check-fixture` 退出码 2；测试 `FixtureError` 失败而非跳过 |
| 畸形规则配置 | 20 种全部 `RuleSpecError`；`replace` 同样受契约约束 |

这些数字仍只是**合成基准的候选结果**：不是 Civ6 数值，不是 Civ6 最优解，不构成对真实游戏的任何断言。

### 14.3 fixture 变更（本轮，对照评审 pin `ce6a2fc5…`）

**只改了两处，全部数值/语义字段未变**：

1. `rules.coverageModelling.settlerProductionWhilePrereqUnmet` 的说明文字由 `"progress capped at cost-1 (7)"` 改为 `"progress capped at cost-1"`（去掉硬编码 7，因为 cap 现在是派生量；不影响任何行为）；
2. `expected.rulesDigest` 由 `421cef78…` 变为 `fdd5a616…`（`Rules` 不再存 `progress_cap` 字段，digest 覆盖 14 个字段而非 15 个）。

把这两处还原后，fixture 的 md5 正好等于评审 pin 的 `ce6a2fc523f93a374845ae6d3d800f61`，可作为"其余字段完全未动"的证据。`rules` 的其余键、`expected` 的所有数值（optimum 5、两类层、见证、27/41、序列数 1）保持原样。

### 14.4 被独立评审指出的项（本轮处理）

评审文件：`research/REVIEW.md`（评审 pin：Python `8ec52a2c…`、fixture `ce6a2fc5…`）。

| 评审项 | 本轮处理 | 证据 |
|---|---|---|
| **S3-2**（MEDIUM）生产进度上限有两个真值来源，`step` 与 `check_state` 可能错位 | 删除存储字段，cap 改为**派生** `settler_cost−1`；`from_spec` 校验 fixture 声明的 cap 等于派生值；`replace(progress_cap=…)` 已不可表达 | §3.1；`test_progress_cap_has_a_single_source`、`test_rules_contract_rejects_malformed_configurations` |
| **S4-2**（LOW）`Rules.to_spec()` 忽略实例字段，扰动规则会静默输出默认常量 | `to_spec()` 由实例字段重建；默认实例等于 `RULES_SPEC`；扰动实例往返一致 | §3.1；`test_to_spec_respects_instance_fields` |
| **S4-3**（LOW）缺 fixture 被 `SkipTest` 掩盖；文档称"逐字节"但只比较部分键 | 缺文件/坏 JSON ⇒ `FixtureError`（`--check-fixture` 退出码 2）；比较改为**全部 16 个顶层键的语义相等**；文档改为"语义比较，非字节比较" | §2.1；`test_missing_or_corrupt_fixture_is_an_error`、`test_fixture_comparison_is_semantic_and_covers_every_key` |
| **S4-5**（LOW/INFO）没有自动的 Lean ↔ fixture 核对 | 新增 `scripts/check-synthetic.py`：期望值只来自 fixture、实际值只来自运行 Lean，47 项检查（含 fixture 自洽、规则常量、两类层、证书、见证、聚合量） | §2.2 / §11.4；`check-synthetic.py` 运行输出 |
| **S4-4**（LOW，本文件部分）`SYNTHETIC.md` 有陈旧表述（"本轮没有 Lean 文件权限"、无自动核对） | 更新 §11/§14：说明 Lean 场景由另一 owner 维护、只读引用；新增交叉核对与确切状态 | §11.4、§14.2 |
| S1-1 / S3-1 / S4-1 / S4-4（其余） | 属于 M0、Lean 场景或他人文档（`Civ6Verify/Scenarios/Synthetic.lean`、`research/REACHABILITY.md`）。本任务**不改动**其他 owner 的文件；S4-1 的 33 序列注释仍待场景 owner 修复 | 未处理，明确记录 |

### 14.5 建议的后续（在各自文件归属内）

1. Lean 侧（另一 owner）修复 S3-1 的 `distLayer_no_goal_below_five` 陈述与 S4-1 的注释计数；本脚本已核对真实数值（33 条 5 步序列、1 条达成序列），可作对照。
2. 用 v0 校准"逐层可达 + 完备动作覆盖"的证书检查器（含篡改测试）；本基准的 `checkCertificate N/N−1 = true/false` 已由交叉核对覆盖。
3. 把 §10.1 的手工界发展成参数化引理（阈值、farm 产能、费用为参数），并给出反例参数。
4. 真实规则（`RULES.md`/`SCOPE.md`）一旦可核实，另建**显式标注非合成**的 fixture；不得把 v0 的常量、层数或定理迁移成 Civ6 结论。

参数扰动示例（仅说明敏感性，不作为候选结果）：若把 farm 产能从 1 调到 0，则 farm tick 不再存产能，最快为 4 个 farm tick（增长）+ 2 个 pop=2 mine tick = 6，与 v0 的 5 不同。这提示"v0 的 5"高度依赖人为常量，因此更不能外推到真实游戏。
