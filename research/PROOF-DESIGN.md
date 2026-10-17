# PROOF-DESIGN：有限期限「最早移民」认证的最小 Lean4 架构

状态：设计文档，未实现。**本文件不含实现文件**，只给签名、证明策略、陷阱与里程碑。
规则数值全部未核实（见 §7）。文中的所有 Lean 签名与关键证明片段，已于
2026-10-17 用 **Lean 4.25.0**（项目 `.tools/lean-4.25.0-linux` 经 `scripts/lean-env`；并用同版本
nixpkgs `lean4-4.25.0` 独立交叉验证；均无 Mathlib、无第三方依赖）实际编译通过；
标「实测」的结论附有测量数据（§10）。

> 环境事实：本机 Steam 库中**没有** Civilization VI（只有 Liftoff 与运行库），因此 M0
> 的规则核实目前无法在本地取证。架构必须假设「公式未知」，把每个规则细节变成具名参数
> 而不是硬编码常量（§7）。

---

## 1. 不可协商的设计约束

从 `PLAN.md` §2.1 / §3 / §6 抽出，所有后续决策必须满足：

| # | 约束 | 架构后果 |
|---|------|----------|
| C1 | 完成事件用**单调历史**记录，不能只看当前队列/现存单位 | `State.done : Nat`，只增不减；`done_mono` + `goal_stable` 定理 |
| C2 | 下界必须覆盖**全部合法动作**，不是搜索器碰巧生成的路线 | 枚举完备性定理 `legal_mem_allActions`；`Legal` 单一来源 |
| C3 | 有限期限即可，不要求无限状态空间有限 | `NoEarlier p N` 只量化 `t < N`；层集合按需裁剪 |
| C4 | 无浮点 | 全部 `Nat`；阈值/费用为整数参数 |
| C5 | 默认内核可复核；用 `native_decide` 必须披露 | 两档证书，`#print axioms` 审计（§4.5） |
| C6 | 模型规格不得被解答文件重定义 | `ReachableAt`（Prop 规格）与 `layer`（实现）分离，用等价定理桥接 |
| C7 | 精确到回合的边界必须有测试 | fixture 表 F1–F10（§9），含 `N-1`/`N+1` 篡改测试 |

---

## 2. 总体架构

```text
Core/Dedup.lean        集合保持的去重（core 没有 List.mem_eraseDups）
Model/Params.lean      纯数据参数（无函数字段）→ 未核实规则都住在这里
Model/Step.lean        Legal : … → Bool，step : … → State（全函数）
Reach/Enum.lean        allActions + 完备性「界在 Legal 里」技巧
Reach/Layer.lean       succsOf / nextLayer / layer（每层去重，禁止跨层）
Reach/Equiv.lean       ReachableAt ↔ s ∈ layer t（规格=实现）
Cert/Witness.lean      legalPathB / run / AchievableAt（证书 A）
Cert/Bound.lean        checkNoEarlier + 可靠性 / 无误报（证书 B）
Cert/Optimal.lean      OptimalAt := AchievableAt ∧ NoEarlier
Scenarios/Synthetic.lean  round-number 合成场景（明确标注非游戏证据）
Scenarios/Candidate.lean  待核实的真实参数值（只有数值，无证明）
Checks/Axioms.lean     #print axioms 全量审计
search/                不受信任的 Python 候选生成器（只产出 witness / N 候选）
fixtures/              SYNTHETIC/ 与 GAME/（后者在 M0 前为空且标注 unverified）
```

依赖方向严格单向：`Scenarios/*` 只允许**填参数**，不得定义 `Legal`/`step`/`layer`/`Goal`。
这样「模型被解答文件改写」在结构上不可能发生（C6）。

**与仓库现状的对应**：`Core/Dedup.lean` + `Reach/Layer.lean` + `Reach/Equiv.lean` +
`Cert/*` 已经由 `Civ6Verify/Reachability/Finite.lean`（673 行，`Model` 类形式）实现并验证；
上表中 `Model/Params.lean`、`Scenarios/Candidate.lean`、`Checks/Axioms.lean` 与
`fixtures/SYNTHETIC|GAME` 的分离仍是缺口。§3–§5 因此读作「现有核心的设计理由 + 待补层的规格」，
评审与对接见 §13。

**为什么不用 Mathlib**：本设计只需要「有限列表 + `Nat` 算术 + Bool 判定」，core 已经足够。
`Fintype`/`Finset` 完全不需要（见 §3 D5）；引入 Mathlib 会让构建时间从 <1s 变成数分钟，
并给审计引入大量无关公理面。

---

## 3. 十个关键设计决策

### D1 动作 = `Nat` 位掩码，不是函数

```lean
abbrev Action := Nat          -- bit i = 市民 i 在 i 号地块上工作
```

不用 `Fin tiles → Bool`：函数类型没有 `DecidableEq`，无法去重、无法 `decide`、无法写进
`State`，并且完备性会被迫用 `funext`。位掩码把所有比较降成 `Nat` 比较。

### D2 `Params` 只放数据，不放函数

```lean
structure State where
  pop  : Nat
  food : Nat
  prod : Nat     -- 当前移民的生产进度
  done : Nat     -- 已完成移民数（单调历史，C1）
  deriving DecidableEq, Repr

structure Params where
  tiles    : Nat
  foodY    : List Nat      -- 逐地块产出，索引即地块
  prodY    : List Nat
  upkeep   : Nat
  growthAt : Nat
  settlerCost : Nat
  popReq   : Nat
  foodCarry : Bool
  init     : State
  deriving DecidableEq, Repr
```

若 `Params` 含 `Nat → Nat` 字段（例如 `growthAtOf : Nat → Nat`），`DecidableEq`/`Repr` 立刻失效，
参数也无法序列化进报告。需要随人口变化的阈值时，用 `List Nat` 查表（`getD`），不要放函数。

### D3 谓词 Bool 优先

```lean
def Legal (p : Params) (s : State) (a : Nat) : Bool :=
  (a < 2 ^ p.tiles) && (workCount p a == s.pop)
```

Prop 版由 `abbrev LegalP p s a : Prop := Legal p s a = true` 派生。好处：`decide` 自动可用
（`Decidable` 实例永远存在），避免为每个谓词手写 `Decidable`；`Bool.and_eq_true` 让
「从合法性抽取算术事实」变成一行。

### D4 `State` 不许含函数/列表

一旦 `State` 含函数字段，`DecidableEq`、去重、`List.mem` 全部退化。所有需要的历史信息用
`Nat` 计数器编码（D9）。若将来必须记录「某地块已被改良」集合，用位掩码 `Nat`。

### D5 枚举完备性用「界放在 Legal 里」技巧（不需要 `Fintype`）

```lean
def allActions (p : Params) : List Nat := List.range (2 ^ p.tiles)

theorem mem_allActions {p : Params} {a : Nat} : a ∈ allActions p ↔ a < 2 ^ p.tiles
theorem legal_lt {p s a} (h : Legal p s a = true) : a < 2 ^ p.tiles   -- 从 && 左分量抽出
theorem legal_mem_allActions (h : Legal p s a = true) : a ∈ allActions p
```

完备性证明只有 3 行，因为**合法性自身携带了界**。这是整个架构最省力的地方：不需要
`Fintype`、不需要 `List.product`（core 里没有 `List.mem_product`）、不需要对函数做 `funext`。
代价：`Legal` 必须显式写出「动作码在范围内」这一条——它本身就是对「没有多余动作」的检查。

### D6 逐层去重，**禁止**跨层去重

```lean
def succsOf (p : Params) (s : State) : List State :=
  ((allActions p).filter (fun a => Legal p s a)).map (step p s)

def nextLayer (p : Params) (ss : List State) : List State :=
  dedupAux [] (ss.flatMap (succsOf p))

def layer (p : Params) : Nat → List State
  | 0 => [p.init]
  | n+1 => nextLayer p (layer p n)
```

层集合**不是**单调的，因此「全局 visited 集合」不健全。实测：合成场景 `big` 在 t=12 有 247 个状态，
其中 **234 个也出现在 t=13**——重复极多，诱惑很大；但若把 t+1 层的 `s` 因为「t 层见过」而删掉，
`t+2` 层就会失去 `s` 在 t+1 时刻的后继（后继属于 `t+2` 层，不会由 t 层的 `s` 产生）。详见 P1。

### D7 自写 `dedupAux`（core 里没有成员引理）

core 有 `List.eraseDups`（`Init/Data/List/Basic.lean:2189`）和 `eraseDups_cons`，
但**没有** `List.mem_eraseDups`；`grind` 也证不出来（实测失败，因为它需要归纳）。
自写 15 行的结构化递归版本，配两个引理（55 行，实测通过）：

```lean
def dedupAux [DecidableEq α] (seen : List α) : List α → List α
  | [] => []
  | a :: t => if a ∈ seen then dedupAux seen t else a :: dedupAux (a :: seen) t

theorem mem_dedupAux [DecidableEq α] (l seen : List α) (a : α) :
    a ∈ dedupAux seen l ↔ (a ∈ l ∧ ¬ a ∈ seen)
theorem mem_dedup [DecidableEq α] {l : List α} {a : α} : a ∈ dedupAux [] l ↔ a ∈ l
```

关键点：`seen` 累加器使递归**结构化**（`l` 变短），于是普通 `induction l` 够用；
若写成 `a :: (t.filter (· ≠ a)).dedup` 这种形式，就必须用 `termination_by length` 加
良基归纳（更贵，且 `dedup.induct` 名字在 4.25 里不可直接用——实测）。

### D8 规格与实现分离

```lean
inductive ReachableAt (p : Params) : Nat → State → Prop where
  | zero : ReachableAt p 0 p.init
  | succ {n s a} : ReachableAt p n s → Legal p s a = true → ReachableAt p (n+1) (step p s a)

theorem reachable_iff_mem {p n s} : ReachableAt p n s ↔ s ∈ layer p n   -- 双向，实测通过
```

`→` 方向（完备性）是 `layer` 不漏解的核心保证；`←` 方向（可靠性）是「层里没有伪造状态」的保证。
两个方向都必须证，且将来换实现（例如 §6 的 `Nat` 编码去重加速）时，**这条定理就是审计点**：
它证不过去就说明优化丢了解。

### D9 完成历史单调

```lean
def goalB (s : State) : Bool := s.done ≥ 1
abbrev Goal (s : State) : Prop := goalB s = true

theorem done_mono (p s a) : s.done ≤ (step p s a).done            -- 实测
theorem goal_stable (p s a) : Goal s → Goal (step p s a)          -- 实测
```

`Goal` 只依赖 `done`，不依赖 `prod` 或队列，因此「完成了移民又开始造别的」不会丢证据（C1）。
`done_mono` 用 `dsimp only [step]; split <;> omega`（注意：`simp only [step]` 展不开带 `let` 的项）。

### D10 时间索引显式化

内部时序：`t = 0` 是初态，`t = k` 是结算 k 次之后（PLAN §2.1）。
UI 回合号用独立函数表达，不要直接混用：

```lean
def uiTurn (offset t : Nat) : Nat := t + offset   -- offset 由 M0 核实后填入 scenario 元数据
```

`NoEarlier p N` 是 `∀ t, t < N → …`（严格小于），`AchievableAt p N` 是「恰好 N 步」。
两者只有在**同一个结算顺序**下才有意义，见 P5。

---

## 4. 证书与定理形状

### 4.1 见证（证书 A）

```lean
def legalPathB (p : Params) : State → List Nat → Bool
  | _, [] => true
  | s, a :: t => Legal p s a && legalPathB p (step p s a) t
abbrev LegalPath (p) (s) (tr) : Prop := legalPathB p s tr = true

def run (p : Params) : List Nat → State → State
  | [], s => s
  | a :: t, s => run p t (step p s a)

def AchievableAt (p : Params) (N : Nat) : Prop :=
  ∃ tr, tr.length = N ∧ LegalPath p p.init tr ∧ goalB (run p tr p.init) = true
```

`LegalPath` 必须是 **`abbrev`**（不是 `def`），否则 `Decidable` 合成不会展开它，`by decide` 直接失败
（实测踩过）。见证证明一律是 `⟨[具体动作表], rfl, by decide, by decide⟩`，代价线性于 N。

### 4.2 下界（证书 B）

```lean
def NoEarlier (p : Params) (N : Nat) : Prop :=
  ∀ n, n < N → ∀ s, ReachableAt p n s → ¬ Goal s

def checkNoEarlier (p : Params) (N : Nat) : Bool :=
  (List.range N).all (fun n => (layer p n).all (fun s => !goalB s))

theorem noEarlier_of_check (h : checkNoEarlier p N = true) : NoEarlier p N        -- 实测
theorem check_false_imp_exists_goal (h : checkNoEarlier p N = false) :
    ∃ n, n < N ∧ ∃ s, ReachableAt p n s ∧ Goal s                                  -- 实测
```

第一条是证书可靠性；第二条是「检查器不会虚报」——它使**篡改测试**（把 N 调小必然失败）
成为真定理而不是口号。

### 4.3 组合

```lean
def OptimalAt (p : Params) (N : Nat) : Prop := AchievableAt p N ∧ NoEarlier p N

theorem achievable_imp_reachable (h : AchievableAt p N) : ∃ s, ReachableAt p N s ∧ Goal s  -- 实测
theorem reachable_run : ReachableAt p n s → LegalPath p s tr → ReachableAt p (n + tr.length) (run p tr s)
```

`OptimalAt` 的 `NoEarlier` 与 `AchievableAt` 若使用**不同**结算顺序或不同 `N` 语义，
结论就毫无意义；因此 `OptimalAt` 的参数里不要塞 `Params` 之外的开关，`N` 保持为定理参数（便于篡改测试）。

### 4.4 `NoEarlier` 的三种实现档位

| 档 | 手段 | 内核信任 | 实测代价（合成 `big`，6 地块，~10³ 状态/层） |
|----|------|----------|--------------------------------------------|
| A | `by decide`（整个层枚举在内核里算） | 只有内核 | N=12: **3m04s**；N=16: **14m17s** |
| B | `by native_decide` | +`Lean.ofReduceBool`, `Lean.trustCompiler` | N=12: 1.2s；N=16: 1.8s；N=24: 9.5s |
| C | 外部生成每层字面量表 + 每层 `rfl`/`decide` 校验 | 同 A（若全 `decide`） | 未实测；见下 |

> 口径：上表 (A)(B) 两列的绝对秒数来自 §11 附录 A 的独立引擎；在同一模型跑仓库 `Finite.lean` 时
> （`legalActions` 每状态重算 + 两段式去重），A 档 N=12 为 **7m47s**、B 档 N=24 为 **17.8s**，
> 档位差距结论不变。详见 §10 与 §13。

**结论（重要）**：A/B 在同一命题上相差约 **475×**（独立引擎 N=16 同题对比）。真实 Civ6 开局（N≈30–40、每层 10³–10⁴ 状态）
下 A 档不可行。B 档可行但必须在报告里明写信任依赖（C5）。C 档的价值不是渐近加速
（`Lit_{t+1} = nextLayer p Lit_t` 仍需完整算一遍映像），而是：分文件 `.olean` 缓存、按层并行、
峰值内存降低、失败定位到具体层。C 档的检查器必须同时校验「每层覆盖」与「无目标」，
不能只校验证书里出现的边（PLAN §4）。

### 4.5 公理审计（必须进 CI）

实测公理依赖：

```text
# A 档（decide）        : [propext, Quot.sound]
# B 档（native_decide） : [propext, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
# 出错未修（真·事故）    : [propext, sorryAx, Quot.sound]
```

第三条不是假想：本设计的实测过程中，`by decide` 因 **`maximum recursion depth`** 失败，
Lean 报错后定理仍被 `sorry` 补上，`#print axioms` 里才看到 `sorryAx`。因此
`Checks/Axioms.lean` 必须对**每个对外定理**跑 `#print axioms`，CI 里 grep 拒绝 `sorryAx`
与未经批准的 `Lean.ofReduceBool`/`Lean.trustCompiler`。

---

## 5. 证明策略与工作量分解

引擎全部定理（实测 262 行、单文件编译 <1s）的引理清单：

| 定理 | 作用 | 证明手段 | 估计行数 |
|------|------|----------|---------|
| `mem_dedupAux_notMem` | 去重不吐出已见元素 | `induction l` + `if_pos/if_neg` | 15 |
| `mem_dedupAux` | 去重保集合（带 seen） | 同上 + `by_cases a = b` | 30 |
| `mem_dedup` | 去重保集合 | 上两条 | 5 |
| `legal_lt` / `legal_mem_allActions` | 枚举完备（C2） | `Bool.and_eq_true` + `List.mem_range` | 6 |
| `mem_succsOf` | 单状态后继刻画 | `List.mem_map`/`mem_filter` | 8 |
| `reachable_imp_mem` | **完备性**（不漏解） | `ReachableAt` 归纳 + `mem_dedup`+`mem_flatMap` | 12 |
| `mem_imp_reachable` | **可靠性**（不造假） | `Nat` 归纳 + `mem_dedup` + `mem_succsOf` | 14 |
| `noEarlier_of_check` | 证书 B 可靠 | `List.all_eq_true` ×2 + 等价定理 | 10 |
| `check_false_imp_exists_goal` | 检查器不虚报 | `List.all_eq_false` ×2 + 可靠性 | 14 |
| `done_mono` / `goal_stable` | C1 | `dsimp only [step]; split <;> omega` | 6 |
| `reachable_run` | 见证 ⇒ 可达 | `List` 归纳 + 加法交换 | 12 |
| `achievable_imp_reachable` | `AchievableAt ⇒ ∃ Goal 状态` | 上一条 | 6 |

**策略要点**：
1. **不对 `step` 的内部算术建理论**。`step` 的所有性质都用 `decide` 在具体参数上验证；
   唯一需要「一般性」的是 `done_mono`（因为 `Goal` 的单调性是语义要求，不是数值巧合）。
   这样把证明负担压在**框架**（枚举/去重/覆盖）而不是规则语义上，正好对应「规则未核实」的现实。
2. 想让 `decide` 真的能跑，`step` 必须可归约：不要用 `String`、不要用 `Decidable` 的复杂实例。
   带 `autoParam` 的函数（如 `List.mergeSort`）在 `#eval` 里没问题，但它们在**内核 `decide`
   路径上的归约行为未经验证**——不要放进 `step`，只用在 `#eval` 侧的搜索/报告工具里。
3. `omega` 是 core 的，覆盖所有 `Nat` 线性算术；`n - k` 的截断语义由 `omega` 正确处理，
   但**不要让模型语义依赖截断**（P4）。

---

## 6. 参数化规则：未核实公式的正确住址

### 6.1 参数清单与核实状态

| 参数 | 含义 | 状态 | 备注 |
|------|------|------|------|
| `tiles`, `foodY`, `prodY` | 地块与产出 | **未核实** | 需 build 号 + 游戏内截图/存档 |
| `upkeep` | 每 pop 每回合粮食消耗 | **未核实** | 可能随时代变 → 用 `List Nat` 查表 |
| `growthAt` | 增长所需粮食 | **未核实** | 很可能随 pop 变 → `growthAtOf : List Nat` |
| `settlerCost` | 移民生产力 | **未核实** | 受速度（标准/快速）影响 |
| `popReq` | 生产移民所需最低人口 | **未核实** | 若为 1，则增长完全不参与下界 |
| `settlerPopCost` | 完成时人口是否减少 | **未核实** | 合成模型**未**建模（见 §6.3） |
| `foodCarry` | 增长后是否保留溢出粮 | **未核实** | 影响同回合双事件 |
| `prodOverflow` | 完成时溢出生产力是否保留 | **未核实** | 合成模型取「丢弃」 |
| `starvation` | 粮食不足是否掉人口 | **未核实** | 合成模型取「只 clamp，不惩罚」 |
| `blockedProd` | 人口不足时生产力是否照常累积 | **未核实** | 合成模型取「照常累积」 |
| `order` | 生产/完成/吃饭/增长的顺序 | **未核实** | 影响 N 的奇偶偏移 |
| `minWork` | 是否必须给每个市民分配地块 | **未核实** | 影响 `Legal` |

**原则**：任何一条不写进 `Params`，而是硬编码进 `step` 的规则，都会在 M0 核实后被推翻，
届时必须改 `step` → 所有已证的 `decide` 结论全部作废。写进 `Params` 则只改 scenario 文件，
定理按 `rfl`/`decide` 重新实例化，引擎零改动。

`order` 建议做成枚举参数（`inductive Order | prodFirst | eatFirst`），并在 `step` 里对其
`match`；首版只证**一种**顺序，并在报告「模型适用边界」里显式声明选择，不要假装它与游戏一致。

### 6.2 场景条件（不属于公式，属于前提）

「宜居度/住房在证明区间内不改变计算」这类条件不能进 Lean 参数，必须以**文档前提**+**检查清单**
的形式记录：在 `Scenarios/*.lean` 顶部注释里列出，并在 `RULES.md` 里给出每条的游戏内验证方式。
Lean 只证明模型内的定理；模型与游戏的一致性永远是独立的验证工作（PLAN §2.3 末段）。

### 6.3 一个真实的「模型漏洞」示例（说明为什么必须披露）

合成场景 `big`（foodY `[3,2,2,1,0,0]`、prodY `[0,1,1,2,3,4]`、upkeep 2、growthAt 24、
settlerCost 30、popReq 2）实测最优 **N = 29**（见证：24 回合 mask 1 攒粮，随后 5 回合 mask 48 双生产地块）。
这个最优解之所以成立，是因为模型里**粮食耗尽只 clamp 到 0、不掉人口**：

```lean
let food2 := if eaten ≤ food1 then food1 - eaten else 0    -- 无饥饿惩罚
```

若真实规则是「缺粮掉人口」，同一开局的下界会完全不同。这不是证明的错误，而是
**模型—游戏一致性**的风险，必须在每份证书里写明当前 `starvation` 参数的取值与状态。
本文件的合成最优值**不能**作为任何游戏结论引用。

---

## 7. 陷阱清单

### P1 去重（最危险）

1. **跨层去重不健全**。`layer` 不是单调的：实测 t=12 的 247 个状态中 234 个在 t=13 复现。
   删掉 t+1 层里「t 层见过」的状态，会让 t+2 层失去它在 t+1 时刻的后继。
   唯一安全的跨层论证需要「存在 stutter 动作且 `step` 对它幂等」——本模型没有。
2. **状态必须包含全部影响未来的信息**。漏掉 `prod` 进度、`food`、`done`、或（若规则需要）
   「本回合是否已增长」标志，去重就会把不同未来合流。判据：`reachable_iff_mem` 的 `→` 方向证不过去。
3. **编码去重必须证往返**。若为了性能把 `State` 编码成 `Nat` 再解码去重（实测到 L24：
   11.4s → 8.0s，约 1.4×；见 P9 的口径说明），必须证 `dec_code : dec (code s) = s`；否则碰撞会**静默**丢掉状态，
   而 `reachable_imp_mem` 会因此证不出来——把这条定理当回归测试，而不是把 `decide` 当回归测试。
4. `List.eraseDups` 在 core 里没有成员引理，`grind` 也证不出（实测）。别在框架层用它。
5. 去重顺序影响 `layer` 的**列表内容**（进而影响 `decide` 的归约结果），但不影响集合语义。
   报告里的「逐层状态数」应当由 `(layer p t).length` 生成，不要手写。

### P2 危险剪枝

1. 枚举上界（`2 ^ tiles`、以及 §6 里各种「够用就行」的截断）必须来自**已证不变量**。
   合成模型里 `food` 无上界、`prod` 无上界（人口不足时照常累积），因此不能假设上界；
   一旦要设上界，必须证明「可达状态的 `food ≤ f_max`」这种引理，否则完备性直接破坏。
2. **支配剪枝**需要保序定理：「若 `s ⊑ s'` 则从 `s` 可达的目标从 `s'` 也可达」。注意反例方向：
   「粮多总是更好」是**假**的（粮多可能已经跨过增长阈值导致维护费上升、或导致不同的增长时机）。
   M3 首版不做任何支配剪枝（PLAN §5 明确要求）。
3. 「无用动作」不能在枚举里删。看起来无用的「不工作 / 只工作粮食地块」在
   `foodCarry = false` 的语义下可能是最优（避免溢出浪费）。删它等于删下界。

### P3 动作覆盖

1. `Legal` 只有一份定义，被 `step` 的调用方、枚举、Python 搜索器共用。任何「枚举时另写一份
   合法判断」都会制造不可见的覆盖漏洞。
2. 掩码高位：`a < 2 ^ tiles` 必须在 `Legal` 里（否则 `allActions` 之外的动作也能合法，
   完备性定理不成立）。
3. 动作空间随 `pop` 变化（`workCount = pop`），因此**同一 `a` 在不同状态合法性不同**——
   合法性的第二个分量必须真的依赖 `s`，否则 `legal_lt` 仍然成立但语义错了。
4. 重复动作（不同掩码、相同产出）**允许存在**：去重发生在状态层，不在动作层。
   若在动作层按产出等价类去重，需要「等价动作产生相同后继」的定理（首版不做）。
5. 若某些动作在游戏里根本不允许（例如人口 1 时同时工作两块地），这属于 `Legal` 的语义，
   必须由 M0 fixture 固定，而不是由「搜索器没生成」来默认。

### P4 `Nat` 减法

1. `a - b` 在 `a < b` 时**截断为 0**。模型的 `food2 := if eaten ≤ food1 then food1 - eaten else 0`
   是显式 clamp；若写成 `food1 - eaten` 则语义相同但**读起来像**允许负数，评审容易误判。
2. 不要把 `Nat` 与 `Int` 混用。需要「可能有负」的量（如净粮食）用 `Nat` + 显式分支，
   或 `Int` 但仅在 `step` 内部、绝不进 `State`（否则 `DecidableEq` 还在，但 `decide` 变慢且 lemma 变丑）。
3. 不为 `Nat` 除法建理论：M4 的下界写成 `settlerCost ≤ t * maxProdPerTurn` 形式，
   避免 `⌈c/p⌉` 与 `Nat.div` 的引理（core 有 `Nat.le_div_iff_mul_le` 一类，但用乘法形式更省）。
4. 所有线性算术交给 `omega`（core），不要手写 `Nat.sub_add_cancel` 链。

### P5 时间索引

1. 内部 `t=0` 是初态；游戏 UI 通常从「第 1 回合」开始显示。映射偏移必须作为
   scenario 元数据显式记录，并在报告里同时给出两种编号（PLAN §2.1 要求）。
2. **完成发生在回合内**：若生产在第 k 次结算内达标，则 `Goal` 在 `t=k` 的状态上为真。
   「回合结束时完成」与「下一回合开始时完成」会差 1，必须由 `order` 参数固定，
   并由 fixture F4（同回合完成+增长）钉死。
3. `NoEarlier` 用 **`t < N` 严格小于**；`AchievableAt` 用**恰好 N 步**。二者组合才推出
   「最早是第 N 回合」。写成 `≤ N` 会退化成无内容的定理。
4. 篡改测试：`¬ AchievableAt p (N-1)` 必须可证（用 `NoEarlier p N` + `achievable_imp_reachable` +
   `omega`，实测在合成场景上成立）。`AchievableAt p (N+1)` 一般也应可证（见证末尾补一个合法动作），
   若不能，说明 `Legal` 在目标态之后不再有合法动作——那本身是模型 bug。

### P6 递归深度与心跳（会静默产生 `sorryAx`）

实测：`by decide` 在 N=16 时先报 `maximum recursion depth has been reached`，
定理随即被 `sorry` 填充。必须：

```lean
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem … := …
```

并在 CI 里对每个定理 `#print axioms`，见到 `sorryAx` 直接失败。**不要**把「编译通过」
当成「证明成立」。

### P7 `native_decide` 的信任传递

实测公理差集：`+ Lean.ofReduceBool, Lean.trustCompiler`。这意味着「通过」依赖编译器正确性。
报告必须像下面这样披露，而不是笼统写「已形式化验证」：

```text
证书 B 的实现档位：native_decide
额外信任依赖：Lean.ofReduceBool（编译期求值结果可信）、Lean.trustCompiler
内核可复核替代方案：A 档（decide），在本场景需要约 X 小时 / 或缩小到 N′
```

### P8 隐藏历史依赖破坏 Markov 性

分层枚举隐含假设：`step` 只依赖 `(s, a)`。若将来加入「本回合已增长则不能再增长」「移民不能连续造」
这类规则，信息必须进 `State`（`Nat` 计数器/位掩码），否则 `reachable_iff_mem` 会是**假定理**
（能证出来只说明它在当前 `step` 定义下成立，而 `step` 定义已经错了）。

### P9 性能（实测数据）

| 实验（合成 `big`，6 地块） | 结果 |
|---|---|
| 层大小 | L12=247，L16=425，L20=651，L24=925 |
| 编译执行（`#eval`）算到 L24，朴素 O(n²) 去重 | 11.4s |
| 编译执行算到 L24，`Nat` 编码 + 排序去重 | 8.0s（≈1.4×，层大小完全一致） |
| 编译执行算到 L34（含 L30/L34 两次全量检查） | 75s |
| 内核 `decide` 证 `NoEarlier` N=12 / N=16 | 3m04s / 14m17s |
| `native_decide` 同命题 N=12 / N=16 / N=24 | 1.2s / 1.8s / 9.5s |

推论：先优化枚举器（编码去重、预计算每 `pop` 的候选动作表、避免每次 `2 ^ tiles` 重算），
再决定是否降级到 B 档；不要用「内核慢」当作跳过优化的理由。

### P10 其他

- `LegalPath`/`Goal` 必须是 `abbrev`，否则 `Decidable` 合成失败（实测）。
- `simp only [step]` 展不开带 `let` 的 `step`；用 `dsimp only [step]` 或 `unfold step`。
- 合取型 `Bool`（`&&`）的分解用 `Bool.and_eq_true`，不要用 `simp` 全展开（会把 `decide` 变成 `Prop` 等式）。
- core 缺失的引理（实测）：`List.mem_eraseDups`、`List.mem_product`、`List.mem_finRange`、
  `Nat.strong_induction_on`（用 `Nat.strongRecOn`）。设计时不要假设它们存在。

---

## 8. 推荐的首个可实现里程碑

### M1-min（1–2 天，纯合成，不触碰游戏数据）

目标：**一个 262 行的引擎 + 一个合成场景，端到端跑通 `OptimalAt`**，全部用 core Lean。
本文件 §4 的所有签名已实测通过，照抄即可；`#print axioms` 只剩 `propext, Quot.sound`。

验收标准：
1. `theorem synth_optimal : OptimalAt synth 2`（2 地块、cost 4、prod 2/回合）。
2. `theorem synth_not_1 : ¬ AchievableAt synth 1`（篡改测试）。
3. 10 条 fixture（§9）全部以 `example ... := by decide` 的形式写进 `Scenarios/Synthetic.lean`。
4. `Checks/Axioms.lean` 全绿；CI 拒绝 `sorryAx`。
5. 报告模板能输出逐回合表（`#eval` 生成，不手写）。

### M1-real（M0 完成后 0.5 天）

只替换 `Scenarios/Candidate.lean` 里的 `Params` 数值 + 在 `RULES.md` 里逐字段登记证据来源。
引擎零改动。若某条规则无法核实，就把它保留为参数并在报告里标注「未核实，取值 X；结论对该取值成立」。

### M3-scale（关键决策点）

按 §4.4 做档位选择：
- 若真实场景 N ≤ 15 且层大小 ≤ 300：用 A 档（全内核，最强结论）。
- 否则默认 B 档 + 披露，同时做 C 档（分层字面量证书）作为可选强化。
- 若连 B 档都超预算：**缩小场景**（减少地块数、缩短期限、或明确「受限建造集合」），
  不能悄悄删动作（PLAN §6）。

---

## 9. 测试夹具（合成，明确非游戏证据）

`fixtures/SYNTHETIC/FIXTURES.md` 首行必须写：
> 这些夹具编码的是**本设计模型**的语义，不是 Civilization VI 的事实。任何一条都不构成游戏证据。

基准场景 `synth = { tiles:=2, foodY:=[2,0], prodY:=[0,2], upkeep:=1, growthAt:=4,
settlerCost:=4, popReq:=1, foodCarry:=false, init:=⟨1,0,0,0⟩ }`。
下列期望值均已实测：

| # | 输入 | 期望 | 覆盖点 |
|---|------|------|--------|
| F1 | `step synth ⟨1,2,0,0⟩ 1`（粮地块） | `⟨1,3,0,0⟩` | 增长阈值**未**达到（2+2−1=3 < 4） |
| F2 | `step synth ⟨1,3,0,0⟩ 1` | `⟨2,0,0,0⟩` | 恰好达到阈值（3+2−1=4 ≥ 4）→ 增长、无溢出保留 |
| F3 | `step synth ⟨1,2,2,0⟩ 2`（生产地块） | `⟨1,1,0,1⟩` | 恰好完工（2+2=4 ≥ 4）→ `done+1`、进度清零 |
| F4 | `step synth ⟨2,3,2,0⟩ 1`（人口 2，粮地块） | `⟨2,3,2,0⟩`（粮 +2 被 upkeep 2 抵消） | 维护费随 `pop` 缩放 |
| F4b | `mix := {tiles:=3, foodY:=[2,0,2], prodY:=[0,2,1], upkeep:=1, growthAt:=4, settlerCost:=4, popReq:=1, foodCarry:=false, init:=⟨2,3,3,0⟩}`，`step mix ⟨2,3,3,0⟩ 5`（mask 5 = 地块 0+2，粮 4 产 1） | `⟨3,0,0,1⟩`（prod 3+1=4 完工清零；粮 7−2=5 ≥ 4 增长） | **同回合双事件**，`order` 可观测（唯一能同时产粮与产锤的混合地块场景） |
| F5 | `step synth ⟨1,0,0,0⟩ 2` | `⟨1,0,2,0⟩` | 缺粮 clamp 到 0，不做负数 |
| F6 | `Legal synth ⟨1,0,0,0⟩ 3`；`Legal synth ⟨1,0,0,0⟩ 4`；`Legal synth ⟨2,0,0,0⟩ 1` | `false,false,false` | 市民数不符 / 掩码越界 / 人口不符 |
| F7 | `layer synth 0/1/2/3` 的元素个数 | `1, 2, 4, 6` | 去重后层大小（实测） |
| F8 | `(layer big 12).length` | 247 | 规模回归（层大小变化 = 语义漂移） |
| F9 | `checkNoEarlier synth 2` / `synth 1`；`checkNoEarlier big 29` / `big 30` | `true/true`、`true/false` | 边界：N=29 可行、N=30 已含目标 |
| F10 | `#print axioms synth_optimal` | 无 `sorryAx` | 公理审计 |

真实游戏夹具（`fixtures/GAME/`）在 M0 前**保持为空**，只放一个 `PENDING.md` 说明需要什么证据
（build 号、速度、文明、初态地块与产出、逐回合人口/储粮/生产）。不要把合成数据伪装成游戏数据。
真实夹具到位后，必须与合成夹具**分开目录、分开标注、分开 CI 任务**，避免混用。

---

## 10. 实测证据表（2026-10-17，Lean 4.25.0，NixOS）

两组测量：**(a)** 本文件 §11 附录 A 的独立最小引擎（`/tmp` 内，仅用于验证设计可行性）；
**(b)** 仓库现有 `Civ6Verify/Reachability/Finite.lean` + 一个 6 地块合成模型
（`scripts/lean-env lake env lean`，与项目工具链一致）。

```text
工具链          lean4-4.25.0：项目 .tools + scripts/lean-env（主）；nixpkgs lean4-4.25.0（同版本，交叉验证）
引擎规模        (a) 262 行；单文件编译 <1s（252 行版本实测 0.46s）；(b) Finite.lean 673 行，lake build ~2s
已验证定理      mem_dedup, legal_mem_allActions, reachable_iff_mem（双向）,
                noEarlier_of_check, check_false_imp_exists_goal,
                done_mono, goal_stable, reachable_run, achievable_imp_reachable
端到端          (a) 合成 big：OptimalAt big 29（见证 24×mask1 + 5×mask48），
                ¬ AchievableAt big 28（篡改测试），native_decide 46s
                (b) 同一 big 模型跑在 Finite.lean 上：Frontier 层大小与 (a) **逐项一致**
                    （L1=5, L2=12, L3=22, …, L12=247）；witnessAt model goalB 29 = some ⟨2,0,0,1⟩
                (b) 内核 decide 证 NoEarlier N=12：**7m47s**（该次运行同时含一个 native_decide 定理，约 +18s）；
                (b) 单独 native_decide 证 NoEarlier N=24：**17.8s**
公理            decide 档 [propext, Quot.sound]；native_decide 档 +[Lean.ofReduceBool, Lean.trustCompiler]
已知失败模式    ① core 无 List.mem_eraseDups（grind 证不出）；
                ② maxRecDepth 默认 1000 → decide 失败并留下 sorryAx；
                ③ List.mem_product / List.mem_finRange / Nat.strong_induction_on 不存在；
                ④ simp only [step] 展不开 let 链，需 dsimp only
```

---

## 11. 附录 A：已验证的核心签名（可直接照抄）

```lean
structure State where
  pop  : Nat
  food : Nat
  prod : Nat
  done : Nat
  deriving DecidableEq, Repr

structure Params where
  tiles : Nat
  foodY prodY : List Nat
  upkeep growthAt settlerCost popReq : Nat
  foodCarry : Bool
  init : State
  deriving DecidableEq, Repr

def Legal (p : Params) (s : State) (a : Nat) : Bool
def step  (p : Params) (s : State) (a : Nat) : State
def allActions (p : Params) : List Nat := List.range (2 ^ p.tiles)
def succsOf (p : Params) (s : State) : List State
def nextLayer (p : Params) (ss : List State) : List State
def layer (p : Params) : Nat → List State

inductive ReachableAt (p : Params) : Nat → State → Prop
  | zero : ReachableAt p 0 p.init
  | succ {n s a} : ReachableAt p n s → Legal p s a = true → ReachableAt p (n+1) (step p s a)
theorem reachable_iff_mem : ReachableAt p n s ↔ s ∈ layer p n

def goalB (s : State) : Bool := s.done ≥ 1
abbrev Goal (s : State) : Prop := goalB s = true
def NoEarlier (p : Params) (N : Nat) : Prop
def checkNoEarlier (p : Params) (N : Nat) : Bool

abbrev LegalPath (p : Params) (s : State) (tr : List Nat) : Prop
def run (p : Params) : List Nat → State → State
def AchievableAt (p : Params) (N : Nat) : Prop
def OptimalAt  (p : Params) (N : Nat) : Prop
```

## 12. 附录 B：待议事项（需要用户/项目决策）

1. `order` 首版固定为哪一种结算顺序？建议 `prodFirst`（生产→完工→吃饭→增长），
   理由是它让「同回合完工」的观测点在 `t=k` 而不是 `k+1`，减少一次解释成本。
2. `N` 是否允许写进 `Scenarios/*` 作为 `def`？建议**不允许**：`N` 只作定理参数，
   便于 `N-1`/`N+1` 篡改测试直接可写。
3. 是否接受 B 档（`native_decide`）作为 M3 的默认交付？若不可接受，须在 M3 前先做 §13.2 R3 的
   枚举器优化 + 场景缩小，或者把 M4 的数学下界提前。
4. `search/` 的 Python 生成器是否允许生成「层字面量表」输入 Lean（C 档）？
   若允许，Lean 侧必须校验每层覆盖与无目标，不能只信 Python。

---

## 13. 与仓库现有 `Civ6Verify/Reachability/Finite.lean` 的对接与评审

写本文件时仓库里**已经存在**一个 673 行的通用核心（`Model` 类 + `Reachable` + `Frontier`
+ `mem_frontier_iff` + `checkNoGoalBelow` + `witnessAt` + `checkCertificate` +
`earliestGoalTick?`），`lake build` 通过，公理只有 `propext`/`Quot.sound`。
因此 §3–§5 的大部分内容**已在仓库落地**，本文件的增量是：未核实规则的参数化纪律（§6）、
陷阱清单（§7）、实测规模数据（§10）与里程碑（§8）。

### 13.1 交叉验证（有用，但不是游戏一致性证据）

我用一个**独立重写**的 262 行引擎跑同一个合成模型 `big`，得到的逐层状态数与 `Finite.lean`
完全一致（L1=5, L2=12, L3=22, L4=35, …, L12=247）。这说明两份实现没有分叉，
但它只证明「两个实现对同一个模型一致」，**不**证明模型与游戏一致（PLAN §6 已明确）。
`Finite.lean` 上同一模型的 `witnessAt model goalB 29 = some ⟨2,0,0,1⟩`，与 §6.3 的手算一致。

### 13.2 评审建议（按优先级）

**R1（高）`legalActions_complete` 是整个下界唯一的单点失效位置。**
`Model` 把它作为场景必须手写的义务，正确但容易被「漏写一个动作」悄悄削弱。
两种改进：
1. 通用枚举 + 界在合法性里（本文件 D5）：`allActions := List.range (2 ^ tiles)`，
   完整性证明退化为 `a < 2 ^ tiles`（实测 3 行）。代价是枚举比「按状态裁剪」大。
2. 保留现状，但给每个场景加一个**自动差异化夹具**：对 `Frontier` 里抽样的每个状态，
   `#eval` 断言 `(List.range bound).filter legalB == legalActions s`；不一致即失败。
   这不能替代证明，但能把「漏动作」从静默变成红灯。

**R2（高）`legal : Prop` + `legalDec` 字段让每个场景手写 `Decidable`。**
建议加一个 Bool 优先的入口：`legalB : State → Action → Bool`，
`legal s a := legalB s a = true`，`legalDec := inferInstance`。
实测经验：`Decidable` 合成**不会**展开 `def`，必须用 `abbrev`（否则 `by decide` 直接失败）；
Bool 优先能消掉这类摩擦，并让 `Bool.and_eq_true` 成为抽取算术事实的标准手段。

**R3（中）`dedup` 是 O(n²)。**
同一模型下把去重换成「`Nat` 编码 + 排序 + `eraseReps`」实测到 L24 只快 **1.4×**（11.4s → 8.0s），
层大小不变：在 ~10³ 状态/层时瓶颈是 `step` 求值而不是去重；`O(n²)` 要到 ~10⁴ 状态/层才会主导
（**推断，未实测**，10⁴ 层规模下应先测再优化）。前提是必须证 `dec (code s) = s`（以及 `code` 在层内码上的往返），
否则碰撞会静默丢状态；`mem_frontier_iff` 的完备性方向就是这条优化的回归测试。

**R4（中）不要在 `Frontier` 上加「跨层 visited」。**
`Frontier` 目前每层独立，这是**正确**的。若要加速而引入全局 visited，会破坏
`mem_frontier_iff`（实测同一模型相邻层重复率约 234/247，诱惑很大，见 P1）。

**R5（中）`decide` 档的规模红线已实测。**
在 `Finite.lean` + 6 地块合成模型上，内核 `decide` 证 `NoEarlier 12` 需 **7m47s**，
`native_decide` 证 `NoEarlier 24` 需 **17.8s**（该次 decide 运行里另有一个 native_decide 定理，故 7m47s 中约 18s 属于它）。真实 Civ6 期限（N≈30–40）必须走
`native_decide` 或分层字面量证书（§4.4 C 档），并在报告里披露公理差集（§4.5）。
另：`decide` 前需 `set_option maxRecDepth 1000000`，否则会因默认 1000 的深度限制
**静默留下 `sorryAx`**（P6）。

**R6（低）`checkCertificate` 只回 `Bool`，报告必须标明档位。**
建议在 `Checks/Axioms.lean` 对每个对外交付的定理逐一 `#print axioms`，
把 `Lean.ofReduceBool`/`Lean.trustCompiler` 的出现当作「需在报告中披露」的触发器。

**R7（低）`earliestGoalTick?` 只是扫描，不是最优性证明。**
对外只应交付 `optimalAt_of_earliestGoalTick?` 或 `optimalAt_of_checkCertificate` 的结论，
不要交付「扫描得到的 N」这个数值本身。

### 13.3 仓库还缺的东西（本文件主张补上的部分）

1. 未核实规则的**参数化纪律**（§6）：`order`、`starvation`、`blockedProd`、`foodCarry`、
   `prodOverflow`、`settlerPopCost`、`minWork` 目前都没有显式位置。
2. UI 回合号与内部 `t` 的映射（§4 D10 / P5）。
3. 合成夹具与游戏夹具的**目录与 CI 分离**（§9）。
4. 规模决策点（§8 M3-scale）与公理档位的报告模板（§4.5）。

### 13.4 工具链备注

本节 (b) 组测量全部用 `scripts/lean-env lake env lean`（项目 `.tools/lean-4.25.0-linux`）。
另外：本轮为验证设计，用 `nix build nixpkgs#lean4` 把
`/nix/store/rd2b216icg666mii82gdbs6fpvhvm39m-lean4-4.25.0` 从「部分下载」补齐为可用
（`lean --version` 正常），因此 `research/TOOLCHAIN.md` 中「该 store 路径损坏」的记述已过时；
项目主工具链不受影响，仍应一律使用 `.tools/` + `scripts/lean-env`。
