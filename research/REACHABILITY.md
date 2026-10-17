# REACHABILITY.md — 通用有限期可达性 / 最优性核心

> 归属：本文件与 `Civ6Verify/Reachability/Finite.lean` 是本轮的唯一产物。
> 未修改根模块 `Civ6Verify.lean`、`Main.lean`、`lakefile.toml` 或其他任何智能体文件。
> 状态：**已实现，Lean 4.25.0 内核检查通过**；无 Mathlib、无 `sorry`、无自定义公理、无 `native_decide`。
> 范围：**不包含任何《文明 VI》规则或数值**。这是让场景模块（例如 `research/SYNTHETIC.md` 的合成 Tiny City v0）实例化并证明“第 N tick 首次达成目标”的通用引擎。

---

## 0. TL;DR

`Civ6Verify/Reachability/Finite.lean` 提供一个以 `Model` 类为输入的有限期证明核心：

- 精确步（exactly-`t`）归纳可达性 `Reachable`；
- 可计算的逐层状态集合 `Frontier`，并证明
  `s ∈ Frontier M t ↔ Reachable M t s`（双向，完备性依赖动作枚举的 `legalActions_complete`）；
- `AchievableAt` / `NoEarlier` / `OptimalAt`；
- 单个布尔检查 `checkCertificate M goalB N`，通过即得
  `OptimalAt M goal N`（把“第 N tick 可达”与“所有 t < N 都不可达”一次证完）；
- 可选择用 `earliestGoalTick?` 扫描最早层，或用 `witnessAt` 找见证；
- 见证路径 API：`LegalPath` + `run`，可直接把 Python 搜索器给出的动作序列重放成 Lean 证明；
- `NoEarlier` 明确等价于“**所有**合法动作序列（长度 < N）都失败”，不是只覆盖搜索器碰巧展开的边。

合成场景的推荐最短路径：

```lean
theorem optimal_at_five : OptimalAt model goal 5 :=
  optimalAt_of_checkCertificate goalB goalB_spec (by decide)

-- 等价的“分离形式”：分别给出下方无目标和第 5 层见证
theorem optimal_at_five_split : OptimalAt model goal 5 :=
  optimalAt_of_noGoalBelow_and_witness goalB goalB_spec
    (by decide) (List.any_eq_true.mp (by decide))
```

其中 `goalB_spec : ∀ s, goalB s = true ↔ goal s` 是唯一的“布尔目标 = 命题目标”桥接证明。

---

## 1. 构建与验证命令

所有命令在 `<project-root>` 下执行，使用项目本地工具链：

```bash
# 直接检查本核心文件（不依赖 lake 的模块图）
scripts/lean-env lake env lean Civ6Verify/Reachability/Finite.lean

# 构建 olean，供其他模块 import
scripts/lean-env lake build Civ6Verify.Reachability.Finite

# 场景文件（例如合成 v0）：先构建核心，再用同一 LEAN_PATH 检查
scripts/lean-env lake build Civ6Verify.Reachability.Finite
scripts/lean-env lake env lean Civ6Verify/Scenarios/Synthetic.lean

# 或者场景模块在 Civ6Verify/ 下时，直接让 lake 构建该模块
scripts/lean-env lake build Civ6Verify.Scenarios.Synthetic
```

注意：

- 根模块 `Civ6Verify.lean` 没有 import 本文件（按任务约束未改动根模块），所以单独跑 `scripts/lean-env lake build` 不会检查本文件；请使用上面的精确命令。
- `scripts/lean-env lake env lean <file>` 使用 Lean 内核归约，不是 `native_decide`。
- 本文件末尾内置了 `#print axioms` 审计；直接检查时会打印信任依赖（见 §6）。

实测（2026-10-17，Lean 4.25.0）：

```text
scripts/lean-env lake build Civ6Verify.Reachability.Finite
→ Built Civ6Verify.Reachability.Finite (约 0.7 s)
→ Build completed successfully
```

---

## 2. 语义约定

### 2.1 时间

与 `PLAN.md` §2.1 一致：

- `t = 0` 是场景初态 `M.init`；
- `t = k` 是恰好完成 `k` 次回合结算后的状态；
- `Reachable M t s` 是**恰好 t 步**，不是“≤ t 步”；
- `NoEarlier M goal N` 量化 `t < N` 的全部精确步可达状态；
- `AchievableAt M goal N` 只问 `t = N` 是否有目标状态；
- 若场景目标是单调历史标记（例如 `done ≥ 1`），`OptimalAt M goal N` 就是“最早完成 tick 为 N”的严格陈述。

### 2.2 合法性与动作枚举

`Model` 把“权威合法性”和“可计算枚举”分开：

```lean
class Model (State : Type u) (Action : Type v) where
  init : State
  step : State → Action → State
  legal : State → Action → Prop
  legalDec : (s : State) → (a : Action) → Decidable (legal s a)
  legalActions : State → List Action
  legalActions_sound : ∀ s a, a ∈ legalActions s → legal s a
  legalActions_complete : ∀ s a, legal s a → a ∈ legalActions s
```

- `Reachable` / `Frontier` 只使用 `legal` 动作；`Frontier` 通过 `legalActions` 枚举，但由 `legalActions_sound` 保证不会引入非法动作。
- `legalActions_complete` 是下界正确性的关键：如果场景漏掉一个合法动作，`mem_frontier_iff` 的后向方向就无法证明，`NoEarlier` 也不能从 frontier 检查推出。**漏动作不是“简化”，而是必须证明的（通常为假的）义务。**
- `legal` 必须是**独立**的规则谓词；不要把 `legal s a` 直接定义成 `a ∈ legalActions s` 来让 `_sound` / `_complete` 退化成 `rfl`。那样枚举就没有独立语义，模型审查会退化为“枚举自己证明自己”。正确做法是：先写规则谓词（及其 `Decidable`），再写枚举，然后证明两者互相覆盖。
- `step` 是全函数。非法输入可以返回任意值（例如原状态）；所有定理只对 `legal` 动作量化，因此全函数化不会引入“非法动作可达”的漏洞。不要在定理里直接对 `step` 量化而不带 `legal`。
- `legalDec` 被注册为低优先级 `Decidable (Model.legal s a)` 实例，场景可以用 `by decide` 关闭 `legal` 子目标，也可以覆盖更高效的判定过程。

### 2.3 目标谓词

本核心不强制目标是单调的；它只证明“在 `N` 首次可达”这一性质。场景应自行保证：

- `goal : State → Prop` 是历史标记（一旦完成就保持），或至少语义上确实表示“目标事件已发生”；
- `goalB : State → Bool` 与 `goal` 有已证明的等价
  `hspec : ∀ s, goalB s = true ↔ goal s`；
- 不要用“当前队列里有部分进度”代替“已完成计数/历史标记”（PLAN.md §2.1）。

---

## 3. API 总览

命名空间：`Civ6Verify.Reachability`。以下省略 `{State Action}`、`[DecidableEq State]`、`[Model State Action]` 等隐式参数。

### 3.1 精确步可达性

```lean
inductive ReachableFrom (M : Model State Action) (start : State) : Nat → State → Prop
  | zero : ReachableFrom M start 0 start
  | succ : ReachableFrom M start t s → M.legal s a → ReachableFrom M start (t+1) (M.step s a)

abbrev Reachable (M : Model State Action) (t : Nat) (s : State) : Prop :=
  ReachableFrom M M.init t s
```

- `Reachable` 是 `ReachableFrom` 把起点固定为 `M.init` 的特例；构造子仍是精确步的 `zero` / `succ`。
- `ReachableFrom.head`：在路径前端插入一个合法动作。
- `ReachableFrom.trans`：`t₁` 步再 `t₂` 步 = `t₁ + t₂` 步。

### 3.2 动作序列见证

```lean
def run (M) : State → List Action → State
inductive LegalPath (M) : State → List Action → Prop
  | nil (s) : LegalPath M s []
  | cons : M.legal s a → LegalPath M (M.step s a) rest → LegalPath M s (a :: rest)

theorem reachable_iff_exists_legalPath :
  Reachable M t s ↔
    ∃ as, as.length = t ∧ run M M.init as = s ∧ LegalPath M M.init as

theorem AchievableAt.of_legalPath
    (hlen : as.length = N) (hpath : LegalPath M M.init as)
    (hgoal : goal (run M M.init as)) : AchievableAt M goal N
```

推荐见证格式：给出 `as : List Action`，逐条用 `LegalPath.cons` 证明合法，`run` 自动重放到最终状态。Python 搜索器只负责产生候选 `as`，不决定定理真假。

### 3.3 计算 frontier

```lean
def successors (M) (s : State) : List State :=
  (M.legalActions s).map (fun a => M.step s a)

def Frontier (M) : Nat → List State
  | 0 => [M.init]
  | t+1 => dedup ((Frontier M t).flatMap (successors M))

theorem mem_frontier_iff (t : Nat) (s : State) :
  s ∈ Frontier M t ↔ Reachable M t s
```

- `Frontier t` 是**恰好 t 步可达**的去重状态列表。
- `dedup` 只在**同一层内**去重；它**不**删除“在更早层已经出现过”的状态。这与 exact-step 语义一致：一个状态可以在 t=2 和 t=5 都可达，`Frontier 2` 与 `Frontier 5` 都可以包含它。
- 这与 BFS 的“最短距离层”不同：距离层会跨层删除重复状态。合成 v0 的 `research/SYNTHETIC.md` §9.5 专门区分了这两种口径；用本核心复现时应期待 exact-step 计数，而不是距离层计数。
- `mem_frontier_iff` 的前向方向把 `Frontier` 成员转成 `Reachable`；后向方向使用 `legalActions_complete`，确保每个合法后继都在枚举中。

### 3.4 目标与最优性

```lean
def AchievableAt (M) (goal : State → Prop) (N : Nat) : Prop :=
  ∃ s, Reachable M N s ∧ goal s

def NoEarlier (M) (goal : State → Prop) (N : Nat) : Prop :=
  ∀ t, t < N → ∀ s, Reachable M t s → ¬ goal s

def OptimalAt (M) (goal : State → Prop) (N : Nat) : Prop :=
  AchievableAt M goal N ∧ NoEarlier M goal N

theorem AchievableAt.of_mem_frontier (hs : s ∈ Frontier M N) (hg : goal s) :
  AchievableAt M goal N

theorem OptimalAt.not_achievable_before (h : OptimalAt M goal N) :
  ∀ t, t < N → ¬ AchievableAt M goal t

theorem NoEarlier.mono (hNN' : N ≤ N') (h : NoEarlier M goal N') :
  NoEarlier M goal N
```

关键联系：

```lean
theorem noEarlier_iff_all_legalPaths :
  NoEarlier M goal N ↔
    ∀ as, as.length < N → LegalPath M M.init as → ¬ goal (run M M.init as)
```

这条定理把“frontier 里没有目标”翻译成“**所有**合法动作序列都失败”。因此下界覆盖全部 `legal` 动作，而不是只覆盖某次搜索展开的边。

### 3.5 可执行检查器

```lean
def checkNoGoalBelow (M) (goalB : State → Bool) (N : Nat) : Bool
def checkCertificate (M) (goalB : State → Bool) (N : Nat) : Bool :=
  checkNoGoalBelow M goalB N && (Frontier M N).any goalB

theorem checkNoGoalBelow_eq_true_iff :
  checkNoGoalBelow M goalB N = true ↔
    ∀ t, t < N → ∀ s ∈ Frontier M t, goalB s = false

theorem noEarlier_of_checkNoGoalBelow
    (hspec : ∀ s, goalB s = true ↔ goal s)
    (h : checkNoGoalBelow M goalB N = true) : NoEarlier M goal N

theorem optimalAt_of_checkCertificate
    (hspec : ∀ s, goalB s = true ↔ goal s)
    (h : checkCertificate M goalB N = true) : OptimalAt M goal N

theorem optimalAt_of_noGoalBelow_and_witness
    (hspec : ∀ s, goalB s = true ↔ goal s)
    (hbelow : checkNoGoalBelow M goalB N = true)
    (hwit : ∃ s, s ∈ Frontier M N ∧ goalB s = true) : OptimalAt M goal N
```

`checkCertificate` 是推荐的主证书接口：一次布尔归约同时检查“下方无目标”和“第 N 层有目标”。

### 3.6 扫描与见证辅助

```lean
def witnessAt (M) (goalB : State → Bool) (N : Nat) : Option State :=
  (Frontier M N).find? goalB

theorem witnessAt_spec (hspec) (h : witnessAt M goalB N = some s) :
  s ∈ Frontier M N ∧ goal s

def earliestGoalTick? (M) (goalB : State → Bool) (bound : Nat) : Option Nat :=
  (List.range (bound + 1)).find? (fun t => (Frontier M t).any goalB)

theorem earliestGoalTick?_spec (h : earliestGoalTick? M goalB bound = some N) :
  N ≤ bound ∧ (Frontier M N).any goalB = true ∧
    ∀ t, t < N → (Frontier M t).any goalB = false

theorem optimalAt_of_earliestGoalTick? (hspec) (h : ... = some N) :
  OptimalAt M goal N

theorem noGoal_below_of_earliestGoalTick?_none (h : ... = none) :
  ∀ t, t < bound + 1 → ∀ s ∈ Frontier M t, goalB s = false
```

- `earliestGoalTick?` 适合“先扫描、再证明”的工作流；它返回 `some N` 时直接给出 `OptimalAt M goal N`，返回 `none` 时只能证明 `bound` 内无目标（不能据此宣称最优）。
- `witnessAt` 找到的是 frontier 中第一个满足 `goalB` 的状态，适合生成人类可读的见证表；但**动作序列**仍应通过 `LegalPath`/`run` 提供（`Frontier` 只记状态，不记路径）。
- `find?_range_eq_some_spec` 是本文件自行证明的辅助引理，用来避免 core `List.find?_range_eq_some` 引入的 `Classical.choice`（见 §6）。

---

## 4. 合成场景接入步骤（给 synthetic v0）

`research/SYNTHETIC.md` 的 v0 只需要把四个概念映射到 `Model`：

| v0 概念 | Lean |
|---|---|
| `State = (pop, food, production, done)` | `structure State` 四个 `Nat` + `deriving DecidableEq, Repr` |
| `Action = (α, β)`（市民分配） | `abbrev Action := Nat × Nat` |
| 规则常量 / 转移 / 合法性 | 场景模块的 `def` / `theorem`，不要塞进 `Model` 字段 |
| 合法动作枚举 | `Model.legalActions`，并证明 `_sound` / `_complete` |
| `goal s := s.done ≥ 1` | `goal`（Prop）与 `goalB := decide (s.done ≥ 1)`（Bool） |
| Python 最早 tick / 见证 | `checkCertificate` / `earliestGoalTick?` / `LegalPath` + `run` |
| 精确步层 | `Frontier M t`（不是 BFS 距离层） |

### 4.1 实例化模板

```lean
import Civ6Verify.Reachability.Finite

namespace SyntheticV0
open Civ6Verify.Reachability

structure State where
  pop : Nat
  food : Nat
  prod : Nat
  done : Nat
  deriving DecidableEq, Repr

abbrev Action := Nat × Nat

/-- 场景的转移函数；非法输入可返回任意值（例如原状态），
    因为所有定理只对 legal 动作量化。 -/
def step (s : State) (a : Action) : State :=
  -- TODO: 按 SYNTHETIC.md §7 的结算顺序实现；这里用占位值保证模板可编译
  s

/-- 权威合法性：分配人数恰好等于 pop，且尚未完成。 -/
def legal (s : State) (a : Action) : Prop :=
  a.1 + a.2 = s.pop ∧ s.done = 0

/-- 注意：合法性含 `done = 0`，所以枚举也必须在 done > 0 时为空；
    否则 `legalActions_sound` 是假的（会枚举出非法动作）。 -/
def legalActions (s : State) : List Action :=
  if s.done = 0 then
    (List.range (s.pop + 1)).map (fun k => (k, s.pop - k))
  else
    []

def model : Model State Action where
  init := ⟨1, 0, 0, 0⟩
  step := step
  legal := legal
  legalDec := fun s a => by unfold legal; infer_instance
  legalActions := legalActions
  legalActions_sound := by
    intro s a h
    simp only [legalActions] at h
    split at h
    · rename_i hdone
      simp only [List.mem_map, List.mem_range] at h
      obtain ⟨k, hk, rfl⟩ := h
      exact ⟨Nat.add_sub_of_le (Nat.le_of_lt_succ hk), hdone⟩
    · simp at h
  legalActions_complete := by
    intro s a h
    obtain ⟨h1, h2⟩ := h
    simp only [legalActions, h2, if_true]
    refine List.mem_map.mpr ⟨a.1, ?_, ?_⟩
    · exact List.mem_range.mpr (Nat.lt_succ_of_le (Nat.le.intro h1))
    · have hsub : s.pop - a.1 = a.2 := by
        rw [← h1]
        exact Nat.add_sub_cancel_left _ _
      simp [hsub]
```

两个枚举证明是场景的**真实义务**。上面的算术片段对应“分配 `a.1 + a.2 = pop`
且 `done = 0`”这一简化合法性；合成 v0 的真实 `legal` 还要包含它自己的前置条件，
但证明形状相同：

- soundness：从 `a ∈ legalActions s` 拆出生成元 `k`，用
  `Nat.add_sub_of_le` / `Nat.le_of_lt_succ` 证明 `k + (pop - k) = pop`；
- completeness：从 `a.1 + a.2 = pop` 得 `a.1 ≤ pop`（`Nat.le.intro`），
  于是 `a.1 ∈ range (pop+1)`；再用 `Nat.add_sub_cancel_left` 把
  `(a.1, pop - a.1)` 还原成 `a = (a.1, a.2)`。

不要用 `sorry` 或自定义公理绕过。

### 4.2 目标桥接

```lean
def goal (s : State) : Prop := 1 ≤ s.done
def goalB (s : State) : Bool := decide (1 ≤ s.done)

theorem goalB_spec (s : State) : goalB s = true ↔ goal s := by
  simp [goalB, goal]
```

`goalB_spec` 是唯一允许把“可计算 Bool”与“定理里的 Prop”连接起来的地方。若这里写错，后面的 `OptimalAt` 仍然成立，但成立的是另一个目标；务必单独审查。

### 4.3 主证书

```lean
theorem optimal_at_five : OptimalAt model goal 5 :=
  optimalAt_of_checkCertificate goalB goalB_spec (by decide)
```

如果状态空间比预期大、`by decide` 归约过慢，可以把检查拆成两部分，仍然不引入额外信任：

```lean
theorem goals_none_below_five :
    ∀ t, t < 5 → ∀ s ∈ Frontier model t, goalB s = false :=
  checkNoGoalBelow_eq_true_iff.mp (by decide)

theorem frontier_five_has_goal :
    ∃ s, s ∈ Frontier model 5 ∧ goalB s = true :=
  List.any_eq_true.mp (by decide : (Frontier model 5).any goalB = true)

theorem optimal_at_five_split : OptimalAt model goal 5 :=
  optimalAt_of_noGoalBelow_and_witness goalB goalB_spec
    (by decide) (List.any_eq_true.mp (by decide))
```

`optimalAt_of_noGoalBelow_and_witness` 就是“下方无目标 + 第 N 层见证”的分离形式；`optimalAt_of_checkCertificate` 是它的单次布尔检查版本。两者都可以作为主证书。

### 4.4 见证动作序列

以下假设 `step` 已按 v0 的真实结算逻辑实现（§4.1 模板里的 `s` 只是占位值）。

```lean
def witness : List Action := [(1,0), (1,0), (1,0), (1,0), (0,2)]

theorem witness_legal : LegalPath model model.init witness := by
  unfold witness
  refine LegalPath.cons (by decide) <| LegalPath.cons (by decide) <|
    LegalPath.cons (by decide) <| LegalPath.cons (by decide) <|
      LegalPath.cons (by decide) (LegalPath.nil _)

theorem witness_run : run model model.init witness = ⟨1, 0, 0, 1⟩ := by decide

theorem witness_achieves : goal (run model model.init witness) := by
  simp [goal, witness_run]

theorem achievable_five : AchievableAt model goal 5 :=
  AchievableAt.of_legalPath (M := model) (goal := goal) (N := 5) (as := witness)
    rfl witness_legal witness_achieves
```

`by decide` 在这里是内核归约的 `Decidable` 证明，不是 `native_decide`；每个 `LegalPath.cons` 的合法性目标是具体的 `legal s a`。

### 4.5 见证查找（可选）

```lean
theorem frontier_five_goal :
    ∃ s, s ∈ Frontier model 5 ∧ goalB s = true :=
  List.any_eq_true.mp (by decide : (Frontier model 5).any goalB = true)

theorem witness_five : AchievableAt model goal 5 :=
  achievableAt_of_witness goalB_spec frontier_five_goal
```

若需要打印具体见证状态，可 `#eval witnessAt model goalB 5`；但 `#eval` 只是调试，最终定理仍应由 `checkCertificate` / `AchievableAt.of_legalPath` 给出。

---

## 5. 语义陷阱（务必阅读）

1. **exact-step vs 距离层**：`Frontier M t` 是“恰好 t 步可达”的去重集合，不是 BFS 最短距离层。一个状态可以在多个层出现；不要用 `Frontier` 的层数直接断言“最短距离”。
2. **层内去重、跨层保留**：`dedup` 只去掉同一层内的重复状态，不删除更早层出现过的状态。这与 exact-step 语义一致。合成 v0 的 exact-step 计数与距离层计数不同（见 `research/SYNTHETIC.md` §9.5）。
3. **`step` 是全函数**：非法动作的返回值是任意的；`Reachable` / `Frontier` 只让 `legal` 动作通过。不要在定理中直接量化 `step` 而不带 `legal`，否则会证出与模型无关的结论。
4. **枚举必须 sound + complete**：`legalActions` 少一个动作，`mem_frontier_iff` 无法证明，下界可能漏掉一条真实路线；多一个非法动作，`legalActions_sound` 无法证明，`Frontier` 可能包含非法后继。两个字段都是证明义务，不是可选项。
5. **`goalB_spec` 是信任接口**：`goalB` 与 `goal` 的等价必须证明。`checkCertificate` 只检查 `goalB`；如果 `goalB` 漏掉某个目标状态，定理仍然“正确”，但证明的是弱化后的目标。
6. **`decide` 不是 `native_decide`**：本文件只用 `decide`（内核归约）。若未来因性能改用 `native_decide`，必须按 PLAN.md §6 披露额外信任依赖；本核心不依赖它。
7. **不要用 `DecidableEq` 做语义等价**：`dedup` 使用 `[DecidableEq State]`。请用 `deriving DecidableEq` 或可证明一致的实例；不要手写一个与真实状态相等性不一致的判定器。
8. **有限期**：`NoEarlier M goal N` 只覆盖 `< N`；它不证明整个无限时间状态空间的最优性。`earliestGoalTick?` 的 `none` 结果只说明 `bound` 内无目标，不能升级为全局下界。
9. **模型 ≠ 游戏**：本核心证明的是 `Model` 语义下的结论。模型与真实 Civ6 的一致性（规则、取整、结算顺序、DLC/版本）是独立的 M0 验证工作，见 `PLAN.md` §2 和 `research/RULES-RESEARCH.md`。

---

## 6. 信任边界与公理审计

### 6.1 设计层面的信任边界

- **无 Mathlib**：只 import Lean core（`Init`/`Std` 由工具链提供）；`lakefile.toml` 没有外部依赖。
- **无 `sorry` / 自定义 `axiom` / `native_decide`**：已用 `grep` 检查源文件，仅文档注释里出现这些词。
- **唯一的“假设”是 `Model` 的字段**：`legalActions_sound` / `legalActions_complete` 是场景必须证明的定理，不是公理。`goalB_spec` 同理。
- **可执行函数与定理同源**：`Frontier`、`checkNoGoalBelow`、`checkCertificate`、`earliestGoalTick?` 都是普通 `def`；它们的规范由同文件定理给出，不存在“Python 检查器”与“Lean 语义”两套实现。

### 6.2 `#print axioms` 实测输出

在 `Civ6Verify/Reachability/Finite.lean` 末尾直接运行：

```text
'Civ6Verify.Reachability.mem_frontier_iff' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.reachable_iff_exists_legalPath' depends on axioms: [propext]
'Civ6Verify.Reachability.AchievableAt.of_legalPath' does not depend on any axioms
'Civ6Verify.Reachability.AchievableAt.of_mem_frontier' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.noEarlier_iff_all_legalPaths' depends on axioms: [propext]
'Civ6Verify.Reachability.noEarlier_iff_no_goal_in_frontier' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.checkNoGoalBelow_eq_true_iff' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.witnessAt_spec' depends on axioms: [propext]
'Civ6Verify.Reachability.optimalAt_of_checkCertificate' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.optimalAt_of_noGoalBelow_and_witness' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.find?_range_eq_some_spec' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.optimalAt_of_earliestGoalTick?' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.Toy.toy_optimal' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.Toy.toy_optimal_check' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.Toy.toy_optimal_split' depends on axioms: [propext, Quot.sound]
'Civ6Verify.Reachability.Toy.toy_check_two_fails' depends on axioms: [propext]
'Civ6Verify.Reachability.Toy.toy_not_achievable_two' depends on axioms: [propext, Quot.sound]
```

解释：

- `propext` 和 `Quot.sound` 是 Lean 标准公理，由 core `List` 引理（`List.mem_flatMap`、`List.any_eq_true`、`List.mem_range` 等）引入；**不是**本项目的自定义公理。
- **没有 `sorryAx`**，**没有 `Classical.choice`**。`Classical.choice` 原本会由 core 的 `List.find?_range_eq_some` 引入；本文件用自证的 `find?_range_eq_some_spec` 替代了它。
- 其余定理（例如 `AchievableAt.of_legalPath`、`ReachableFrom.head`、`LegalPath.append`、`NoEarlier.mono`）完全不依赖任何公理。
- 对整个模块做过额外抽查：没有任何导出定理依赖 `Classical.choice`。
- 若项目后续要求“连 `propext` 也不用”，需要重写 core 列表引理的本地版本；当前阶段按 PLAN.md §6 的要求披露即可，不应把“通过编译”等同于“没有信任依赖”。

---

## 7. 冒烟测试（Toy）

文件末尾的 `namespace Toy` 是一个四状态合成模型，不是 Civ6 场景：

- 状态 `s0, s1, s2, s3`；动作 `wait, advance`；
- `legalActions s0 = [wait, advance]`，`s1/s2 = [advance]`，`s3 = [wait]`；
- `goal s := s = s3`，`goalB s := decide (s = s3)`；
- `witness = [advance, advance, advance]`；
- 已证明：
  - `Toy.witness_legal` / `Toy.witness_run` / `Toy.toy_achievable`（上界）；
  - `Toy.toy_earliest : earliestGoalTick? model goalB 6 = some 3`（扫描）；
  - `Toy.toy_optimal : OptimalAt model goal 3`（扫描证书）；
  - `Toy.toy_check : checkCertificate model goalB 3 = true`（布尔证书）；
  - `Toy.toy_optimal_split`（分离的 lower bound + witness 形式）；
  - `Toy.toy_check_two_fails : checkCertificate model goalB 2 = false`（故意降低 N 失败）；
  - `Toy.toy_not_achievable_two : ¬ AchievableAt model goal 2`（负结果）；
  - `Toy.toy_witnessAt : witnessAt model goalB 3 = some s3`（见证查找）。

实测 `Frontier` 层大小（同层去重、跨层保留）：

```text
[1, 2, 3, 4, 4, 4, 4]
```

`Frontier 3 = [s0, s1, s2, s3]`；`checkCertificate ... 3 = true`，`... 2 = false`，`earliestGoalTick? ... 6 = some 3`。

这个测试的价值是：它把“模型实例化 → 合法路径 → 精确步 frontier → 布尔证书 → 负结果”整条链在一次编译中跑通，且规模足够小，`decide` 不会成为性能问题。

---

## 8. 限制与后续工作

本核心刻意保持通用和最小；以下内容**不在**本文件范围内：

1. **真实 Civ6 规则/数值**：由 M0 规则核实与后续 `Civ6Verify/Rules/`、`Scenarios/` 模块负责。本文件不包含任何 Civ6 常量。
2. **状态不变量与支配剪枝**：`Frontier` 不做任何剪枝；若场景要加入支配关系，必须单独证明“剪枝保持目标可达性”，不能假定“储粮更多永远更好”（PLAN.md M3）。
3. **距离层/BFS 最短路径**：`Frontier` 是 exact-step；若需要 BFS 距离层，应在场景侧另建集合，并证明其与 `AchievableAt` 的关系。
4. **外部 frontier 证书导入**：本核心从 `M.init` 重新计算；若要从 Python 导入逐层证书，需要额外的检查器验证初态、全后继覆盖和无目标性质（PLAN.md §4）。
5. **无限期/全局最优性**：只支持有限 `N`；`NoEarlier` 不覆盖 `t ≥ N`。
6. **性能**：`Frontier` 每层做一次 `flatMap` 和 `dedup`（`dedup` 是二次过滤），适合几十到几千状态的小场景；大规模场景需要更高效的数据结构或经过证明的剪枝。`decide` 的归约成本也随状态数增长。
7. **多实例**：`Model` 是 typeclass；同一 `State`/`Action` 有多个模型时，用 `letI`/局部实例或显式 `@` 参数区分，避免类型类搜索选错模型。
8. **目标单调性**：本核心不强制 `goal` 单调；若场景目标是“曾经完成过”，请用单调历史计数并在场景层证明单调性。`OptimalAt` 的“首次”语义在非单调目标下仍然定义为“在 N 成立且之前不成立”，但解释时要小心。

---

## 9. 文件清单

```text
Civ6Verify/Reachability/Finite.lean   # 本核心（唯一修改的 Lean 文件）
research/REACHABILITY.md              # 本文件
```

未修改：

```text
Civ6Verify.lean
Main.lean
lakefile.toml
lean-toolchain
scripts/lean-env
research/ENVIRONMENT.md
research/RULES-RESEARCH.md
research/SYNTHETIC.md
research/TOOLCHAIN.md
```
