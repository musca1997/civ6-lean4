# RESULTS.md — 条件 MVP 基线模型：结果、下界推导与未决项

归属：本文件只由本任务 owner 维护。
日期：2026-10-18。
契约：`mvp/RULE-CONTRACT.md` v2.1；场景 σ = `sigma-capital-4tiles-v1`。

> **结论强度：条件模型内定理（CONDITIONAL）。**
> 下面所有 `N` 都是 `M_MVP(θ, σ)` 内部的结论，不是《文明 VI》事实。
> 本仓库没有钉死任何游戏构建、没有跑过游戏内 fixture、`[V] = 0`。
> 所认证的是一个 **Civ6 形状的条件基线模型**，**不是**经过真实游戏引擎/构建校验的模型。

---

## 1. 已认证的内容（Lean，kernel-checked）

文件：`Civ6Verify/Model/Mvp.lean`、`Civ6Verify/Bounds/MvpArithmetic.lean`、
`Civ6Verify/Bounds/MvpOptimality.lean`。

```lean
theorem optimalAt_baseline : OptimalAt (model baselineParams) goal 20
theorem optimalAt_cost110  : OptimalAt (model cost110Params)  goal 25
```

- `OptimalAt M goal N := AchievableAt M goal N ∧ NoEarlier M goal N`。
- **可达性**来自模型自身的 witness：`baseline_achievable` / `cost110_achievable`。
- **下界**来自模型自身 `step`/`legal` 生成的 `Reachable` 上的归纳不变式
  （`inv_step`、`inv_of_reachable`、`trained_zero_at_19/24`、`noEarlier_20/25`），
  不是把结论当成假设，也不是简单枚举 frontier。
- 动作枚举的 soundness / completeness（`legalActions_sound` / `legalActions_complete`）
  由 `List.mem_filter` 证明。
- 公理足迹（本地 `#print axioms` 复核）：

```
optimalAt_baseline  depends on axioms: [propext, Quot.sound]
optimalAt_cost110   depends on axioms: [propext, Quot.sound]
noEarlier_20        depends on axioms: [propext, Quot.sound]
noEarlier_25        depends on axioms: [propext, Quot.sound]
inv_of_reachable    depends on axioms: [propext, Quot.sound]
```

无 `sorryAx`、无自定义公理、无 `native_decide`、无 Mathlib。

### 1.1 参数化范围（重要限制）

**Lean 中只有成本轴是参数。** `Params` 只含 `cost`；其余候选轴（回合内顺序、新市民输出、
宜居存量、食物篮、生产取整、阈值取整）**固定在基线假设**上：

| 轴 | Lean 基线取值 | Python 候选 |
|---|---|---|
| settlerCost | 8000 / 11000（已参数化） | 80 / 110 |
| turnOrder | growth_first | growth_first / production_first |
| newCitizen | best | best / none |
| amenityStock | 2 | 2 / 1 |
| basketOnGrowth | zero | zero / subtract |
| productionRounding | exact | exact / trunc10 |
| thresholdRounding | exact (T(3)=3383) | floor (3300) / exact (3383) |

Python 搜索器 `search/mvp.py` 枚举了全部 **128 组 θ 候选**，得到包络 `[20, 25]`。
**这 128 组全部是搜索估计，未经 Lean 证明**；Lean 只认证其中 argmin（cost 80）与
argmax（cost 110）两点。因此"只有成本轴在 Lean 中变化，其余 Python 候选未证明"是本文件的
核心限制之一。

---

## 2. 精确资源下界（来自 bridge 本身，而非独立的算术）

下界在模型侧是一个**析取不变式** `Inv t s`（`MvpOptimality.lean`），沿模型的 `Reachable`
归纳。它不是"把另一份算术结论抄过来"，而是把算术核心的逐步界接入真实 `step`。

### 2.1 逐步界（`MvpArithmetic` + 模型侧实例）

- `e = growthAmount ≤ 220`（pop 1–2；pop 3 时 ≤ 110）；
- 记 `q = qOf`（未乘 credit 的产量）：全局 `q ≤ 735`；
- pop 2 且本步不增长：`q ≤ 630`；
- pop 2 或 pop 3 且本步不增长（对偶）：`11·q + 21·e ≤ 9240`。

### 2.2 食物阶梯

`floorI(p) := 1500·[p≥2] + 2400·[p≥3] + 3383·[p≥4]`，不变式含

```
food + floorI(pop) ≤ 220·t
```

（生长自动发生且 `basket = zero`，所以已生成食物必须覆盖已消耗阈值加上当前篮子。）
推论：`t ≤ 23` 时 `pop ≤ 3`——因为 `floorI(4) = 7283 > 220·23 = 5060`。

### 2.3 case A：停留在 pop 2

- 第 7 步才能到 pop 2（`⌈1500/220⌉ = 7`），第 8 步才可能出现第一次 credited 步骤；
- 此后每步 `q ≤ 630`，故 `11·prog ≤ 6930·(t − 7)`。

```
t = 19:  6930·12 = 83160  ⇒ prog ≤ 7560 < 8000
t = 24:  6930·17 = 117810 ⇒ prog ≤ 10710 < 11000
```

case A 是紧的：模型 witness 在 `t = 19` 恰好取得 `prog = 7560`
（`witness_prog_eq_bound`、`witness_after_nineteen`）。

### 2.4 case B：pop 3 分支（诚实说明它如何被计入下界）

这是契约 v2.1 §10(iii) 列为"未证明"的分支；`MvpOptimality.lean` 用**状态局部**形式给出它，
而不是把它当作独立算术。

在 pop 2 → 3 的增长步：增长要求 `food + e ≥ T(2) = 2400`，且 `e ≤ 220`，
故该步之前篮子满足 `food ≥ 2400 − e ≥ 2180`。把它代入 pop 2 的对偶不变式
`11·prog + 21·food ≤ 9240·(t − 7)`，再叠加该增长步的粗界 `q ≤ 735`：

```
11·prog' ≤ 9240·(t − 7) − 21·2180 + 8085
         = 9240·(t + 1) − 111615
```

于是 pop 3 不变式为

```
11·prog ≤ 9240·t − 111615
```

数值端点：

```
t = 19:  9240·19 − 111615 = 63945  ⇒ prog ≤ 5813  < 8000
t = 24:  9240·24 − 111615 = 110145 ⇒ prog ≤ 10013 < 11000
```

（`caseB_endpoint_19/24` 证明这两个数论蕴含。这个端点比 `mvp/LOWER-BOUND.md` 文档形式的
`5889 / 10089` 更紧；两者都属于同一套模型侧记账，文档形式的推导也是对偶 + 食物阶梯。）

### 2.5 结论

`Inv` 含有 `trained = 0`，所以：

- cost 80：`∀ t ≤ 19, trained = 0` ⇒ `NoEarlier ... goal 20`；
- cost 110：`∀ t ≤ 24, trained = 0` ⇒ `NoEarlier ... goal 25`。

与 witness 的 `AchievableAt` 合并即得 §1 的 `OptimalAt`。

**边界条件**：`t = 19` 时 `pop ≤ 3`（§2.2）；若 pop 3 分支出现，它被 §2.4 的
`−111615` 端点单独收费，而不是被"从第 8 步起 `q ≤ 735`"这种会伪证 `18/22` 的说法覆盖。
这正是"从 bridge 本身解释下界、而不只是列另一份算术"的意义。

---

## 3. 契约风格 witness（数值直接来自 Lean）

witness = `GH ×7 IDLE`（growth 步 `extra = none`，v2.1 的 `extraGain(⊥)=0`），
随后 `GH+PH ×13`（cost 80）或 `GH+PH ×18`（cost 110）SETTLER。
下列状态由 Lean `run` 直接求值（`#eval`）并与 `witness_run` / `witness110_run` 一致。

### 3.1 cost 80（`baselineParams`，N = 20）

| 步 | pre-pop | 工作格 | build | F | P | d | e | q | food | prog |
|---|---|---|---|---|---|---|---|---|---|---|
| 1–6 | 1 | GH | IDLE | 400 | 400 | 200 | 220 | 420（不计） | 0 → 1320 | 0 |
| 7 | 1 | GH | IDLE | 400 | 400 | 200 | 220 | 420（不计） | 1320 + 220 = 1540 ≥ 1500 ⇒ pop 2，篮子 → 0 | 0 |
| 8–19 | 2 | GH,PH | SETTLER | 500 | 600 | 100 | 110 | 630 | 0 → 1320 | 0 → 7560 |
| 20 | 2 | GH,PH | SETTLER | 500 | 600 | 100 | 110 | 630 | 1430 | 7560 + 630 = 8190 ≥ 8000 ⇒ **goal** |

终态（Lean `witness_run`）：`(pop = 1, food = 1430, prog = 190, trained = 1)`。

### 3.2 cost 110（`cost110Params`，N = 25）

| 步 | pre-pop | 工作格 | build | F | P | d | e | q | food | prog |
|---|---|---|---|---|---|---|---|---|---|---|
| 1–6 | 1 | GH | IDLE | 400 | 400 | 200 | 220 | 420（不计） | 0 → 1320 | 0 |
| 7 | 1 | GH | IDLE | 400 | 400 | 200 | 220 | 420（不计） | 1320 + 220 = 1540 ≥ 1500 ⇒ pop 2，篮子 → 0 | 0 |
| 8–24 | 2 | GH,PH | SETTLER | 500 | 600 | 100 | 110 | 630 | 0 → 1870 | 0 → 10710 |
| 25 | 2 | GH,PH | SETTLER | 500 | 600 | 100 | 110 | 630 | 1980 | 10710 + 630 = 11340 ≥ 11000 ⇒ **goal** |

终态（Lean `witness110_run`）：`(pop = 1, food = 1980, prog = 340, trained = 1)`。

说明：

- `q = 420` 出现在 growth 行，因为 `extra = none` 时 `extraGain = 0`（v2.1 的 B1 修正；
  旧的 `q = 525` 读数已作废）。
- IDLE 步骤不产生 settler 进度；`t ≤ 7` 时 `prog = 0`。
- 两条 witness 都 idle-free、饥饿-free，且 `pop ≥ 2` 之前 `prog = 0`。

---

## 4. 使用的显式假设（每条都可被实测推翻）

| 假设 | 取值 | 标签 / 影响 |
|---|---|---|
| A8 pre-turn selection | build 在步骤开始时选定；pop 1 不能选 SETTLER；同回合增长不会事后合法化 SETTLER | `[ASSUME]`；若假，模型会更快（`19/24`，在 Θ 之外） |
| R-SET-9 / no idle credit | IDLE 不计任何 settler 进度 | `[D*]` 语义选择；v1 的 banking 版本已作废（曾给出 `15/20`） |
| starving 非法 | modifier 后 surplus < 0 不是合法动作 | **限制类**：只会抬高 `N`，不能承载真实游戏下界 |
| palace +2 P（A1） | 城中心 2F/1P + 宫殿 +2P ⇒ 基础 `F₀=200, P₀=300` | `[C]`；若宫殿为 +0/+1/+3，则 `N` 与 horizon 都变 |
| happy 乘数 | amenityStock = 2 ⇒ pop 1–3 为 Happy：growth ×1.10、非食物 ×1.05 | 与 A1/A2 共同决定 `e=220, q=630` |
| 固定 4 格 | G 2F/0P、GH 2F/1P、PH 1F/2P、P 1F/1P；1 人 1 格、不重复、无边界扩张 | `[SCENARIO]` |
| fresh water / housing 惰性 | housing 6，pop ≤ 3 时 growth factor = 1.00 | G2 |
| basket zero / exact rounding | 增长清空篮子；产量取整与阈值取整均为精确 | C5/C6/C7；C7 惰性 |
| no carry | 未建模建造的 overflow 不转入 settler | 限制类（`≤ q` carry 会给出 `19/24`，在 Θ 之外） |
| step ≠ UI turn | `t = 0` 是建城快照；一步 = 一个 settlement step，不是界面回合 | 时间约定 |
| 无第二城 | 不建模移动、建城、第二城；goal 是"trained ≥ 1"而不是"已坐城" | 范围外（X10/X11） |
| 能力型排除 | X1–X17/X19/X20 被排除（购买、砍伐、政策/市政、建造者、万神殿、村庄、城邦、伟人、奇观…） | 下界只对受限动作集成立 |
| 松弛型排除 | X18 蛮族/敌方/灾害被排除 | 安全：真实游戏只会更慢 |
| IDLE 合法性 | IDLE 代表"在建别的东西"，其合法性依赖 X4–X7 的排除 | 必须显式写出 |

---

## 5. 复现与验证状态

### 5.1 已本地复核

```bash
scripts/lean-env lake build Civ6Verify.Bounds.MvpOptimality   # 绿
python3 search/mvp.py --self-test                            # 28 tests OK
python3 search/mvp.py --check-fixture                        # ok: baselineN=20, cost110N=25
```

本文件中的 `1430 / 1980 / 190 / 340 / 7560` 等数值由 Lean `run`/`#eval` 与
`#print axioms` 直接复核，不是手抄。

### 5.2 验证流水线状态

- `scripts/verify.sh` 已由集成方独立完整执行并通过：主构建与最优性模块构建、两套模型各 28 项测试、
  fixture 校验、synthetic 47 项对照、MVP 2239 项对照及 7 项负向测试、公理审计均通过。
  审计覆盖 686 个公开定理常量及 21 个私有生成定理。详见 `mvp/VALIDATION.md`。
  这些检查确认模型内部一致与证明可信边界，不是实际文明 VI 的验证。
- `.github/workflows/verify.yml` 已存在，但**从未执行**（没有 push），因此其状态不可作为证据引用。
- 本任务直接复核的证据是：MVP 目标 `lake build` 绿；`#print axioms` 仅 `propext`/`Quot.sound`；
  `search/mvp.py --self-test` 28 项通过；`--check-fixture` 返回 `baselineN=20, cost110N=25`。

### 5.3 冻结 fixture 的已知差异

`fixtures/mvp-baseline.json` 自身记录了与旧分析稿的 3 处差异（`D-SCALE-maxLayerObserved`、
`D-SCALE-maxFoodPop3`、`D-AMEN-P4`），这些差异不影响 `N`，且**不被静默修复**。
另有限制 `L-HORIZON`：可执行文件用 `H = 27`（任务上限），契约用 `H = 34`；所有 θ 的
`N ≤ 25`，故最小性不受影响，但 `H = 34` 的敏感性包络未在此检查。

---

## 6. 合成基准仍然保留

`fixtures/synthetic-v0.json`（BMK-v0）与 `Civ6Verify/Scenarios/Synthetic.lean` 继续保留，
用途是通用引擎的流水线自检（第 5 步完成，最优序列唯一）。它刻意**非 Civ6 形状**：

- 不要把 BMK-v0 的回合数与 `M_MVP` 的 `20/25` 混排；
- BMK-v0 **不**构成任何真实游戏最优主张；
- `M_MVP` 的 `20/25` 也**不**构成任何真实游戏最优主张。

---

## 7. 未决范围（unresolved scope）

1. **证据验证缺失（最重要）**：`[V] = 0`；未钉死游戏构建；未跑任何游戏内 fixture；
   A1–A8 全部未实测；K0–K7 未解除。因此本文档不能升级为任何真实游戏断言。
2. **θ 覆盖不完整**：Lean 只参数化成本轴，只认证 argmin/argmax；128 组 Python 候选
   （包络 `[20, 25]`）未经证明；C2–C7 的惰性没有 Lean 引理。
3. **模型不等于引擎**：这是一个 Civ6 形状的条件基线模型，不是真实游戏规则引擎，也没有构建校验。
4. **witness/下界之外的量**：per-axis marginal 的 Lean 惰性引理、pop-3 下界的紧性、
   第二移民/第二城均未证明。
5. **文档陈旧**：`mvp/LOWER-BOUND.md`、`mvp/LEAN-MODEL.md`、`research/MVP-VALIDATION.md`
   写于 bridge 完成前，仍称"下界是桥接义务 / 只证明 witness"；这些文件不在本任务 ownership 内。
6. **CI 尚未运行**：本地统一验收已通过，`mvp/VALIDATION.md` 已落地；GitHub CI 未执行，本轮改动未 push。
7. **无游戏资源**：本项目不包含《文明 VI》游戏资源，与游戏发行商无关联；也不引入任何此前删除的致谢/灵感归属。
