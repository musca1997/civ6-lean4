# ROBUSTNESS.md — 候选轴稳健性（C2–C7），条件模型内结论

归属：本文件与 `Civ6Verify/Robustness/Candidates.lean` 由 candidate-robustness 里程碑 owner 维护。
契约：`mvp/RULE-CONTRACT.md` v2.1 §6（Θ_MVP，2⁷ = 128）；基线结果：`mvp/RESULTS.md`。

> **结论强度：条件模型内定理（CONDITIONAL）。**
> 下面的 "inert / 稳健" 全部是 `M_MVP(θ, σ)` 内部、kernel-checked 的结论，**不是**《文明 VI》事实。
> 本仓库没有钉死游戏构建、没有跑 fixture、`[V] = 0`、没有公开游戏证据。
> 本文**不**声称 128 组全部已认证；只声称下表列出的、每根轴**单独**切换时的结论，
> 其余轴（C2、C4、C5）明确标为未决，并列出精确未结证明义务。

---

## 1. 背景与问题

现有 Lean 开发只参数化 `settlerCost`（`Params.cost`）；C2–C7 全部硬编码在基线
θ* = (growth_first, best, amenityStock 2, basket zero, productionRounding exact,
thresholdRounding exact 3383)。`mvp/RESULTS.md` §1.1 已记录该限制；契约 §6 的
128 组候选是 Python 搜索估计（`search/mvp.py`，不可信），契约 §0/§10 的 "only argmin
and argmax certified" 与 "C2–C7 predicted inert (unproved)" 是本文要处理的核心缺口。

本文回答两个问题：

1. **哪几根非成本轴可以在 kernel 内证明为 inert（或由现有下界覆盖）？**
2. **不能的，卡在哪里？精确的未结证明义务是什么？**

---

## 2. 结论总表

| 轴 | 候选值 | 结论 | 机制 | Lean API |
|---|---|---|---|---|
| **C1** `settlerCost` | 80 / 110 | 已参数化，两端点已认证（既有） | `Params.cost`，成本在完成判据中单调 | `optimalAt_baseline` / `optimalAt_cost110` |
| **C7** `thresholdRounding` | exact 3383 / floor 3300 | **✅ 两端点均认证 inert** | 差异只在 pop 3；`Inv` 梯子给 `food+e ≤ 1600 < 3300`，两读数都不增长 | `modelF`, `stepT_floor_eq_step`, `floor_optimalAt_baseline/cost110`, `c7_inert_certified` |
| **C3** `newCitizen` | best / none | **✅ 两端点均认证 inert**（下界 + 见证） | 只把 `q` 逐点降低（`qOf` 不影响食物/人口/合法性）；基线路径支配 | `qNewCitizenNone`, `modelQ`, `stepQ_dom`, `c3_optimalAt_baseline/cost110` |
| **C6** `productionRounding` | exact / trunc10 | **✅ 两端点均认证 inert**（下界 + 见证） | 同上：`trunc10 ≤ qOf` 逐点 | `qTrunc10`, `trunc10_noEarlier_20/25`, `c6_optimalAt_baseline/cost110` |
| **C2** `turnOrder` | growth_first / production_first | ❌ 未结 | 改变步内增长/生产的**次序**；既非步等价也无逐点 `q` 支配 | — |
| **C4** `amenityStock` | 2 / 1 | ❌ 未结，且**已证步级不可等价** | pop 3 时基线 Happy（×1.05），stock 1 为 Content（×1.00）；增长/生产乘子同时改变 | `c4_multiplier_separates` |
| **C5** `basketOnGrowth` | zero / subtract | ❌ 未结，且**已证步级不可等价** | 改变食物篮，进而改变后续增长时点 | `c5_step_separates` |

补充：**C6 也已证步级不可等价**（`c6_step_separates`：`init` 上只工作 `PH`
时 `q = 525`，trunc10 为 `520`）。所以 C6 的结论是 "在 N=20/25 处 inert"，
**不是** "逐步等价"——这两者必须分开陈述（这也是本里程碑要求的最小诚实度）。

---

## 3. C7 `thresholdRounding`：完整的 inert 证书

### 3.1 语义
`thresholdT3Floor` 是把 `Civ6Verify.Model.Mvp.threshold` 的第 3 项从 `3383` 改为
`3300` 的**独立定义**（`exact 33.8284` vs `floor 33.00`）。模块里另写了完整管线
`wg / popAfterT / foodAfterT / productionT / qOfT / progAfterT / completesT / stepT`，
并以

```lean
theorem stepT_threshold_eq (p s a) : stepT threshold p s a = step p s a
```

证明它**是**基线的扩展而不是分叉（不是简单改标签：`stepT` 自带 `q`，与
`Civ6Verify.Model.Mvp.step` 是分离定义）。

### 3.2 关键引理
```lean
theorem wg_floor_eq_wg {n s a} (hinv : Inv n s) (hn : n ≤ 24) (hleg : legal s a) :
    wg thresholdT3Floor s a = wg threshold s a
theorem stepT_floor_eq_step {n p s a} (hinv : Inv n s) (hn : n ≤ 24) (hleg : legal s a) :
    stepT thresholdT3Floor p s a = step p s a
```
证明：阈值只在 `pop = 3` 处不同。`Inv`（既有 `MvpOptimality.Inv`）含食物梯子
`(s.food : ℤ) + floorI s.pop ≤ 220·n`，其中 `floorI 3 = 3900`。于是
`n ≤ 24 ⇒ s.food ≤ 1380`，又 `growthAmount ≤ 220`（`growthAmount_le_220`），
所以 `food + e ≤ 1600`，远低于 **两个**阈值 ⇒ 两读数都不增长。（实际余量很大：
梯子在 pop 3 允许的是 `≤ 1600`，不是逼近 3300。）

### 3.3 传递到最优值
```lean
theorem inv_of_reachable_floor  -- 沿 modelF 的可达性归纳，复用 inv_step
theorem floor_noEarlier_20 / floor_noEarlier_25
theorem floor_achievable / floor_achievable110   -- 见证在 modelF 下逐字回放
theorem floor_optimalAt_baseline : OptimalAt (modelF baselineParams) goal 20
theorem floor_optimalAt_cost110  : OptimalAt (modelF cost110Params)  goal 25
theorem c7_inert_certified        -- 两者合取
```

### 3.4 精确假设
- 梯子不变量 `Inv n s`（既有定理 `inv_of_reachable`/`inv_step` 提供），且 **`n ≤ 24`**；
  这正好覆盖两个认证端点（20 与 25 的下界分别用 T = 19、24）。
- 其余五轴固定在基线；合法性谓词与阈值无关，所以 `legal`/`legalActions` 直接复用。
- `H = 34` 的 `horizonOk` **不被本文使用**：只需 `t ≤ 24`。诚实说明：梯子在
  `t = 34` 只给 `food ≤ 3580`，超过 3300，因此 t > 24 的 C7 等价性**未证**；
  它不影响 N = 20/25 的认证，但如果将来要证到更大的 horizon，这段论证必须加强。

---

## 4. C3 / C6：逐点 `q` 耦合（现有下界的转移）

### 4.1 机制
`newCitizen` 只通过 `extraGain` 进入 `production`；`productionRounding = trunc10`
只把 `q` 变为 `⌊q/10⌋·10`。两者都**不改变** `growthAmount`、`wouldGrow`、
`popAfter`、`foodAfter` 或合法性。因此模块定义了一个泛化的替代步
`stepQ qFn`（除被记 `q` 外完全同 §4），并证明：

```lean
def Dom (sb sa) := sa.pop = sb.pop ∧ sa.food = sb.food ∧ sa.trained = sb.trained ∧ sa.prog ≤ sb.prog
theorem qOf_dom          -- 耦合状态下 qOf 相同
theorem stepQ_dom        -- 基线不完成 + qFn ≤ qOf ⇒ Dom 保持
theorem coupled_exists_gen / coupled_exists / coupled_exists_110
theorem modelQ_coupled_noEarlier_20 / _25   -- 泛化下界：∀ qFn ≤ qOf
theorem qNewCitizenNone_le / qTrunc10_le
theorem newCitizenNone_noEarlier_20/25, trunc10_noEarlier_20/25
```

直观：替代路径 `sa` 与基线路径 `sb` 同步（相同动作），
`pop/food/trained` 相等而 `prog` 更小；基线不变式保证 `prog < cost`
（`trained_zero_at_19/24` ⇒ 未完成），故替代路径也不会提前完成。

### 4.2 上界（见证）
基线见证在增长步用 `extra = none`（`extraGain = 0`），且生成的 `q` 为 `420`、`630`，
都是 10 的倍数，因此在 C3 与 C6 语义下**逐步相同**。于是：

```lean
theorem c3_optimalAt_baseline / c3_optimalAt_cost110
theorem c6_optimalAt_baseline / c6_optimalAt_cost110
theorem c3_c6_inert_certified
```

### 4.3 精确假设
- 耦合论证是 horizon-uniform 的，但模块只在 `t ≤ 19`（cost 80）与 `t ≤ 24`（cost 110）
  上实例化，且使用既有 `trained_zero_at_19` / `trained_zero_at_24`（即基线不变式）。
- `qFn ≤ qOf` 必须是**逐点**不等式（对任意状态/动作），这是两个实例的证明义务，
  已分别由 `qNewCitizenNone_le` / `qTrunc10_le` 关闭。

---

## 5. 未结轴：精确证明义务

### C2 `turnOrder`
`production_first` 的 `q` 在**增长前**人口上计算，且（按 `search/mvp.py` 的读法）
不含新市民项；增长发生在生产之后。这与 `growth_first` 不是步等价的，
也不满足 `qFn ≤ qOf`（顺序变化可双向）。**义务**：
1. 在 `Candidates.lean` 风格下定义 `stepProductionFirst` 的完整管线；
2. 给出耦合/对偶不等式，例如在 pop 2 的中间步上重建
   `11·q + 21·e ≤ 9240`（`MvpArithmetic.dual_pop2`）在 production_first 下的对应物；
3. 证明 `NoEarlier 20/25`，再回放见证。
预计这是 6 轴中最重的一根，因为它改的是步的**结构**而非某个标量项。

### C4 `amenityStock = 1`
**已证步级不同**（`c4_multiplier_separates`）：pop 3 时基线 `prodMult 3 = 105`，
stock 1 为 `100`；`growthMult 3` 也从 `110` 降到 `100`。**义务**：把
`growthMult`/`prodMult` 参数化（tier 由 `stock − req(pop)` 决定），重做
`growthAmount_le_220`、`qOf_le_630`、双不等式与 `Inv`（Content 层下产出更低，
下界反而更容易，但食物侧增长也更慢，必须整体重推，不能只换乘子）。注意这**不是**
单调替换：增长项与生产项同时下降。

### C5 `basketOnGrowth = subtract`
**已证步级不同**（`c5_step_separates`：见证增长步 zero 给 0，subtract 给 40）。它改变
未来增长时点，所以既不是步等价也无现成的逐点支配。**义务**：把 `foodAfter` 参数化，
证明 subtract 语义下的 `Inv` 变体（篮子在增长后残留 `food + e − T`，梯子要改成
"已投入 + 残留"，并重新算 pop 3 到达时间的端点）。

---

## 6. 与 128 组包络的关系（不夸大）

- 本模块**没有**证明 128 组全部认证，也没有把 "C7 inert" 当作其余轴的普适结论。
- 显式认证的 θ 点：C1 ∈ {80, 110} 上，**单独**切换 C3、C6、C7 各得一个点，
  加上基线，共 **8 / 128**。组合（如 C3∧C6、或再叠 C7）**未形式化**；
  精确义务很小：定义 `qNewCitizenNoneTrunc10 := fun s a => (qNewCitizenNone s a / 10) * 10`，
  用 `le_trans (Nat.div_mul_le_self _ _) (qNewCitizenNone_le s a)` 得逐点界，
  再套 `modelQ_coupled_noEarlier_*` + 见证回放即可；C7 与它们正交（不触碰 `q`），
  合并需要把 `stepT` 与 `stepQ` 组合成单一 `stepTQ`（这是**下一步工作**，未做）。
- C2/C4/C5 未结，故 `[20, 25]` **仍然只是搜索估计**，不是认证区间。

---

## 7. 公理足迹 / 复现命令

```bash
scripts/lean-env lake env lean Civ6Verify/Robustness/Candidates.lean
```

- 无 `sorry`、无 `admit`、无自定义公理、无 `native_decide`、无 Mathlib。
- `#print axioms` 输出（全部）：`propext`、`Quot.sound`（核心 `List` 引理带来），
  个别为 `[]` 或 `[propext]`；**没有 `sorryAx`、`Classical.choice`、`Lean.ofReduceBool`**。
- 闭式数值事实用 `decide +kernel`（kernel reduction，无编译器信任）。
- 未修改 `Civ6Verify/Model/Mvp.lean`、`Civ6Verify/Bounds/MvpOptimality.lean`、
  `Civ6Verify.lean` 根模块与 lakefile；本模块只 import 它们，且不被根模块 import
  （因此 `lake build` 不受影响，需按上面命令单独编译）。

---

## 8. 非声明（Non-claims）

- 不是 Civ6 事实；不是真实游戏最早 settler；不涉及第二个 settler/城市/地图。
- 只在 §8.1 限制动作集与 A1/A2/A8、no-carry 限制下成立。
- "inert" 仅指在 `OptimalAt` 的 N 上不变；C6 明确**不**是步级 inert。
- 未背书 `search/mvp.py` 的 128 组预测；未声称包络 `{20, 25}` 已证。
