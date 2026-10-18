# civ6-lean4

用 Lean 4 探索《文明 VI》运营极限的形式化证明。

> **这是一个"条件模型"项目，不是文明 VI 模拟器，也没有经过真实游戏引擎/构建校验。**
> 仓库现在包含一个 Civ6 形状的条件基线模型 `M_MVP(θ*, σ)`（单城、固定 4 格、首个移民），
> 并已在 Lean 中证明 `OptimalAt ... goal 20`（成本 80）与 `OptimalAt ... goal 25`（成本 110）。
> 这些结论只对模型成立：没有 `[V]` 实测、没有钉死游戏构建、也没有跑过游戏内 fixture。
> 已验证的合成城市基准仍然保留，但它只是流水线自检，不代表任何真实开局的最优回合。

## 想证明什么？

给定明确的规则、初始城市和允许操作，同时证明：

1. **做得到**：存在第 N 回合完成目标的合法路线。
2. **不能更快**：所有合法操作序列都无法在 N 之前完成目标。

## 当前成果

### 条件基线模型（MVP v2.1）

- `Civ6Verify/Model/Mvp.lean`：`M_MVP(θ*, σ)` 基线模型，动作枚举的 soundness/completeness 已证明，不是建模假设。
- `Civ6Verify/Bounds/MvpArithmetic.lean`：与模型无关的 σ 算术核心（每格预算、对偶不等式、食物阶梯、端点）。
- `Civ6Verify/Bounds/MvpOptimality.lean`：把上面的算术接到模型自身的 `step`/`Reachable` 上，得到真正的
  `OptimalAt (model baselineParams) goal 20` 与 `OptimalAt (model cost110Params) goal 25`
  （可达性用模型自带 witness，下界用不变式归纳，不是额外假设）。
- 公理足迹：`optimalAt_baseline` / `noEarlier_20` / `optimalAt_cost110` / `noEarlier_25` 只依赖 `propext` 与 `Quot.sound`；
  无 `sorryAx`、无自定义公理、无 `native_decide`、无 Mathlib。

**Lean 里只参数化了成本轴。** 其余候选轴（回合内顺序、新市民、宜居、食物篮、两种取整）固定在基线假设上；
Python 搜索器给出的 128 组 θ 候选（包络估计 `[20, 25]`）全部只是**搜索估计，未经证明**。

### 通用引擎与合成基准

- 通用有限期可达性引擎：合法动作枚举必须具有 soundness / completeness 证明。
- 精确步数可达状态枚举，并证明枚举与数学可达性双向等价。
- 合成城市基准（BMK-v0）：最早第 **5** 步完成，最优操作序列唯一。该基准刻意非 Civ6 形状，
  **不得**与 `M_MVP` 的回合数混排，也不构成任何游戏最优主张。
- Python 搜索器 `search/synthetic.py`，28 项自测；Lean 与 JSON fixture 自动对照，47 项检查。

## 运行

需要 **Lean 4.25.0**、Lake 和 Python 3（仅标准库，不需要 Mathlib）。

### 使用 elan

安装 [elan](https://github.com/leanprover/elan)，确保 `lean` / `lake` 在 PATH 中。项目的 `lean-toolchain` 会选择指定版本。

```bash
lake build
python3 search/synthetic.py --self-test
python3 search/synthetic.py --check-fixture
```

### 使用项目本地工具链

可将官方 [Lean 4.25.0 Linux 发行包](https://github.com/leanprover/lean4/releases/tag/v4.25.0) 解压为：

```text
.tools/lean-4.25.0-linux/
```

`.tools/` 不入库。随后运行：

```bash
scripts/lean-env lake build
python3 scripts/check-synthetic.py
```

### 条件 MVP 模型

```bash
# 编译模型、算术核心与最优性模块
scripts/lean-env lake build Civ6Verify.Bounds.MvpOptimality

# Python 侧语义可执行文件（不受信任，仅候选生成与重放）
python3 search/mvp.py --self-test        # 28 项自测
python3 search/mvp.py --check-fixture    # 重放冻结 fixture，确认 N=20/25
python3 search/mvp.py --all              # 128 组 θ 搜索估计（约 3.5 分钟）
```

`#print axioms` 探针可确认公理足迹；脚本用法见 `scripts/audit-axioms.py --help`。

### 验证流水线状态

- `scripts/verify.sh` 已完成本地集成验收：构建、两套模型各 28 项自测、fixture 检查、
  synthetic 47 项交叉检查、MVP 2239 项交叉检查及 7 项负向测试、公理审计全部通过。
- 审计覆盖 686 个公开定理常量及 21 个私有生成定理，只使用批准的 `propext` / `Quot.sound`。
- MVP 对照是实现漂移检测，不代替 Lean 最优性证明，也不提供真实游戏一致性证据。
  完整说明见 [`mvp/VALIDATION.md`](mvp/VALIDATION.md)。
- MVP 提交 `1eb5125` 的 GitHub CI 已通过；新增成果的远端状态以对应提交的 Actions 结果为准。

## 目录

```text
Civ6Verify/Reachability/Finite.lean       通用可达性、完备性与最优性
Civ6Verify/Scenarios/Synthetic.lean       合成城市模型与已验证定理
Civ6Verify/Model/Mvp.lean                 条件基线模型 M_MVP（单城 / 4 格 / 首个移民）
Civ6Verify/Bounds/MvpArithmetic.lean      σ 算术核心（与模型解耦）
Civ6Verify/Bounds/MvpOptimality.lean      OptimalAt 20/25 的模型侧下界
search/synthetic.py                      合成基准搜索、重放与测试
search/mvp.py                            MVP 语义可执行文件（不受信任）
fixtures/synthetic-v0.json               冻结的合成场景与预期结果
fixtures/mvp-baseline.json                冻结的 MVP 可执行输出（含 128 θ 估计）
fixtures/mvp-rule-candidates.json         v2.1 规则/候选契约（机器可读）
scripts/check-synthetic.py                实际 Lean 输出与 synthetic fixture 对照
scripts/check-mvp.py                      MVP 的 Lean 输出与 Python/fixture 交叉检查
scripts/audit-axioms.py                   全库公理与禁用 token 审计
mvp/RULE-CONTRACT.md                      v2.1 规则契约
mvp/RESULTS.md                            MVP 结果、下界推导与未决项（详版）
SCOPE.md                                  当前声明范围与未完成项
research/                                 设计、规则研究、审查与验证报告
```

研究报告记录了开发过程和历史状态；其中部分文件（如 `mvp/LOWER-BOUND.md`、`mvp/LEAN-MODEL.md`、
`research/MVP-VALIDATION.md`）写于下界桥接完成之前，状态措辞已过时。发生冲突时，
以当前源代码、测试结果和 `SCOPE.md`、`mvp/RESULTS.md` 的保守范围为准。机器环境调查报告不公开。

## 后续成果：稳健性、政策突破与人口策略

- **机制稳健性（Lean）**：单独修改人口 3 阈值、新市民当步生产、生产十分位截断后，两个成本的最优性仍为 20／25 步。目前认证 8 个配置点，不代表任意组合或全部 128 组。见 [`mvp/ROBUSTNESS.md`](mvp/ROBUSTNESS.md)。
- **政策突破（Lean）**：假设初始已装备 Urban Planning，且其 +1 基础生产力按模型乘数结算，可在 18／22 步完成，严格突破无政策基线下界。未证明政策变体自身最优，也不包含解锁成本。见 [`mvp/POLICY.md`](mvp/POLICY.md)。
- **人口策略（搜索＋Lean 见证）**：有限模型搜索发现人口 3 的收益存在窗口与间隙，而非单调分界。成本 13861（百分之一生产力单位）有经 Lean 验证的 29 步路线；“首个分界”和“严格优于全部人口 2 路线”仍只是搜索结果，缺少对应下界证明。见 [`mvp/COST-FRONTIER.md`](mvp/COST-FRONTIER.md)。

上述模块均纳入主构建与公理审计；政策和成本探索测试也纳入 `scripts/verify.sh`。仍然没有真实游戏实测背书。

## 下一步

- 钉死游戏构建，把 `[U]` / `[D*]` 证据升级为可复现的实测；目前 `[V] = 0` 是最主要的缺口。
- 已有 MVP 提交的 GitHub CI 通过；后续新增模块需随提交重新执行 CI。
- 把其余候选轴参数化进 Lean，或证明它们在 Θ 上惰性，从而收缩 `[20, 25]` 搜索包络。
- 用公开资料建立并校准更多真实规则，对取整、增长与完工顺序等不确定项给出判别式实测。
- 从具体最优解中提炼适用于一类开局的瓶颈定理。

**Lean 证明保证结论符合模型，不自动保证模型符合真实游戏。**

本项目不包含文明 VI 游戏资源，与游戏发行商无关联。
