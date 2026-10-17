# civ6-lean4

用 Lean 4 探索《文明 VI》运营极限的形式化证明。

> **当前是早期证明框架，不是文明 VI 模拟器。** 已验证结果全部来自人为设计的合成城市基准，不代表任何真实游戏开局的最优回合。真实文明 VI 规则模型尚未实现。

## 想证明什么？

给定明确的规则、初始城市和允许操作，同时证明：

1. **做得到**：存在第 N 回合完成目标的合法路线。
2. **不能更快**：所有合法操作序列都无法在 N 之前完成目标。

计划从首个移民开始，逐渐扩展到建立第二城、第三城，以及资源瓶颈与突破下界的机制。

## 当前成果

- 通用有限期限可达性引擎：合法动作枚举必须具有 soundness / completeness 证明。
- 精确步数可达状态枚举，并证明枚举与数学可达性双向等价。
- 可行路线、下界与最优性证书。
- 合成城市基准：最早第 **5** 步完成，最优操作序列唯一。
- Python 搜索器，28 项自测；Lean 与 JSON fixture 自动对照，47 项检查。
- 核心和合成场景的已审计定理仅使用标准 `propext` / `Quot.sound`（或不依赖公理），无 `sorryAx`、自定义公理或 `native_decide`。

合成基准中的粮食、人口、生产和移民数值均为证明工程设计，不是文明 VI 规则。Python 搜索不受信任；最终最优性由 Lean 检查。

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

自动对照脚本使用项目本地 wrapper；具体参数见 `python3 scripts/check-synthetic.py --help`。NixOS 上运行官方 Linux 二进制可能需要额外的动态加载器支持。

## 目录

```text
Civ6Verify/Reachability/Finite.lean  通用可达性、完备性与最优性
Civ6Verify/Scenarios/Synthetic.lean 合成城市模型与已验证定理
search/synthetic.py               Python 搜索、重放与测试
fixtures/synthetic-v0.json         冻结的合成场景与预期结果
scripts/check-synthetic.py         实际 Lean 输出与 fixture 对照
PLAN.md                           分阶段计划
RULES.md                          规则证据、候选语义和验证要求
SCOPE.md                          当前声明范围与未完成项
research/                         设计、规则研究、审查与验证报告
```

研究报告记录了开发过程和历史状态；发生冲突时，以当前源代码、测试结果和 `SCOPE.md` 的保守范围为准。机器环境调查报告不公开。

## 下一步

- 用公开资料选择明确版本，建立受限的真实文明 VI 规则模型。
- 对取整、增长与完工顺序等不确定项保留显式假设，并寻找判别式实测。
- 得到首个真实开局的可达性与下界证明。
- 从具体最优解中提炼适用于一类开局的瓶颈定理。

**Lean 证明保证结论符合模型，不自动保证模型符合真实游戏。**

本项目不包含文明 VI 游戏资源，与游戏发行商无关联。
