# RULES.md — 规则契约 v0（首个合成参数化模型 M0）

归属：本文件只由本任务 owner 维护。
角色：`research/RULES-RESEARCH.md` 是**证据汇编**；本文件是**契约**——可编码的规则、状态标注、语义开关、验收标准与判别式 fixture。
适用范围：M0/M1/M2/M3 的**合成模型** `M0(θ)`。它**不**断言文明 VI 的真实数值、真实最优回合数或任何 `N`。

> **本文件的第一条事实：当前 [V]（游戏内实测）计数为 0。**
> 本机没有安装游戏（见 `research/ENVIRONMENT.md`），因此没有任何一条规则是"在已钉版本的游戏里观测到的"。
> 所有"看起来像游戏事实"的句子，在本文件中都只是 `[A]/[D]/[C]/[I]` 级材料或参数。

---

## 0. 元规则（违反即视为审计失败）

- **M1**：任何进入 `Civ6Verify/Rules/` 的常量必须带 Rule ID + 证据标签 + `RULES.md` 章节号。无 ID 常量禁止入库。
- **M2**：v0 的所有定理都是 `M0(θ)` 内的定理。报告标题与定理名不得出现"文明 VI 的最优解"字样；只允许"模型 M0(θ) 中的 `OptimalAt`"。
- **M3**：未决语义**不得**用"看起来合理"的默认值填死。每个未决项必须二选一：进入 θ（可枚举、可出 envelope），或配一个可判定的 fixture。两者皆无者标 `[U-BLOCK]`，禁止进入模型。
- **M4**：标注升级必须留痕（§13 变更日志）。不允许静默把 `[C]` 写成事实。
- **M5**：不得因为"这个机制在最优路线里大概用不到"而删除动作或机制；只能把它列为**明确排除**并给出 §8 的后果分析。

---

## 1. 证据标签

| 标签 | 定义 | 升级条件 | 当前计数 |
|---|---|---|---|
| `[V]` | 在**已钉版本**的实机中直接观测（截图 + 回合号 + build hash，或存档） | — | **0** |
| `[D]` | 从**已钉版本**的游戏数据文件直读（`Base/Assets/Gameplay/Data/*.xml` 等） | 需要 buildid + 文件 hash | 0（仅有未钉版本的 wiki 数据模块，记作 `[D*]`） |
| `[D*]` | 社区镜像的游戏数据导出，**版本不明**（如 fandom `Module:Data/Civ6/Base/*`） | 与 `[D]` 对照一致后升级 | 12 |
| `[A]` | 官方手册 / 官方 Civilopedia 规则文本 | 与 `[D]` 对照后可作为语义证据 | 5 |
| `[C]` | 社区资料、实测报告、modder 说明 | 至少一条可定位来源；只能当假设 | ~14 |
| `[I]` | 由上述材料推导（公式、表格、推论） | 推导步骤必须写明 | ~12 |
| `[U]` | 未决；必须参数化 + fixture | fixture 落地后升级 | 20 |

**关键纪律**：`[D*]` 不等于 `[D]`。wiki 数据模块没有版本标注，已证明会发生漂移（移民递进参数 20→30）。凡是从 `[D*]` 读到的数值，在 M0 里一律视为"候选值"，其不确定性由 θ 承担。

---

## 2. 模型 M0(θ) 的签名

```
σ : Scenario                      -- 固定场景（§2.2）
θ : Config                        -- 语义开关（§9），承担全部 [U]
S : Type                          -- 状态
A : Type                          -- 动作
step   : Config → Scenario → S → A → Option S      -- 非法动作返回 none
Goal   : S → Prop                                  -- 单调历史谓词
reach  : Config → Scenario → Nat → Finset S        -- 逐层完备可达集
N(θ)   : Nat  :=  min { t | ∃ s ∈ reach t, Goal s }   -- 存在性由证书给出
OptimalAt(θ, n) := (∃ s ∈ reach n, Goal s) ∧ (∀ t < n, ∀ s ∈ reach t, ¬ Goal s)
```

- `N(θ)` **不是**本文件断言的值。`RULES.md` 不写任何具体回合数；任何"N = …"的句子必须在 `reports/` 中由 `OptimalAt(θ, N)` 的 Lean 定理支撑，并显式写出 θ。
- 时间约定沿用 `PLAN.md §2.1`：`t = 0` 为初态（建都后、第一次 `EndTurn` 前），`t = k` 为完成 k 次结算后的状态。与 UI 回合号的映射见 `R-ORD-4`（未决）。

### 2.1 状态（v0 最小集）

```
S := { t : Nat, pop : Nat, food : Nat, prog : Nat, trained : Nat, hasSettler : Bool }
```

- `food`、`prog` 是**定点整数**，单位为 1/100（见 §4）。
- `trained` 是单调计数器（`PLAN.md §2.1`）：完成后不回退，即使移民单位被删除/移动。
- `hasSettler` 只用于报告，不参与 `Goal`。
- 不建模：单位位置、地图、金币、信仰、文化、科技、市政、政策、边界、其他城市。

### 2.2 场景 σ（合成，不是真实地图）

v0 场景必须是**显式数据**，字段如下；任何字段缺省即视为规格不完整：

| 字段 | 含义 | v0 默认（合成） |
|---|---|---|
| `centerF, centerP` | 城市中心地格产出（已含下限规则） | `2, 1`（平坦草原，避免 §5.5 的丘陵歧义） |
| `palaceF, palaceP` | 宫殿产出 | `0, 2`（`R-CITY-4`，`[C]`） |
| `palaceHousing` | 宫殿住房 | `1`（`R-CITY-4`） |
| `palaceAmenity` | 宫殿宜居 | θ 参数 `{1, 0}` |
| `freeCityAmenity` | 每城免费宜居 | θ 参数 `{1, 0}`，默认 1 |
| `waterHousing` | 水源住房 | `5`（淡水，`R-HOUS-1`） |
| `tiles : List (f, p)` | 可工作地格（不含中心） | 见下 |
| `startPop` | 初态人口 | `1`（`R-CITY-5`，`[C]`） |
| `startFood` | 初态储粮 | `0`（`[U]`，`R-ORD-4`） |
| `startProg` | 初态生产进度 | `0` |
| `startTrained` | 初态已训练移民数 | `0`（起手免费移民**不计**，`R-SET-1`） |

合成地格集（v0 默认，刻意小且可手算；数值是**模型参数**，不是地形事实）：

```
T = [ (2,0),   -- 草原
      (1,1),   -- 平原
      (2,1),   -- 草原丘陵
      (1,2),   -- 平原丘陵
      (0,0) ]  -- 休耕地（用于"停增长"与单调性论证）
```

场景设计约束（进 Lean 前必须检查）：
- **S-1**：中心地格必须是平坦地形。原因：`R-CITY-3` 的丘陵中心规则在来源内部自相矛盾（见 §5.5、§14-C2），会让 1P 的差异污染全模型。
- **S-2**：地格集必须允许在建模人口范围内构造"盈余恰为 0"的分配，否则"停止增长以避免宜居掉档"这一策略不可表达，模型会被迫增长，`N` 被系统性推高。
- **S-3**：地格集必须含一个 `(0,0)` 地格，使"新增人口不产出"与"新增人口产出"两种 θ 都可表达（§9 的松弛纪律）。
- **S-4**：不得含资源、地貌、河流、自然奇观、部落村庄；场景是数据，不是地图。

---

## 3. 版本固定（规则集 ≠ build）

| ID | 要求 | 状态 | 证据 / 说明 |
|---|---|---|---|
| R-VER-1 | 规则集 = 原版 Base，不启用 R&F / GS | `[U]` | 两资料集在宜居度上数值完全不同（§5.4），必须钉死 |
| R-VER-2 | 必须记录 Steam `buildid` + `Base/Assets/Gameplay/Data/{GlobalParameters,Units,Buildings,Policies}.xml` 的 hash | `[U]` | 已证明漂移：移民 `CostProgressionParam1` 发售版 20、后期 30（§14-C5） |
| R-VER-3 | 游戏速度 = Standard（`CostMultiplier=100`） | `[D*]` | `Module:Data/Civ6/Base/GameSpeeds`；速度会同时缩放增长阈值与产能成本 |
| R-VER-4 | 难度 = Prince，且需确认人类侧无增长/产能修正 | `[U]` | 手册只说难度影响"the speed at which your civilization grows"，未说人类侧；见 FX-DIFF |
| R-VER-5 | 文明/领袖 = 其能力对本模型全部量（食物、产能、人口、住房、宜居、增长、移民成本）无作用 | `[U]` | 必须在报告中逐条列出能力文本并说明为何无作用；不允许"随便挑一个" |
| R-VER-6 | DLC / MOD / 游戏模式全部关闭 | `[U]` | 模式（如 Monopolies）会改住房/宜居 |
| R-VER-7 | 地图固定、无部落村庄；建都地格无村庄（建都会自动激活） | `[U]` | `City (Civ6)`：建城时相邻格村庄被激活 |
| R-VER-8 | 起始时代 = Ancient（后期时代会送住房与宜居） | `[U]` | `CitySupport.lua` 暴露 `GetAmenitiesFromStartingEra()` |

**结论**：在 R-VER-1/2 解除前，任何证书只能写"原版规则集的某次导出"，不能写"文明 VI 原版"。

---

## 4. 数值核（禁止浮点）

### 4.1 表示

- 全部以 **1/100 为单位的 `Nat`/`Int`** 存放（`food100`, `prog100`, 阈值 `T100`，倍率以有理数 `num/den` 表示并在 `step` 内做**显式**取整）。
- 禁止 `Float`/`Float32`；禁止依赖 `Nat` 除法默认行为而不写取整策略。
- **比例尺充分性义务**：必须证明在 θ 与 σ 下，`step` 产生的所有值都是 1/100 的整数倍，或在声明的取整点之外不发生截断。理由：整数盈余 × 1.1 → 1/10 栅格；× 0.5 → 1/2；× 0.25 → 1/4；× 1.05 → 1/20；以上都在 1/100 内闭合。只有"两个增长修正相乘"（θ 组合律）与"1.1 × 0.25"会需要 1/1000；若可达集里出现这类组合，比例尺必须升级或该分支被证明不可达。

### 4.2 增长阈值

基准公式（`[C]` + `[D*]` 参数，`R-GROW-1`）：

```
T(n) = 15 + 8·(n−1) + (n−1)^1.5        n = 当前人口
```

`T(n)` 在 n ≥ 3 时一般**不是**整数，因此阈值进入模型时必须选一个**截断模式**（`θ.thresholdMode`）：

| n | T(n) 精确值 | `floor`（食物单位） | `exact`（1/100 单位） | 维基整数表 |
|---|---|---|---|---|
| 1 | 15.000000 | 15 | 1500 | 15 |
| 2 | 24.000000 | 24 | 2400 | 24 |
| 3 | 33.828427 | 33 | 3383 | 33 |
| 4 | 44.196152 | 44 | 4420 | 44 |
| 5 | 55.000000 | 55 | 5500 | 55 |
| 6 | 66.180340 | 66 | 6619 | 66 |
| 7 | 77.696938 | 77 | 7770 | 77 |
| 8 | 89.520259 | 89 | 8953 | 89 |
| 9 | 101.627417 | 101 | 10163 | 101 |
| 10 | 114.000000 | 114 | 11400 | 114 |

- 维基 30 项整数表与 `floor(T(n))` **逐项一致**（已用脚本核对 30/30）。但这只说明"表被取整过"，不说明"游戏取整"。
- `[I]` 义务：若 θ 选 `exact`，Lean 中用有理区间夹逼（如 `3382/100 < T(3) < 3383/100`）并把比较化为整数比较 `food100 ≥ 3383`；不得引入浮点。
- v0 只需要 n ≤ 6（若模型确实不越过 6，见 `R-GROW-6` 的可达性守卫）。

### 4.3 取整点清单（全部参数化）

| 取整点 | 备用取值 | 默认（v0） | 依据 |
|---|---|---|---|
| 增长阈值 | `floor` / `exact` | 无默认，两者都算 | `[U]`，FX-TH |
| 修正后盈余的累加 | 精确 / 截到 0.1 / 截到 1 | 精确 | `[U]`，FX-PROD-FRAC 同族 |
| 产能倍率后的累加 | 精确 / 截到 0.1 / 截到 1 | 精确 | `[U]`，FX-PROD-FRAC |
| 生产完成比较 | `prog ≥ cost` | 精确 | `[I]` 无歧义 |
| 溢出结转 | 结转 / 丢弃 | 结转 | `[C]` `R-PROD-3` |

---

## 5. 规则卡

格式：ID｜规则陈述｜状态｜证据｜θ 参数（若有）｜影响（错的后果）。

### 5.1 食物与消耗

| ID | 规则 | 状态 | 证据 |
|---|---|---|---|
| R-FOOD-1 | 每市民每回合消耗 **2 食物** | `[D*]`+`[A]` | `CITY_FOOD_CONSUMPTION_PER_POPULATION=2`；手册 p.104 |
| R-FOOD-2 | 盈余 = 城市食物产出 − 消耗；可为负 | `[A]` | 手册 p.104–105 |
| R-FOOD-3 | 盈余（经增长修正）累加进"食物篮子"；篮子 ≥ 阈值 → 人口 +1 | `[A]`+`[C]` | 手册 p.105；`Population (Civ6)` |
| R-FOOD-4 | 增长后篮子**清空**（不是减阈值） | `[A]`；备选 `[U]` | 手册原文 "the city growth bucket is then emptied"；θ `basketOnGrowth ∈ {Zero, Subtract}` |
| R-FOOD-5 | 负盈余 → 先耗尽篮子，再掉人口（饥饿） | `[C]` 含糊 | v0 **禁止**产生负盈余的动作（§7），见 §8 |

**R-FOOD-4 的影响**：`Subtract` 在 v0 中通常与 `Zero` 等价（盈余远小于阈值），但连续增长的 M5 场景会分叉。v0 必须两者都算一次以确认"惰性"。

### 5.2 增长

| ID | 规则 | 状态 | 证据 |
|---|---|---|---|
| R-GROW-1 | 阈值公式 `15 + 8(n−1) + (n−1)^1.5` | `[C]`+`[D*]` | CFC 公式帖；`CITY_GROWTH_{THRESHOLD,MULTIPLIER,EXPONENT} = 15/8/1.5` |
| R-GROW-2 | 阈值是否取整 | **`[U]`** | 见 §14-C1：小数表只是公式复算，不是观测 |
| R-GROW-3 | 阈值表 n=1..10 | `[I]` | §4.2 |
| R-GROW-4 | 增长修正作用于**盈余**（不是阈值） | `[D*-ui]`+`[C]` | 游戏自带 UI：`foodGainNextTurn = foodSurplus * GetOverallGrowthModifier()`（`CitySupport.lua`）。θ `growthBase ∈ {surplus, threshold}`，默认 `surplus` |
| R-GROW-5 | 一次结算最多长 1 级 | `[U]` | θ `multiGrowth ∈ {off, on}`，v0 默认 off；仅在"篮子溢出保留 + 盈余 ≥ 下一阈值"时才可分叉 |
| R-GROW-6 | 多个增长修正如何合成（乘 / 加） | **`[U]`** | θ `compose ∈ {product, additive}`。v0 只在住房与宜居**同时非 1.0** 时承重（见下表） |
| R-GROW-7 | 修正后盈余的取整点 | **`[U]`** | θ `growthRounding ∈ {exact, trunc10, trunc1}` |

**R-GROW-6 的可达性守卫（重要）**：在 σ 的淡水首都下，把"住房档 × 宜居档"化简为**只依赖人口的表** `g(pop)`；只要可达集内没有同时激活两个修正的人口，`compose` 就是惰性参数。表如下（`[I]`，由 §5.3/§5.4 相乘得到；"加"变体由 θ 计算）：

| pop | 住房档（housing=6） | 宜居 A=2 | g（A=2, 乘） | 宜居 A=1 | g（A=1, 乘） |
|---|---|---|---|---|---|
| 1 | 1.00 | Happy 1.10 | 1.10 | Happy 1.10 | 1.10 |
| 2 | 1.00 | Happy 1.10 | 1.10 | Happy 1.10 | 1.10 |
| 3 | 1.00 | Happy 1.10 | 1.10 | Content 1.00 | 1.00 |
| 4 | 1.00 | Happy 1.10 | 1.10 | Content 1.00 | 1.00 |
| 5 | 0.50 | Content 1.00 | 0.50 | Displeased 0.85 | **0.425** |
| 6 | 0.25 | Content 1.00 | 0.25 | Displeased 0.85 | **0.2125** |
| 7 | 0.25 | Displeased 0.85 | **0.2125** | Displeased 0.85 | **0.2125** |

加粗格 = 两个修正同时激活 = `compose` 从惰性变为承重：**A=2 时只有 pop 7（及以上），A=1 时从 pop 5 起**。Lean 侧必须有一条**守卫定理**:`∀ s ∈ reach t, pop s ≤ 6`(A=2)或 `≤ 4`(A=1);若不成立,证书必须声明 `compose` 已承重。

### 5.3 住房

| ID | 规则 | 状态 | 证据 |
|---|---|---|---|
| R-HOUS-1 | 淡水 5（+宫殿 1 = 6）；海岸 3；无水 2 | `[D*]`+`[C]` | `CITY_POPULATION_{RIVER_LAKE,COAST,NO_WATER}=5/3/2`；宫殿 `Housing=1` |
| R-HOUS-2 | `left = housing − pop`：`≥2 → 1.0`；`=1 → 0.5`；`0..−4 → 0.25`；`≤−5 → 0` | `[A]`+`[C]` | Civilopedia standard-rules；Housing 页表；Population 页复述 |
| R-HOUS-3 | `LEFT_ZERO=-4` 的严格性（`≤−4` 还是 `<−4` 归零） | `[I]` 倾向严格 | 两张独立 wiki 表都说 `−4` 仍是 25%、`−5` 才 0%；θ `zeroStrict ∈ {on, off}`，默认 on |

**R-HOUS-2/3 的影响**：v0 淡水首都下，pop ≤ 4 完全不受住房约束（`left ≥ 2`）。因此**v0 若把人口限制在 ≤4，住房整块可以从模型里消去**——但这是一个必须被证明的守卫条件，而不是假设（因为"不长到 5"正是策略变量，见 `R-AMEN-7`）。

### 5.4 宜居度（**不要照抄"首都恒 Happy"**）

| ID | 规则 | 状态 | 证据 |
|---|---|---|---|
| R-AMEN-1 | 每城免费宜居 **1**（原版；GS 取消） | `[D*]`+`[C]` | `CITY_AMENITIES_FOR_FREE=1`；GS 模块为空；`Amenities (Civ6)` "In GS, cities no longer start with a free Amenity" |
| R-AMEN-2 | 宫殿 +1 宜居（当前数据；GS +2） | `[D*]`+`[C]` | `BUILDING_PALACE{Entertainment=1}`；Palace 页 "+1 (GS +2)" |
| R-AMEN-3 | 需求 `req(pop) = max(0, ⌊(pop−1)/2⌋)` | `[A]`+`[D*]` | 手册 p.95 "1 Amenity for each 2 Population, starting at 3"；`CITY_POP_PER_AMENITY=2`；与 `⌈pop/2−1⌉` 对所有 pop 等价 |
| R-AMEN-4 | 等级 = f(可用 − 需求)：`≥3` Ecstatic；`1..2` Happy；`0` Content；`−1..−2` Displeased；`−3..−4` Unhappy；`−5..−6` Unrest；`≤−7` Revolt | `[A]`+`[C]` | 手册 p.95；Amenities 页原版表 |
| R-AMEN-5 | Happy：增长 +10%，**非食物**产出 +5%（食物不吃这个加成） | `[A]` | 手册 p.95；CFC 产出报表观察（仅产能/金币显示 5%） |
| R-AMEN-6 | 需求为 0 时是否仍参与比较 | `[I]` 是 | UI：`AmenitiesNetAmount = GetAmenities() − GetAmenitiesNeeded()`，纯差值，无"需求为 0 则强制 Content"分支 |
| R-AMEN-7 | **pop 3–4 的等级取决于可用宜居总数 A** | **`[U]`** | 见下 |

**R-AMEN-7 的真实分叉（这是本文件对研究报告最重要的一处纠正）**：

> 冲突证据（必须保留）：2016 年发售前的社区汇总称 "The Capital starts with 1 amenity by default …, but the other cities start with 0 amenities"（`[C-weak]`，预览版）。这与 `CITY_AMENITIES_FOR_FREE=1` 的当前数据导出以及 GS 改版说明都冲突。三种读数（免费 1 + 宫殿 0 / 免费 0 + 宫殿 1 / 免费 1 + 宫殿 1）在 pop 1–2 上**都**给出 Happy，因此只有 pop 3 能判别。这正是 θ5 存在的理由。

| A = 免费 + 宫殿 | pop 1–2 | pop 3–4 | pop 5–6 | pop 7–8 |
|---|---|---|---|---|
| **2**（1+1，当前数据导出） | Happy | **Happy** | Content | Displeased |
| **1**（1+0，2016 发售版；或 0+1） | Happy | **Content** | Displeased | Displeased |
| **0**（0+0，假想） | Content | Displeased | Displeased | Unhappy |

- `CITY_AMENITIES_FOR_FREE` 的存在只能确定"原版每城有 1 点免费宜居"；**宫殿那 1 点是后加的**。R&F/GS 宜居度改版补丁注记原文："**Removed the free population amenity. Added an amenity to the palace.**"（社区转述，`[C]`）。因此发售版的 A 很可能是 **1**（构成是 1+0 还是 0+1 仍未定），而打了后续补丁的 build 是 **2**。
- 后果：**"首都从第 1 回合起就带 +5% 产能"这句话只在 A=2 时对 pop 3–4 成立；在 A=1 时 pop 3–4 是 Content，产能与增长都没有乘数。** 大多数首移民产能恰恰在 pop 3–4 期间累进。
- 因此 v0 必须把 `A ∈ {2, 1}` 作为 θ 的承重参数，并由 **FX-AM3（pop=3 的等级）** 判别。pop=1/2 的观测**无法**区分 A=2 与 A=1（两者都是 Happy），这是研究报告 F3 的设计缺陷（§14-C3）。
- pop 1–2 为 Happy 在 A ≥ 1 时成立（`[I]` 高置信），这是 v0 可以安全使用的唯一宜居结论。

### 5.5 城市中心与宫殿

| ID | 规则 | 状态 | 证据 |
|---|---|---|---|
| R-CITY-1 | 中心地格产出下限：食物 `max(地形, 2)`、产能 `max(地形, 1)`（逐项，先于加成） | `[D*]`+`[C]` | `YIELD_{FOOD,PRODUCTION}_CITY_TERRAIN_REPLACE=2/1`；City 页 |
| R-CITY-2 | 中心地格**免费工作**，不占市民 | `[C]` | City 页 "always worked and does not require any citizen" |
| R-CITY-3 | 平原丘陵中心是否再 +1 产能 | **`[U]`** | 同一页自相矛盾：正文说 "Plains Hills add an additional point of Production"，但同页算例给平原丘陵中心 **2F/2P**（不是 3P）。**v0 规避**：中心用平坦地形（S-1），θ `centerHills ∈ {maxOnly, plusOne}` 仅供 M5 |
| R-CITY-4 | 宫殿：+2 产能、+1 住房、+1 宜居（+5 金 / +1 文化 / +2 科技不入模型） | `[C]`+`[D*]`（住房/宜居为 `[D*]`，+2 产能为 `[C]`） | `BUILDING_PALACE` 只有 `Housing=1; Entertainment=1`；+2 产能在产出表里，本机无法直读，故只能 `[C]` |
| R-CITY-5 | 新城市初始人口 = 1 | `[C]` | City 页 |

**R-CITY-4 的审计缺口**：`BUILDING_PALACE` 的 XML 片段不含 `+2 Production`（产出在另一张表，本机取不到）。因此"宫殿 +2 产能"是 `[C]`，必须由 **FX-CAL** 用"总产出 − 已工作地格"反解。若反解出 3 或 1，§2.2 的 `palaceP` 立即改。

### 5.6 市民分配

| ID | 规则 | 状态 | 证据 |
|---|---|---|---|
| R-CIT-1 | 每市民工作 1 个地格；同一地格不可被两人工作 | `[D*]`+`[A]` | `CITY_NORMAL_PLOT_WORKER_CAPACITY=1`；手册 p.104 |
| R-CIT-2 | 中心地格不可分配（免费产出） | `[C]` | 同 R-CITY-2 |
| R-CIT-3 | 每回合可手动重分配 | `[A]` | 手册 p.104 "MANUALLY ASSIGNING CITIZENS" |
| R-CIT-4 | 重分配在同一回合结算中是否生效 | **`[U]`** | θ `assignTiming ∈ {sameTurn, nextTurn}`，默认 `sameTurn`（松弛端） |
| R-CIT-5 | 新市民在出生当回合是否产出 | **`[U]`** | θ `newCitizen ∈ {none, best}`；`best` 是松弛端（允许玩家为新市民挑最优空闲格） |
| R-CIT-6 | 是否允许市民闲置（工作 < pop 人） | **`[U]`** | θ `idle ∈ {allow, forbid}`；`allow` 是松弛端（真实游戏由总督自动分配，但"任何分配"都是玩家的可选项；"闲置"未必可达） |

**松弛纪律（§9 的核心）**：`R-CIT-4/5/6` 的默认值全部取"对玩家最有利"的一端。这些端是真实行为的**超集**，因此用于**下界**是保守的；但它们不能用于**可达性**证明，除非确认与真实一致。`OptimalAt` 只在"松弛端 = 假定精确端"时才能宣称。

### 5.7 生产

| ID | 规则 | 状态 | 证据 |
|---|---|---|---|
| R-PROD-1 | 每回合结算时累加一次产能 | `[C]`+`[D*-ui]` | Production 页；UI `ProductionPerTurn` |
| R-PROD-2 | 切换建造不清零进度 | `[C]` | Production 页 "Progress is not lost" |
| R-PROD-3 | 溢出进入下一项（v0 只有一项可建，仅影响"Idle"分支） | `[C]` | Production 页 |
| R-PROD-4 | 产能乘数（Happy +5%）后的取整点 | **`[U]`** | θ `prodRounding ∈ {exact, trunc10, trunc1}`，默认 `exact`。研究报告引用的"9 → 9.4"**不能**区分"截到 0.1"与"浮点显示截断"（`9*1.05 = 9.45` 的二进制近似是 9.4499…，`%.1f` 同样给 9.4） |
| R-PROD-5 | 产能乘数作用于"城市总产能"（含宫殿） | `[I]` | 未见反例；FX-CAL 同回合可复核 |

### 5.8 移民

| ID | 规则 | 状态 | 证据 |
|---|---|---|---|
| R-SET-1 | 第一个**训练**移民成本 = 80 或 110（起手免费移民是否计入 `PREVIOUS_COPIES`） | **`[U]`** | 两条独立 `[C]`（Sullla "80 then 110 then 140"；Skymods 明确写出 `cost = 30·N + 80`，`N=已训练数`，1st=80）；但 wiki Settler 页写 `30(x+1)+50` 且 **x 含起手移民**（⇒ 首个 110）。θ `settlerBase ∈ {80, 110}`，默认 **80** |
| R-SET-2 | `CostProgressionParam1 = 30`，**线性加**到基础成本上（不是百分比） | `[D*]`+`[C]` | `UNIT_SETTLER{Param1=30}`。观测到的 80→110 是 **+30 绝对量**（非 ×1.375），因此"线性加"成立；百分比解释要求 104。建造者 `Param1=4` 只作为"参数量级与线性解释相容"的旁证，**不**断言其具体成本序列 |
| R-SET-3 | **v0 中递进参数完全惰性** | `[I]` | 目标只要求 `trained ≥ 1`，所以只有 k=0 的成本进入模型。递进只在 M5（第二个移民）承重 |
| R-SET-4 | 需人口 ≥ 2 才能建造 | `[A]`+`[D*]` | 手册 p.105；`PrereqPopulation=2` |
| R-SET-5 | 完成时人口 −1 | `[A]`+`[D*]` | 手册 p.105；`PopulationCost=1` |
| R-SET-6 | 无科技前置 | `[D*]` | `UNIT_SETTLER` 无 `PrereqTech` |
| R-SET-7 | 生产移民期间城市**照常增长**（不是 Civ5 的冻结） | `[C]` | 无权威来源；`[C]` 级轶事 + 反证：若冻结，社区不会讨论"完成移民时人口没掉"（§14-C6）。**必须 FX-SG** |
| R-SET-8 | 完成 −1 人口时食物篮子**保留** | `[C]` | Reddit 轶事链："pop 2 建移民后没掉到 1" 的最佳解释是"掉到 1 后用存量食物立刻长回 2"。θ `basketOnSettler ∈ {keep, zero}`，默认 keep |

**R-SET-1 的处置**：默认 80，但证书必须对 80 与 110 各算一次（`θ.settlerBase`）。80→110 的差别是 +30 产能，在早期大约是 5–7 回合，**远超**任何取整歧义，因此 FX-SET-BASE 是所有 fixture 里性价比最高的之一（开局第 1 回合打开生产面板即可）。

### 5.9 回合内顺序（最大未知）

| ID | 规则 | 状态 |
|---|---|---|
| R-ORD-1 | 食物/增长 与 生产/完工 的先后 | **`[U]`**，θ `order ∈ {GrowthFirst, ProductionFirst, Simultaneous}` |
| R-ORD-2 | 消耗用哪个人口（完工 −1 之前还是之后） | **`[U]`**，由 `order` 决定 |
| R-ORD-3 | 完工后是否再做一次增长判定（"掉人口又立刻长回"） | **`[U]`**，θ `postCompletionGrowth ∈ {none, recheck}` |
| R-ORD-4 | 建都当回合是否结算产出 | **`[U]`**，θ `foundingTurn ∈ {produces, not}` → 决定 `t` 与 UI 回合号映射 |
| R-ORD-5 | 初态食物篮子 = 0 | **`[U]`**（低风险），θ `startFood` |

**证据状况**：研究报告 §4.9 的唯一"顺序"来源自述是 **Civ5 外推**（`[C-weak]`），且同一页内部自相矛盾。本文件不接受任何顺序断言，只接受 fixture。

---

## 6. 结算管线（规范性伪代码）

以下伪代码是 `step` 的**唯一**定义；Lean 实现必须逐行对应，任何偏差都是模型 bug。

```
resolve σ θ (s : S) (a : Action) : Option S
-- 前置：legal σ θ s a
-- P1 产出（整数，食物/产能分别求和）
  f := centerF + palaceF + Σ_{t ∈ a.work} tileF t
  p := centerP + palaceP + Σ_{t ∈ a.work} tileP t

-- P2/P3/P4/P5 的相对顺序由 θ.order 决定：
case θ.order of
| GrowthFirst =>
    -- 食物阶段（用结算前人口）
    d  := f − 2·s.pop
    if d < 0 then none                      -- §7：v0 禁止负盈余
    e  := growApply θ d (g θ s.pop)         -- 乘 g；按 θ.growthRounding 取整
    (pop1, b1) := growthStep θ s.pop (s.food + e)   -- 可能 +1；b1 按 θ.basketOnGrowth
    -- 生产阶段（用 pop1；新市民按 θ.newCitizen）
    q  := prodApply θ p (prodMult θ pop1)   -- Happy ⇒ 1.05
    (trained1, prog1, pop2, goal1) := completeStep θ s.trained s.prog pop1 q
    -- 可选的完工后再增长
    (pop3, b2) := if θ.postCompletionGrowth = recheck then growthStep θ pop2 b1 else (pop2, b1)
| ProductionFirst =>
    -- 生产阶段（用结算前人口）
    q  := prodApply θ p (prodMult θ s.pop)
    (trained1, prog1, pop1, goal1) := completeStep θ s.trained s.prog s.pop q
    -- 食物阶段（用 pop1：完工 −1 之后的人口）
    d  := f − 2·pop1
    if d < 0 then none
    e  := growApply θ d (g θ pop1)
    (pop2, b2) := growthStep θ pop1 (s.food + e)
| Simultaneous =>
    -- 两者都用结算前人口；人口净变化在末尾一次性结算
    d  := f − 2·s.pop
    if d < 0 then none
    e  := growApply θ d (g θ s.pop)
    (popG, b1) := growthStep θ s.pop (s.food + e)      -- 只算"是否增长"
    q  := prodApply θ p (prodMult θ s.pop)             -- 不用 popG 的乘数
    (trained1, prog1, popC, goal1) := completeStep θ s.trained s.prog s.pop q
    pop2 := popG + (popC − s.pop)                      -- 增长与 −1 同时生效
    b2 := b1
-- P9 时钟
  return { t := s.t+1, pop := pop2, food := b2, prog := prog1,
           trained := trained1, hasSettler := s.hasSettler ∨ goal1 }
```

关键实现约束：
1. `completeStep` 只在 `prog ≥ settlerCost θ s.trained` 时触发，且要求 `pop ≥ 2`（`R-SET-4`）。
2. `growthStep` 比较 `b ≥ threshold(pop, θ)`，其中 `pop` 是**增长前**人口。
3. `prodMult` 只依赖**当前人口对应的宜居档**（§5.4 表），与住房无关。
4. `g` 只依赖人口（§5.2 表）——这是 σ 的性质，不是普遍规律；M5 双城时必须重新推导。
5. `Simultaneous` 分支的"净人口变化"必须显式定义取整顺序（先加后减与先减后加在 `pop=2` 时结果相同，但在 `pop=2` 且同时增长与完工时都得到 2；需在 Lean 中固定为 `pop + grow − done`，并用测试锁死）。

---

## 7. 动作空间（v0 精确清单）

```
Action := { work : Finset Tile, build : Build }
Build  := Settler | Idle          -- v0 受限建造集合，见 §8
legal σ θ s a :=
     a.work ⊆ σ.tiles                     -- 只能工作已声明的固定地格（Finset 天然无重复）
  ∧ a.work.card ≤ s.pop                    -- 允许闲置（θ.idle，见 R-CIT-6）
  ∧ (a.build = Settler → s.pop ≥ 2)        -- R-SET-4
  ∧ (结算后盈余 ≥ 0)                        -- §7.1，θ.starvation = forbid
```

- 动作粒度为"**一个结算**"：玩家在每次 `EndTurn` 前选一次 `(work, build)`。
- `work` 的数量上界为 `Σ_{k≤pop} C(|tiles|, k)`；v0 默认 `|tiles| = 5`、`pop ≤ 6` ⇒ ≤ 32 种分配 × 2 种建造 = 64 个动作/状态。
- **枚举完备性义务**：`legal s a ↔ a ∈ allActions s`，且 `allActions` 由 `Finset.powerset` 生成（不是手写列表）。

### 7.1 负盈余（饥饿）

v0 把"结算后盈余 < 0"的动作判为**非法**（`θ.starvation = forbid`）。这是**模型限制**，不是游戏规则：
- 后果：v0 的下界是"在禁止饥饿的动作集上"的下界。
- 为什么可接受：饥饿在本模型中没有任何加速机制（它只减人口、减产出）；但"可接受"只是论证，不是证明。§8 把它列为"能力型排除"的边界情形，M5 若要放开，必须先钉死饥饿语义（FX-STARVE）。

---

## 8. 排除机制清单与对下界的影响

**分类原则（本文件的核心方法论点）**：

- **松弛型排除（relaxation-safe）**：真实游戏里只会让玩家**更慢**或**更差**的东西。排除它 = 给模型更多自由度 = 模型是真实行为的超集。因此 `N_model ≤ N_real`，**模型下界可以直接搬回真实游戏**（"真实不可能早于 N"）。
- **能力型排除（capability）**：真实游戏里**多出来**的选项。排除它 = 模型是真实行为的真子集。这时 `N_model ≥ N_real` 完全可能，下界**不能**搬回真实游戏；证书只能写"受限动作集下的下界"。

| # | 排除项 | 类型 | 它会给玩家什么 | 对下界的影响 | 状态 |
|---|---|---|---|---|---|
| X1 | 金币购买移民/建造者 | 能力 | 320 金直接出移民（≈ 跳过 80 产能） | 若可达，`N` 可塌到 1；证书只能声明"无购买" | 未建模金币；需在证书首行声明 |
| X2 | 信仰购买 | 能力 | 同上（信仰购买单位） | 同上 | 无信仰产出，实际为惰性 |
| X3 | 砍伐/收获（Woods/Stone 等） | 能力 | 一次性大量产能 | 可提前数回合；且需要科技（Mining/Masonry）→ 与 X4 绑定 | 需 Builder（X7） |
| X4 | 科技/尤里卡 | 能力 | Pottery→Granary(+2 食物/+2 住房)；Mining→砍伐；Irrigation→？ | 打开 X3 与 X7 | **承重** |
| X5 | 市政/鼓舞 | 能力 | **Code of Laws → Urban Planning：+1 全城产能**；**Early Empire → Colonization：+50% 移民产能** | **最承重的两项**：+1 产能约等于早期 +20%；+50% 直接改成本 | **承重**，必须 M5 首个扩展 |
| X6 | 政策卡/政变政府 | 能力 | 同 X5（政策必须挂在政体上；Chiefdom 自带 1 经济槽） | 同 X5 | 承重 |
| X7 | 建造者与地块改良 | 能力 | Farm +1 食物（Agriculture 是起始科技，可能开局可建） | 50 产能换 +1 食物，通常不划算，但**不能假设** | 需 FX 或论证 |
| X8 | 万神殿/宗教 | 能力 | Religious Settlements = 直接送 1 移民（`N` 可塌到 0）；Fertility Rites = +10% 增长 | 可完全摧毁下界 | 承重 |
| X9 | 部落村庄 | 能力 | 可送移民/人口/金币/信仰；建都格村庄会自动激活 | 随机性 + 可能直接达成 | 场景前置条件：无村庄 |
| X10 | 边界扩张/买地 | 能力 | 更多/更好的可工作地格 | 提高产出上界 | 固定地格集 |
| X11 | 移民移动与建城（第二城） | 能力 | 第二城独立产出；第二城可再造移民 | 完全改变问题 | v0 目标是"训练出"，不是"建城" |
| X12 | 贸易路线/商队 | 能力 | 国内商路 +食物/+产能 | 可提前 | 排除 |
| X13 | 城邦/使者/宗主 | 能力 | 部分城邦给食物/产能/住房 | 可提前 | 排除 |
| X14 | 伟人 | 能力 | 个别伟人给产出 | 可提前 | 排除 |
| X15 | 奇观 | 能力 | Hanging Gardens(+15% 增长)、Temple of Artemis 等 | 可提前 | 排除 |
| X16 | 难度/游戏模式/资料集加成 | 能力 | 人类侧修正（若存在） | 直接改所有倍率 | 固定 Prince + Base |
| X17 | 文明/领袖能力 | 能力 | 视文明而定 | 必须逐条论证惰性 | R-VER-5 |
| X18 | 蛮族/敌方/灾害/掠夺 | 松弛 | — | 只会让玩家更慢 ⇒ 排除后模型更快 ⇒ 下界仍成立 | **安全** |
| X19 | 单位生产（战士/侦察）等其它建造项 | 已用 `Idle` 覆盖 | 占用产能（更慢）；副作用（Monument 文化等）因 X4–X7 已排除而无意义 | 在**建模量**上与 `Idle` 等价 ⇒ 不改变下界；但等价性依赖 X4–X7 | 见下 |
| X20 | 起始时代 > Ancient | 能力 | 送住房/宜居/人口 | 直接改初态 | 固定 Ancient |

**关于 X19 的精确处理**：v0 的 `Build` 只有 `Settler | Idle`。`Idle` 表示"本回合产能不投向移民"（等价于在建别的东西且进度不共享）。这**不是**严格超集：真实游戏里建 Monument/Builder 会产生副作用（Monument +1 文化 → 更快到 Code of Laws → 更快拿 Urban Planning）。但因为 X4/X5/X6 已整体排除（文化/市政/政策不建模），Monument 的副作用在本模型里无意义。因此 `Idle` 对"本模型的量"是充分的。**这一点必须写进证书的适用边界**：`Idle` 的合法性依赖于 X4–X7 的排除。

**下界表述模板**（每个证书必须照抄并填括号）：

> 在模型 `M0(θ)`、场景 σ、排除集 {X1…X20} 下，对所有满足 `legal` 的动作序列，目标不可能在 t < N 达成。
> 由于排除集包含能力型项 {X1–X17, X19, X20}，本下界**不**蕴含真实文明 VI 的下界；它只对"受限动作集"成立。
> 松弛型项 {X18} 的排除是安全的。

---

## 9. θ：语义开关与 v0 敏感性盒

### 9.1 承重开关（进入 v0 的 192 组合盒）

| # | 开关 | 取值 | 默认 | 判别 fixture | 若错的后果 |
|---|---|---|---|---|---|
| θ1 | `thresholdMode` | `floor` / `exact` | 无（两者都算） | FX-TH | 差 ≤ 1 回合 |
| θ2 | `order` | `GrowthFirst` / `ProductionFirst` / `Simultaneous` | 无（三者都算） | FX-ORD* | 差 1–2 回合 |
| θ3 | `basketOnGrowth` | `Zero` / `Subtract` | `Zero` | FX-BASKET | v0 通常惰性 |
| θ4 | `newCitizen` | `none` / `best` | `best`（松弛端） | FX-ORD-c | 差 0–1 回合 |
| θ5 | `amenityStock A` | `2` / `1` | `2` | FX-AM3 | **差 1–3 回合**（pop 3–4 有无 ×1.05） |
| θ6 | `settlerBase` | `80` / `110` | `80` | FX-SET-BASE | **差 5–7 回合** |
| θ7 | `compose` | `product` / `additive` | `product` | 无（惰性守卫） | 仅 pop ≥5 承重 |
| θ8 | `postCompletionGrowth` | `none` / `recheck` | `recheck` | FX-ORD-d | 差 0–1 回合 |

`Θ_v0 := θ1 × θ2 × θ3 × θ4 × θ5 × θ6 × θ8`（7 个开关，2·3·2·2·2·2·2 = **192** 个组合）。θ7 只在 pop ≥5 时并入。**这不要求 192 份证书**：`RULES.md` 要求的是

1. 对每个 θ ∈ Θ_v0 计算 `N(θ)`（Python 搜索即可，不受信）；
2. 至少对 `argmin` 与 `argmax` 两个极端 θ 出具完整 Lean 证书；
3. 对其余组合出具 **Lean 可检查的单调性/区间引理**，或出具"差分表 + 脚本 hash"（明确标注为未证明）；
4. 报告写明 `min_θ N(θ)`、`max_θ N(θ)`，即 **envelope**。

**Envelope 的意义**：在语义未定时，单一 `N` 是假精度。Envelope 是诚实的结论形式；当且仅当 envelope 退化为单点（所有 θ 同值）时，才能说"本模型对未决语义不敏感"。

### 9.2 非承重但必须写死的开关

| # | 开关 | 取值 | 默认 | 依据 |
|---|---|---|---|---|
| θ9 | `growthBase` | `surplus` / `threshold` | `surplus` | `[D*-ui]`：`foodSurplus * GetOverallGrowthModifier()` |
| θ10 | `growthRounding` | `exact` / `trunc10` / `trunc1` | `exact` | `[U]` |
| θ11 | `prodRounding` | `exact` / `trunc10` / `trunc1` | `exact` | `[U]` |
| θ12 | `assignTiming` | `sameTurn` / `nextTurn` | `sameTurn` | `[U]`，松弛端 |
| θ13 | `idle` | `allow` / `forbid` | `allow` | `[U]`，松弛端 |
| θ14 | `starvation` | `forbid` / `model` | `forbid` | §7.1 |
| θ15 | `multiGrowth` | `off` / `on` | `off` | `[U]`，v0 惰性 |
| θ16 | `zeroStrict` | `on` / `off` | `on` | R-HOUS-3 |
| θ17 | `centerHills` | `maxOnly` / `plusOne` | 规避（S-1） | R-CITY-3 |
| θ18 | `foundingTurn` | `produces` / `not` | 无（影响 t↔UI 映射） | R-ORD-4 |
| θ19 | `basketOnSettler` | `keep` / `zero` | `keep` | R-SET-8 |

### 9.3 配置的不可变性

θ 与 σ 必须由**解答文件之外**的模块定义，并在证书中以 hash 引用（`PLAN.md §6`）。解答文件不得重定义 θ。

---

## 10. 证明义务（M2/M3）

### 10.1 可达性证书（M2）

1. `playout : List Action` 逐步通过 `step`，每步 `legal` 成立。
2. 终态 `Goal` 成立，且 `t = N`。
3. 逐回合报告表：pop / food / prog / 分配 / 建造 / 该回合的 `g` 与 `prodMult`。

### 10.2 下界证书（M3）

1. `reach 0 = {s0}`。
2. `reach (t+1) = ⋃_{s ∈ reach t} ⋃_{a ∈ allActions s} step s a`（去重）。
3. `reach_sound : s ∈ reach t → ReachableAt t s`。
4. `reach_complete : ReachableAt t s → s ∈ reach t`（依赖动作枚举完备性）。
5. `no_goal_before : ∀ t < N, ∀ s ∈ reach t, ¬ Goal s`。
6. 组合：`OptimalAt θ N`。

### 10.3 去重与支配（**不得假设"粮食越多越好"**）

- 唯一允许的去重键：整个状态相等（`pop, food, prog, trained`）。
- **反例（本模型内可构造）**：在 A=2 的首都，pop 4→5 会从 Happy 掉到 Content，失去 +10% 增长与 +5% 产能。因此"储粮更多"可能把一个状态推向 pop 5，使后续产能下降。**粮食不是单调收益**。
- 若 M4 想引入支配剪枝，必须证明：`s ⪯ s' ⇒` 对任意从 `s'` 出发的达成路线，存在一条从 `s` 出发、不晚于它的路线。上述反例说明简单分量序不成立；需要把宜居档纳入支配条件（例如"相同 `g` 且相同 `prodMult`"）。

### 10.4 规模预算

上界估算（σ 默认、`|tiles|=5`）：`pop ≤ 6`、`food < max threshold ≈ 6600`（1/100）、`prog < 8000`（1/100）。朴素状态空间 ~3×10^8，但逐层去重后每层预计 10^3–10^5 量级。策略：

1. 先用 `|tiles| = 3` 的极简场景跑通 M2/M3（推荐 `(2,0), (1,1), (0,0)`）。
2. 再扩到 5 格。
3. 若内核 `decide` 超时，改用**证书检查器**：Python 产出每层状态列表，Lean 验证 (a) 初态、(b) 每层全覆盖、(c) 无目标。检查器本身必须是 `Bool` 函数并由定理绑定（`of_decide_eq_true`）。
4. 若使用 `native_decide`，必须在报告中披露 `Lean.ofReduceBool` 依赖；不得把"编译通过"写成"无额外假设"。

### 10.5 公理审计

`#print axioms` 必须只列出 `propext`/`Classical.choice`/`Quot.sound`（或更少）。拒绝 `sorryAx`。任何自定义公理一律拒绝。

---

## 11. Fixtures（按优先级，判别式设计）

**总则**：每个 fixture 先写下"两个互斥假设各自的**不同可观测值**"，再去游戏里看。没有预测表的观测不算 fixture。

### P0（阻塞一切数值结论）

| ID | 判别问题 | 设置 | 观察 | 决策规则 | 翻转 |
|---|---|---|---|---|---|
| **FX-VER** | build 与数据版本 | 在合法安装的机器上只读导出 | `appmanifest_289070.acf` 的 `buildid`；`GlobalParameters.xml`/`Units.xml`/`Buildings.xml`/`Policies.xml` 的 sha256 | 无此记录 ⇒ 所有 `[D*]` 不得升级 | R-VER-2 |
| **FX-SET-BASE** | 首个训练移民 80 还是 110 | 新开局，建都后立刻打开生产面板 | Settler 的产能成本；以及金币价（若“金币 = 4× 产能”成立，则为 320 或 440） | `80 ⇒ θ6=80`；`110 ⇒ θ6=110`。金币价只作交叉校验，不当主判据 | θ6 |
| **FX-AM1** | pop 1–2 是否带增长/产能乘数 | 首都 pop 1，只工作 1 格 2 食物 0 产能地格 | 城市面板“食物 +X/回合”与“产能 Y/回合” | `+2.2 ⇒ 有 ×1.1`；`+2.0 ⇒ 无`。产能应为 `3×1.05 = 3.15`（若显示 3.0 则无乘数） | θ5/`R-AMEN-6` |
| **FX-AM3** | pop 3 的宜居等级（**A=2 vs A=1 的唯一判别点**） | 首都长到 pop 3，不做任何操作 | City Details → Amenities：可用数、需求数、等级 | `可用 2 / 需求 1 / Happy ⇒ A=2`；`可用 1 / 需求 1 / Content ⇒ A=1` | θ5 |
| **FX-SG** | 建移民期间是否照常增长 | 让首都在建移民的同时接近增长 | 移民生产期间"距增长回合数"是否变化；人口是否增加 | 变化 ⇒ 增长继续（R-SET-7 成立）；冻结 ⇒ **整个模型结构要改** | 结构性 |
| **FX-TH** | 阈值 33 还是 33.83 | **非首都**城（1 免费宜居、需求 1 ⇒ Content），pop 3，淡水（住房 5 ≥ pop+2），盈余恰 3/回合，篮子从"刚增长那回合末"归零起算 | 先确认面板等级显示 **Content**（若为 Displeased，说明该城可用宜居为 0 ⇒ 先解决 U16，本 fixture 作废）；第 11 回合末 vs 第 12 回合末是否增长；同时看面板"距增长所需食物" | 11 回合 ⇒ `floor`；12 回合 ⇒ `exact` | θ1 |
| **FX-FOUND** | 建都当回合是否结算 | 第 1 回合原地建都，直接结束回合 | 第 2 回合开始时的食物篮子/生产进度 | 非 0 ⇒ 建都回合产出；0 ⇒ 不产出 | θ18 |

### P1（决定 N 的 1–2 回合）

| ID | 判别问题 | 设置 | 决策规则 |
|---|---|---|---|
| **FX-CAL** | 中心+宫殿基线 | pop 1，依次只工作两个已知不同产出的地格 | 总量差 = 地格差；解出 `center+palace`，再解出 `palaceP`（R-CITY-4） |
| **FX-ORD-a** | 增长与完工同回合：人口结果 | pop 2，移民剩 1 回合，篮子剩 1 回合满 | 完工后 pop=2 ⇒ 先长后 −1；pop=1 ⇒ 先 −1 |
| **FX-ORD-b** | 完工当回合的消耗人口 | 同上 | 食物净变化 −4/−6/−2 分别对应 pop2/pop3/pop1 |
| **FX-ORD-c** | 新市民当回合是否加产能 | 增长与完工同回合 | 该回合产能增量是否含新地格 ⇒ θ4 |
| **FX-ORD-d** | 完工 −1 后篮子与再增长 | 同上，记录完工后立刻的篮子 | 篮子非 0 ⇒ `keep`；且若立刻回长 ⇒ `recheck` |
| **FX-PROD-FRAC** | 产能小数与取整 | 首都 pop 1，基础产能 9，Happy | 面板 9.4/9.45/9；下一回合进度增量 ⇒ θ11 |
| **FX-AM5** | pop 5 是否掉到 Content（A=2 时的预测） | 首都长到 pop 5 | 等级 Content 且 +5% 产能消失 ⇒ §5.4 表成立；仍 Happy ⇒ A≥3 或分档不同 |
| **FX-BASKET** | 增长后溢出 | 篮子差 1 满，盈余 5 | 下回合篮子 0 ⇒ `Zero`；4 ⇒ `Subtract` |

### P2（M5 才承重，或低风险）

| ID | 判别问题 |
|---|---|
| FX-HOUS | 无水城 pop 1（left=1 ⇒ 50%）、pop 2（left=0 ⇒ 25%）的增长回合数；确认 `−4` 仍是 25%、`−5` 才是 0% |
| FX-ASSIGN | 同一回合改分配是否当回合生效（θ12） |
| FX-DIFF | Prince vs Deity 同种子，人类侧首次增长回合是否相同（R-VER-4） |
| FX-STARVE | pop 3、盈余 −3 时篮子与掉人口的时点（v0 不建模，但 M5 要） |
| FX-CENTER-HILLS | 平原丘陵建都：中心是 2F/2P 还是 2F/3P（R-CITY-3） |
| FX-MULTIGROW | 一次结算是否能连涨两级（θ15） |

### 11.1 模型自检轨迹（**不是游戏证据**，用于抓实现 bug）

默认 σ、θ5=A2、θ6=80、θ1=`exact`、θ2=`GrowthFirst`：

```
t=0: pop1, food0(0), prog0(0)
  分配 (2,0) 地格
  f = 2(中心) + 0(宫殿) + 2(地格) = 4
  p = 1(中心) + 2(宫殿) + 0(地格) = 3
  d = 4 − 2·1 = 2 ； e = 2 × 1.1 = 2.2
  ⇒ food = 220，prog = 3 × 1.05 = 3.15 → 315
  分配不变时每回合同样 +220 / +315
  t=7: food = 1540 ≥ 1500(=15.00) ⇒ pop 2，food 清 0（θ3=Zero）
```

三个必须逐项对上的观测（比"第几回合增长"更判别）：

| t | 观测量 | 正确值 | 错误签名 |
|---|---|---|---|
| 1 | `food`（1/100） | **220** | 200 ⇒ 增长乘数未生效（或作用到阈值上） |
| 1 | `prog`（1/100） | **315** | 300 ⇒ 产能乘数未生效 |
| 7 | `pop` | **2** | 8 ⇒ 2.0/回合（乘数未生效）；5 或 6 ⇒ 消耗、阈值或盈余被算错（用 t=1 的篮子值定位） |

注意：**“第 7 回合增长”不是判别式**。若错误地把 +10% 作用到阈值（`15/1.1 = 13.636`，2.0/回合），仍然在第 7 回合（14.0）增长。真正的判别量是 **t=1 的篮子值 220 vs 200**（与 FX-AM1 的面板读数同源）。

---

## 12. 证据接受标准

### 12.1 一条规则从 `[U]` 升级为 `[V]` 的最小条件

1. `buildid` + 四个 XML 的 sha256；
2. 设置清单：规则集 / 速度 / 难度 / 文明与领袖 / DLC / MOD / 游戏模式 / 地图与种子 / 起始时代；
3. 至少一张**带回合号**的截图，显示被观测的量（城市面板 / Amenities 折叠区 / 生产面板）；
4. 观测值与 `[D*]` 数据一致（若不一致，以实机为准并把数据标为漂移）；
5. 该观测能被**第二个人**按记录复现（存档 hash + 操作序列）。

### 12.2 不接受为证据的材料

- wiki 的**复算表**（例如把公式代入得到 33.8/44.1）——它证明的是"公式"，不是"游戏"；
- 任何 MOD / 自制地图 / 修改过的 XML 下的观测（只能记 `[C-mod]`，且不可迁移）；
- 预览版、Beta、发售前资料；
- 没有 build 号与回合号的视频、截图、口述；
- "社区一致认为"（只能产生假设，不能产生 `[V]`）。

### 12.3 冲突处理

- 两个 `[V]` 冲突 ⇒ 停止，记录两个 build，按 build 分叉 θ（这意味着 R-VER-2 未完成）。
- `[V]` 与 `[D]` 冲突 ⇒ 以 `[V]` 为准，数据标 `drift`，并检查 build 号。
- `[C]` 与 `[C]` 冲突 ⇒ 保留双方，写进 θ 的两个取值，fixture 判别；**不得**取平均或取"更合理"的一个。

### 12.4 反驳协议

任何 fixture 与模型不符时：
1. 在 §13 记录：日期、fixture ID、模型版本、θ、预期值、观测值；
2. 该 θ 取值标 `[V-refuted]` 并禁用；
3. 之前依赖它的证书**全部作废**（在 `reports/` 中标 `INVALIDATED-BY:<fixture>`）；
4. 若新观测无法被现有 θ 表达，模型版本 +1，不修改旧证书。

---

## 13. 未决登记与变更日志

### 13.1 未决项（与 `research/RULES-RESEARCH.md §6` 的对应与修订）

| ID | 问题 | 影响 | 本文件处置 | 原报告 |
|---|---|---|---|---|
| U1 | build 未知 | 高 | R-VER-2，θ6/θ5 承重 | 保留 |
| U2 | `LEFT_ZERO=-4` 严格性 | 低（v0 pop ≤4 不触发） | 已基本消解：两张表都支持"−4 仍 25%"，θ16 仅保留形式 | **降级为低** |
| U3 | 阈值是否取整 | 高（≤1 回合） | θ1，FX-TH | 保留 |
| U4 | 增长后溢出 | 低 | θ3，FX-BASKET | 保留 |
| U5 | +10% 作用于盈余还是阈值 | 高 | **已基本确定**：`[D*-ui]` 显示作用于盈余；θ9 仅作形式保留 | **升级** |
| U6 | 产能小数取整 | 高 | θ11，FX-PROD-FRAC；原"9→9.4"证据被判定为**不可判** | **修订** |
| U7 | 回合内顺序 | 最高 | θ2/θ8，FX-ORD* | 保留 |
| U8 | 新市民当回合产出 | 高 | θ4，FX-ORD-c | 保留 |
| U9 | 建城当回合 | 中 | θ18，FX-FOUND | 保留 |
| U10 | 改分配生效时机 | 中 | θ12 | 保留 |
| U11 | pop<3 是否判 Happy | 高 | **已基本消解**：需求为 0 时纯差值比较（UI `NetAmount`），且 A≥1 时 pop1–2 必为 Happy；真正未决的是 A 的**数量**（见 U16） | **改写** |
| U12 | 首个移民 80/110 | 高 | θ6，FX-SET-BASE | 保留 |
| U13 | 难度修正 | 中 | R-VER-4，FX-DIFF | 保留 |
| U14 | 饥饿 | 低 | v0 禁负盈余；FX-STARVE 留 M5 | 保留 |
| U15 | 25% 档缺失值 | 低 | 消解：Civilopedia 明说 25% | **关闭** |
| **U16** | **首都可用宜居总数 A = 2 还是 1** | **高（1–3 回合）** | **新增**：θ5，FX-AM3（pop 3） | 报告未识别 |
| **U17** | 平原丘陵中心是否 +1P | 中（v0 规避） | **新增**：θ17；来源自相矛盾，§14-C2 | 报告采用了一个与来源算例冲突的公式 |
| **U18** | 生产移民期间增长是否冻结 | **结构性** | **新增**：FX-SG（报告无对应 fixture） | 报告仅引用轶事 |
| **U19** | 宫殿 +2 产能的可核性 | 中 | **新增**：FX-CAL（XML 里没有该字段） | 报告当作已知 |
| **U20** | 增长修正的合成律（乘/加） | 中（pop≥5 承重） | **新增**：θ7 + 可达性守卫 | 报告未讨论 |

### 13.2 变更日志

| 日期 | 版本 | 变更 | 触发 |
|---|---|---|---|
| 2026-10-17 | v0-draft | 建立契约；[V] 计数 0 | 本任务 |
| — | — | （fixture 落地后在此追加；禁止改写历史行） | — |

---

## 14. 对 `research/RULES-RESEARCH.md` 的独立核查（更正）

以下每条都在本任务中独立复核过（fandom MediaWiki API 原文、游戏自带 UI Lua、补丁注记）。报告整体可用，但下列 7 点必须更正。

- **C1｜"社区实测给出 33.8 / 44.1，说明游戏内部用浮点"——证据不成立。**
  该小数表恰好是公式求值后截到 1 位：`T(6)=66.180…→66.1`、`T(7)=77.696…→77.6`、`T(8)=89.520…→89.5`。若真是在游戏里读数，66.18 应显示 66.1 或 66.2，而 89.52 应显示 89.5——但这三例同时与"公式截断"吻合，且没有任何一例偏离公式。**结论：小数表只能证明公式，不能证明游戏内部表示。** U3 应保持 `[U]`，不得写"倾向后者"。

- **C2｜城市中心"平原丘陵 +1 产能"与来源算例冲突。**
  报告写成 `centerProd = max(terrainP,1) + (1 if plainsHills)`（⇒ 平原丘陵 3P）。但 City 页自己的算例明确给出：平原丘陵原生 1F/2P，建城后为 **2F/2P**。同一页正文的"+1 Production"更可能指"丘陵相对平坦平原的地形加成"，而不是中心的额外加成。**处置：v0 用平坦中心规避；θ17 保留。**

- **C3｜报告的 F3（pop 1 宜居等级）不是判别式。**
  A=2 与 A=1 在 pop 1 都是 Happy（差值 +2 vs +1，同属 Happy 档）。F3 只能区分"Happy vs Content"。**判别点必须在 pop 3（需求=1）**：A=2 ⇒ 差 +1 Happy；A=1 ⇒ 差 0 Content。已改为 FX-AM3。

- **C4｜"首都恒 Happy（pop ≤4）"是 build 相关的，不是原版规则。**
  R&F/GS 改版补丁注记（社区转述）："Removed the free population amenity. **Added an amenity to the palace.**"。这句话本身就说明宫殿宜居是**后加的**；再叠加 2016 年预览版社区汇总（"Capital starts with 1 amenity … other cities start with 0"），首都可用宜居总数 A 至少有 **1 和 2 两种读数**（甚至 0+1 与 1+0 两种构成），而报告把 `CITY_AMENITIES_FOR_FREE=1` + 当前 `BUILDING_PALACE` 直接相加并当作"原版事实"，掩盖了版本漂移。**处置：θ5 承重，FX-AM3 在 pop 3 判别。**

- **C5｜移民成本的核心分叉在"起手免费移民是否计入"，报告的两条证据其实同源。**
  Sullla 与 Skymods 都只说明"已训练数"从 0 起（⇒ 80）；wiki 的 `30(x+1)+50` 明确写"包括起手移民"（⇒ 110）。这不是"80 对 110 的口径之争"，而是 `COST_PROGRESSION_PREVIOUS_COPIES` 是否统计"免费获得的单位"这一个语义问题。报告的建议（默认 80）合理，但**必须**把 110 也纳入 envelope；且要注意 v0 中递进参数 30 **完全惰性**（R-SET-3），真正的分叉只有 80/110。

- **C6｜"生产移民期间城市照常增长"缺少 fixture，且报告的证据链是轶事。**
  报告引用两条 Reddit；其中"移民完成人口没掉"的观察其实**同时**支持"篮子保留 + 完工后再判定增长"。这条轶事不足以确定 R-SET-7，更不足以确定 R-ORD-3。**新增 FX-SG 为 P0。**

- **C7｜排除清单漏掉两项承重机制：`Colonization`（+50% 移民产能，Early Empire）与 `Urban Planning`（+1 产能，Code of Laws）。**
  报告只提了 Urban Planning。已核实 `Module:Data/Civ6/Base/Policies`：`POLICY_COLONIZATION{Description="+50% Production toward Settlers"; PrereqCivic="CIVIC_EARLY_EMPIRE"}`。两者都必须进入 §8 的 X5，并在证书首行声明"不含政策卡"。

**另外两处小修**：
- 报告的常量块写 `"palace": {"production": 2}` 且未标注证据级别——该字段来自 wiki 产出表，`BUILDING_PALACE` 的 XML 片段里没有，必须由 FX-CAL 反解（U19）。
- 报告的 `CITY_HOUSING_LEFT_ZERO` 处置为"解释存疑、差一位"——实际上两张独立表都支持"−4 仍 25%、−5 才 0"，参数名很可能表示"最后一个仍增长的 left 值"。U2 可降级。

---

## 15. 与 SCOPE / PLAN 的接口

- 本文件定义 `M0(θ)`；`SCOPE.md` 定义**v0 声称什么、不声称什么**。
- `PLAN.md` 的 M0 通过条件（"增长、生产完成和两者同回合发生等边界情况都有明确预期"）在本文件中落实为：§11 的 FX-ORD-a/b/c/d + §11.1 的模型自检轨迹。**注意：M0 的"明确预期"在 v0 只能是"模型内的预期"；游戏内的预期要等 FX 落地。**
- `PLAN.md` 的 M3 通过条件（"故意降低 N 的测试无法通过"）在本文件中落实为 §10.2 的五条义务 + §10.3 的去重纪律。
- 本文件不修改 `PLAN.md`、`research/*`、Lean 引导文件。

---

## 16. 与仓库内并行产物的关系（重要，不加会出不一致）

本任务期间仓库中并行出现了三件东西。它们的**信任角色不同**，不得混用：

| 产物 | 角色 | 是否本契约的实例 | 注意事项 |
|---|---|---|---|
| `Civ6Verify/Reachability/Finite.lean` | 通用有限期可达/最优性引擎（`Model` typeclass，无任何游戏规则） | 是**目标接口** | 本文件 §10.2 的五条义务正好对应它的 `legalActions_sound` / `legalActions_complete` / 前沿定理。它不做规则，规则必须由本契约提供 |
| `fixtures/synthetic-v0.json` + `search/synthetic.py` | 一个**刻意非 Civ6** 的合成基准（2 格、pop ≤ 2、阈值 `T=4p`、成本 8） | **否**（只借用同一种 `Model` 形状） | 见下方 BMK-v0 的三处规则差异 |
| 本文件的 `M0(θ, σ)` | 文明 VI **形状**、常量全部参数化的契约模型 | 是 | 不产生任何游戏断言；`[V]=0` |

### BMK-v0（合成基准）与 `M0` 的规则差异

1. **同格多人**：基准允许两名市民工作同一格（`A(p) = {(k, p−k)}`）。Civ6 禁止（`CITY_NORMAL_PLOT_WORKER_CAPACITY=1`，`R-CIT-1`）。
   → 本契约新增 **θ20 `tileCapacity ∈ {1, pop}`**，默认 **1**（游戏侧）；`pop` 仅用于复现基准。**使用 `pop` 的证书必须标注：这是放松，不是 Civ6。**
2. **禁止闲置**：基准要求每市民恰好 1 格；本契约默认 `θ13 = allow`（松弛端）。两者不可混用：基准的 `allow` 会让基准的下界变弱。
3. **完工清零食物 + 减阈值增长**：基准 `basketOnSettler=zero`、`basketOnGrowth=Subtract`、`multiGrowth=on`；本契约默认 `keep / Zero / off`。这四个都是 θ 上的不同取值，**不得**在报告里互相引用数字。

### 验收要求

- `synthetic-v0` 可由 `θ20 = pop` + `θ13 = forbid` + `θ3 = Subtract` + `θ15 = on` + `θ19 = zero` **近似**表示；但它还有本契约没有的三条规则（完工清零进度、pop 上限时丢弃盈余、前置未满足时进度封顶），因此严格说它是**独立基准**，不是 `M0` 的实例。
- BMK-v0 的价值：用极小状态空间把 `Finite.lean` 的接口、枚举完备性与证书格式跑通（这正是 `PLAN.md` M1/M2/M3 的“流水线”部分）。
- BMK-v0 **不能**验证：宜居/住房、非整数产出、pop ≥ 3、闲置、1 格 1 人、增长修正合成律。这些正是 `M0` 要补的部分。
- 任何报告若把 BMK-v0 的 `N` 写成“文明 VI 的第一个移民回合”，直接判定审计失败（见 `SCOPE.md §3`）。

