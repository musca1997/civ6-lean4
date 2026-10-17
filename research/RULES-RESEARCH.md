# RULES-RESEARCH — 《文明 VI》原版规则核实（单城 · 最早首个移民）

> 归属：本文件是本轮唯一产物（owned file）。未修改任何游戏文件、存档或仓库内其他文件。
> 目的：为 M0/M1 提供**可编码的常量、已核实的结算语义、明确的未知项和必做 fixture**。
> 约束：只收录有 URL 的公开证据；凡是推导出来的公式都显式标注 `[推导]`，不把推导当证据。
> 日期：2026-10-17。调研者：research/RULES-RESEARCH.md owner。

---

## 0. TL;DR（对模型影响最大的 10 条）

1. **单城最早移民的关键常数全部可取**：2 食物/市民、增长阈值 `15 + 8(n-1) + (n-1)^1.5`、移民 80 产能 +30/个、需人口 ≥2、完工 −1 人口、城市中心地格至少 2 食物 1 产能。见 §3、§4。
2. **宜居度不能像 PLAN 2.3 假设的那样“不建模”**。原版每个城市自带 1 点免费宜居度，首都宫殿再 +1，共 2 点；人口 1–4 时需求为 0/1。若“需求为 0 时仍参与比较”（待 F3 确认），首都人口 1–4 恒为 **Happy：+10% 增长、+5% 非食物产出**，即本场景从第 1 回合起就带增长与产能乘数。见 §4.4、§6-U11。
3. 由此推论：**产能与食物盈余都会出现小数**（社区实测把 9 产能显示为 9.4）。Lean 侧不能只用整数“每回合 +P”离散模型，必须先由 fixture 定死取整规则。见 §6-U3、§7-F5。
4. 首都若选**淡水**（住房 5 + 宫殿 1 = 6），人口 ≤4 时住房完全不起作用；若选无淡水（2+1=3），人口 2 就会吃到 50% 增长惩罚。**场景选址直接决定要不要建模住房**。见 §4.3。
5. **增长阈值不是整数**：人口 3→4 需 33.828…、4→5 需 44.196…。维基表里的 33/44 是向下取整后的展示值；社区实测给出 33.8/44.1，说明游戏内部用浮点比较。**“33 够不够”必须用 fixture 判**。见 §4.2、§7-F2。
6. **移民费用是 80，不是 110**（`Cost=80`，`CostProgressionParam1=30`，按已产出份数递进）。维基“含初始移民”的表述与实测/数据冲突，按 80/110/140 采用并在报告中声明。见 §4.7。
7. **版本漂移真实存在**：2016 年 10 月发售版 `Units.xml` 里移民 `CostProgressionParam1="20"`（80/100/120…），后来（“Summer patch”）改成 30。**“原版规则集”必须再钉一个 build 号**，否则连移民费用都不唯一。见 §2。
8. **回合内处理顺序（食物/增长 vs 生产完工 vs 移民 −1 人口）没有任何权威来源**，只有 Civ5 外推的社区描述。这是当前最大的语义空洞，必须用 fixture 钉死。见 §4.9、§7-F7。
9. **政策卡会直接打破下界**：`Urban Planning`（法典解锁，+1 全城产能）就能把 20 回合级别的最早移民显著提前。PLAN 2.3 排除政策是允许的，但证书必须写成“受限动作集下的下界”，并把它列为 M5 首要突破项。见 §5.3。
10. **本机没有任何《文明 VI》游戏数据**（Steam 库只有 Liftoff 等），所以本轮结论全部来自公开资料，**不能声称“已验证模型与游戏一致”**；`fixtures/` 必须等真实游戏环境。见 §9。

---

## 1. 证据分级

| 级别 | 含义 | 本轮是否使用 |
|---|---|---|
| **A** | 官方手册 / 官方 Civilopedia 文本 | 是（2K 官方 PDF、civilopedia.net standard-rules） |
| **B** | 从游戏 XML/SQL 自动提取的数据（维基 `Module:Data/Civ6/Base/*`） | 是（核心常量来源，但**build 不明**） |
| **C** | 社区实测/共识（CivFanatics、Reddit、Sullla 等），单条不足为凭 | 是（用于语义与取整） |
| **D** | 推导/外推（含本文件的计算、Civ5 外推） | 是，全部标 `[推导]` |

使用规则：**A > B > C**；只有 A+B 同时支持才写进 §3 常量表；只有 C 支持的一律进 §6 未决项。

---

## 2. 版本界定：规则集 ≠ build（必须先钉死）

PLAN 2.1 要求“记录实际游戏 build、DLC、MOD、速度、文明”。核实结果说明这不是形式要求：

- 维基 `Module:Data/Civ6/Base/Units` 的 `UNIT_SETTLER` 当前是 `CostProgressionParam1=30`：
  ```
  UNIT_SETTLER={ Name=[=[Settler]=]; ...; Cost=80; PopulationCost=1; FoundCity=true;
    CostProgressionModel="COST_PROGRESSION_PREVIOUS_COPIES"; CostProgressionParam1=30;
    PrereqPopulation=2; CanTrain=true; ...};
  ```
  来源：<https://civilization.fandom.com/wiki/Module:Data/Civ6/Base/Units>
- 但 2016-10 发售版玩家直接读 `Units.xml` 的记录是 `CostProgressionParam1="20"`，并实测“80, 100, 120…”：
  > “For workers and settlers there are also some parameters in Units.xml: Settler: Cost="80" CostProgressionModel="COST_PROGRESSION_PREVIOUS_COPIES" CostProgressionParam1="20" … On standard speed cost of settler goes like: 80, 100, 120…”
  来源：<https://forums.civfanatics.com/threads/district-settler-builder-cost-formula-october-2016.600489/>
- 同一现象的另一处独立记述：
  > “The first settler costs 80 production and each additional one costs another 30 production (initially 20 production before the Summer patch), so 80 then 110 then 140 and so on.”
  来源：<https://sullla.com/Civ6/exceedsexpectations.html>

**结论**：本项目必须声明“原版规则集 + 具体 build/补丁”二元组。仅写 “vanilla” 不足以确定移民递进参数（20 还是 30）。维基 `Base` 数据模块**没有版本标注**（`Module:Data/Civ6/Base/doc` 不存在），只能视为“某次最终态 vanilla 导出”，不可当作 build 证据。→ 见 §9 阻塞项 B1。

其他必须固定的设置（每项都会改变数值）：

| 设置 | 必须取值 | 证据 |
|---|---|---|
| 规则集 | 原版（不启用 R&F / GS） | 两资料集差异显著，见 §4.3/§4.4 对照 |
| 游戏速度 | Standard（`CostMultiplier=100`） | `Module:Data/Civ6/Base/GameSpeeds`: `GAMESPEED_STANDARD={... CostMultiplier=100;}` |
| 难度 | Prince（最低 AI 加成） | 手册：“The game difficulty determines a number of things, including … the speed at which your civilization grows”，但未给出人类侧修正；→ 需 fixture 确认人类增长不受难度影响 |
| 万神殿/宗教 | 不得在此窗口内创立，或显式建模 | `Fertility Rites` +10% 增长、`Religious Settlements` 直接送移民 |
| 政策卡 | PLAN 排除；但见 §5.3 | `POLICY_URBAN_PLANNING`：`+1 Production in all cities`, `PrereqCivic="CIVIC_CODE_OF_LAWS"`（<https://civilization.fandom.com/wiki/Module:Data/Civ6/Base/Policies>） |
| MOD / 游戏模式 | 全部关闭 | —— |

---

## 3. 已核实常量表（可直接编码）

来源：维基从游戏 XML/SQL 自动提取的 **Base** 数据模块（B 级），与官方 Civilopedia/手册（A 级）逐条互证。

### 3.1 GlobalParameters（vanilla）

| 键 | 值 | 含义 | A 级互证 |
|---|---|---|---|
| `CITY_FOOD_CONSUMPTION_PER_POPULATION` | **2** | 每市民每回合食物消耗 | 手册 p.104：“consume 2 food for each population point” |
| `CITY_GROWTH_THRESHOLD` | **15** | 增长阈值基数 | 手册 p.105（只给“bucket”概念，未给数） |
| `CITY_GROWTH_MULTIPLIER` | **8** | 每级线性项 | —— |
| `CITY_GROWTH_EXPONENT` | **1.5** | 幂次项 | —— |
| `CITY_GROWTH_OCCUPATION_MULTIPLIER` | 0.0 | 占领城增长倍率（本场景不涉及） | —— |
| `CITY_HOUSING_LEFT_50PCT_GROWTH` | **1** | 住房−人口 = 1 → 50% | Civilopedia：`1 below → 50%` |
| `CITY_HOUSING_LEFT_25PCT_GROWTH` | **空** | 未显式设置（默认 25% 档） | Civilopedia：`at Housing limit → 25%` |
| `CITY_HOUSING_LEFT_ZERO_GROWTH` | **−4** | 增长为 0 的阈值（**解释存疑**，见 §6-U2） | Civilopedia：`can grow to 5 over Housing, then stop` |
| `CITY_AMENITIES_FOR_FREE` | **1** | 每城免费宜居度（GS 中为空/0） | Amenities 页：“In GS, cities no longer start with a free Amenity (except the Capital)” → 反推 vanilla 每城 1 |
| `CITY_POP_PER_AMENITY` | **2** | 每 2 人口 1 宜居度 | 手册 p.95：“1 Amenity is required for each 2 Population, starting at a Population of 3” |
| `CITY_POPULATION_RIVER_LAKE` | **5** | 淡水住房 | Housing 页：淡水 5 |
| `CITY_POPULATION_COAST` | **3** | 海岸住房 | Housing 页：海岸 3 |
| `CITY_POPULATION_NO_WATER` | **2** | 无水源住房 | Housing 页：其它 2 |
| `CITY_NORMAL_PLOT_WORKER_CAPACITY` | **1** | 每市民占 1 地块 | Population 页：“each Citizen can work one tile” |
| `YIELD_FOOD_CITY_TERRAIN_REPLACE` | **2** | 城市中心地格食物下限 | City 页（见 §4.5） |
| `YIELD_PRODUCTION_CITY_TERRAIN_REPLACE` | **1** | 城市中心地格产能下限 | 同上 |
| `CITY_MIN_RANGE` | 3 | 可工作半径 | Population/City 页：“3 hexes of the City Center” |

来源：<https://civilization.fandom.com/wiki/Module:Data/Civ6/Base/GlobalParameters>

### 3.2 单位 / 建筑 / 速度

`UNIT_SETTLER`（B 级，见 §2 引文）：`Cost=80`、`PopulationCost=1`、`PrereqPopulation=2`、无 `PrereqTech`、`CostProgressionModel=COST_PROGRESSION_PREVIOUS_COPIES`、`CostProgressionParam1=30`、`PurchaseYield=YIELD_GOLD`（本模型排除金币购买）。

`BUILDING_PALACE`（B 级）：
```
BUILDING_PALACE={ Name=[=[Palace]=]; Cost=1; MaxPlayerInstances=1; Capital=true;
  PrereqDistrict="DISTRICT_CITY_CENTER"; Housing=1; Entertainment=1; ObsoleteEra="NO_ERA"; };
```
即宫殿：**+1 住房、+1 宜居度**。产出面（Wiki Palace 页，C 级）：+2 产能、+2 科技、+1 文化、+5 金币、1 大作家槽。
来源：<https://civilization.fandom.com/wiki/Module:Data/Civ6/Base/Buildings>、<https://civilization.fandom.com/wiki/Palace_(Civ6)>

`GAMESPEED_STANDARD`：`CostMultiplier=100`（即标准速度 = 1.0 倍，全部成本/阈值 ×1.0）。
来源：<https://civilization.fandom.com/wiki/Module:Data/Civ6/Base/GameSpeeds>；Speed 页说明速度影响“All costs of Food (for Population growth), Production, …”。

### 3.3 可直接粘贴的常量块

```jsonc
// vanilla (Base) constants, Standard speed
{
  "foodPerCitizen": 2,
  "growth": { "threshold": 15, "multiplier": 8, "exponent": 1.5 },
  "housing": { "left50Pct": 1, "left25Pct": "default(25%)", "leftZero": -4,
               "water": { "fresh": 5, "coast": 3, "none": 2 } },
  "amenities": { "freePerCity": 1, "popPerAmenity": 2,
                 "tiers": { "ecstatic": 3, "happy": [1,2], "content": 0,
                            "displeased": [-2,-1], "unhappy": [-4,-3],
                            "unrest": [-6,-5], "revolt": "<=-7" } },
  "amenityEffects": { "ecstatic": {"growth": 0.20, "nonFood": 0.10},
                      "happy":    {"growth": 0.10, "nonFood": 0.05},
                      "content":  {"growth": 0.00, "nonFood": 0.00},
                      "displeased":{"growth": -0.15, "nonFood": -0.05},
                      "unhappy":  {"growth": -0.30, "nonFood": -0.10} },
  "settler": { "cost": 80, "costPerPreviousCopy": 30, "prereqPopulation": 2,
               "populationCost": 1, "prereqTech": null },
  "cityCenter": { "minFood": 2, "minProduction": 1, "workedForFree": true },
  "palace": { "housing": 1, "amenity": 1, "production": 2 },
  "plotsPerCitizen": 1, "workRadius": 3,
  "initialCityPopulation": 1
}
```

---

## 4. 已核实结算语义

### 4.1 粮食与人口

A 级（官方手册 p.104–105，原文）：
> “A city requires 2 food per citizen (another term for “population”) per turn to avoid starvation.”
> “A city’s citizens have first call on that food, and consume 2 food for each population point (so a city of population 7, it consumes 14 food each turn). Any food left over is put into the “City Growth Bucket.””
> “When the quantity of food reaches a specific amount, the city’s population (citizens) will increase by 1; the city growth bucket is then emptied, and the process begins all over again.”
来源：<https://downloads.2kgames.com/civilization/vi/manuals/eu/CIV_VI_25TH_ONLINE_MANUAL_ENG.pdf>（p.104–105；本地已下载 22 MB 并用 `pdftotext -layout` 提取；页码标记位于每页页脚，故“consume 2 food…”与“Settlers…”两段在 p.105，“A city requires 2 food…”在 p.104）

结论（可编码）：
- 消耗 = `2 × pop`，在盈余计算之前扣除；
- 盈余（可为负）进入“food basket”；
- 篮子满 → pop +1，**篮子清空**（不是“减去阈值”）。这一点对多人口连续增长很重要，`[A]` 明说 “the city growth bucket is then emptied”。

未明确：达到阈值那一回合的**溢出是否保留**（手册说清空；但社区有“harvest 90 food 一次涨多级”的说法）。→ §6-U4。

### 4.2 增长阈值（含取整）

B 级：`threshold=15, multiplier=8, exponent=1.5`。
C 级（CivFanatics 公式帖，原文）：
> “Civ VI's formula is **15 + (n-1) x 8 + (n-1) ^ 1.5**. n is the current population.”
来源：<https://forums.civfanatics.com/threads/population-growth-formula.694910/>

B 级（维基表，n=1..30）：15, 24, 33, 44, 55, 66, 77, 89, 101, 114, …
来源：<https://civilization.fandom.com/wiki/Population_(Civ6)>

`[推导]` 我用 Python 逐项核对：**表中 30 个值与 `floor(15 + 8(n-1) + (n-1)^1.5)` 完全一致，0 处不符**。即：

```
T(n) = floor( 15 + 8·(n−1) + (n−1)^1.5 )      # 仅当游戏真的取整
精确值: T(1)=15, T(2)=24, T(3)=33.8284…, T(4)=44.1962…, T(5)=55, T(6)=66.1803…
```

**关键未决**：表里的 33/44 是“展示用向下取整”还是“游戏内阈值”？社区实测给出 33.8 / 44.1，倾向后者：
> “Read this as, take the 4th row for example, when your population is 4, it take **44.1** extra food for the population to grow to 5.”
来源：<https://www.reddit.com/r/civ/comments/hyj2ac/does_anyone_know_the_exact_amount_of_food_needed/>

对 Lean 的影响：若阈值是 33.828…，则“篮子=33”不增长；若是 33，则增长。相差正好 1 回合。→ §7-F2 必须做。
`[推导]` 注意 `(n−1)^1.5` 一般是无理数，**不能用有理数精确表示**；建议做法：
- 要么由 fixture 证明游戏确实把阈值取整（则模型只用整数）；
- 要么在 n≤6 的有限范围内用有理数夹逼（如 `33.82 < T(3) < 33.83`）并配以“食物篮子以 0.1 为最小粒度”的实测前提；
- 不要引入浮点。

### 4.3 住房（Housing）

A 级（Civilopedia **standard-rules**，即 vanilla 规则集，原文）：
> “A city will add all surplus Food towards growth if its current Population is 2 or more below the city's Housing limit. If the city is 1 Population below its Housing limit, its growth will slow to 50%. When the Population is at the Housing limit, it will grow only at 25% the normal rate. A city can grow to 5 Citizens over its Housing limit at this rate, and then it will stop growing entirely.”
来源：<https://www.civilopedia.net/en-US/standard-rules/concepts/cities_12/>

C 级（表格化，含上限说明）：
| Housing − Pop | 增长率 |
|---|---|
| ≥2 | 100% |
| 1 | 50% |
| 0 … −4 | 25% |
| ≤−5 | 0%（硬上限 Housing+5） |
来源：<https://civilization.fandom.com/wiki/Housing_(Civ6)>

与 B 级参数对照：`LEFT_50PCT=1` ✔；`LEFT_25PCT` 空（默认 25%）✔；`LEFT_ZERO=-4` 与表中“≤−5 才是 0%”**差一位**（见 §6-U2）。

住房来源（本场景相关）：淡水 5 / 海岸 3 / 无水源 2，宫殿 +1。
`[推导]` 首都：淡水 → 6；海岸 → 4；内陆无水 → 3。

推论（对场景选择极重要）：
- 淡水首都：pop ≤4 时 Housing−Pop ≥2 → 住房完全不影响，可从模型里**有条件地**消去；
- 海岸首都：pop=3 时 Housing−Pop=1 → 50%；
- 无水首都：pop=2 时即 50%，pop=3 时 25%。
→ 首版建议锁定**淡水首都**并显式证明“在证明窗口内 pop ≤ 4，故住房倍率恒为 1”；若窗口内会到 pop 5，则必须建模（此时 Housing−Pop=1 → 50%）。

### 4.4 宜居度（Amenities）— **不能排除**

A 级（官方手册 p.95，原文）：
> “1 Amenity is required for each 2 Population, starting at a Population of 3. A content city will not have any modifier applied to it, but a happy city will have a 10% growth increase and a 5% yield increase. Furthermore, an Ecstatic city will have a 20% growth increase and 10% yield increase. Likewise, having too few Amenities will create displeasure among your Citizens, and the growth and yields will receive negative modifiers. At the level of unrest, your growth will stop and you may find rebel partisans in your city.”

Vanilla vs GS 分档（C 级，逐字表）：
| 等级 | Vanilla / R&F | GS |
|---|---|---|
| Ecstatic | ≥+3：非食物产出 +10%，增长 +20% | ≥+5：全产出 +20% |
| Happy | +1..+2：非食物 +5%，增长 +10% | +3..+4：全产出 +10% |
| Content | =0：无修正 | 0..+2：无修正 |
| Displeased | −1..−2：非食物 −5%，增长 −15% | 同左但非食物 −10% |
| Unhappy | −3..−4：非食物 −10%，增长 −30% | 非食物 −20%，增长 −30% |
| Unrest | −5..−6：非食物 −30%，出现叛军 | 同 |
| Revolt | ≤−7 | 同 |
来源：<https://civilization.fandom.com/wiki/Amenities_(Civ6)>

需求公式（C 级）：`required = ceil(pop/2 − 1)`（pop 1–2 → 0，3–4 → 1，5–6 → 2，7–8 → 3）。
来源：同上；与 A 级“每 2 人口 1 点，从人口 3 开始”一致。

`[推导]` **首都宜居度 = 1（每城免费，`CITY_AMENITIES_FOR_FREE`）+ 1（宫殿 `Entertainment=1`）= 2**，于是：
| pop | required | 多余 | 等级 | 增长 | 非食物（含产能） |
|---|---|---|---|---|---|
| 1–2 | 0 | +2 | Happy | ×1.10 | ×1.05 |
| 3–4 | 1 | +1 | Happy | ×1.10 | ×1.05 |
| 5–6 | 2 | 0 | Content | ×1.00 | ×1.00 |
| 7–8 | 3 | −1 | Displeased | ×0.85 | ×0.95 |

这条推论的后果非常大：
1. **PLAN 2.3 里“若不建模宜居度，必须给出让其不改变计算的条件”这个让步在本场景里做不到**——首回合就是 Happy。
2. 而且存在一个反直觉的优化：从 pop 4 长到 pop 5 会**掉到 Content**，失去 +10% 增长和 +5% 产能。首移民路线上“该不该继续长到 5”因此不是单调问题。
3. 但也要注意：**“pop<3 时是否也判 Happy”是社区未明确处**（需求为 0 时是否仍比较）。这是 §7-F3 的核心。

旁证（C 级，说明 +5% 只落在部分产出上）：
> “when I look at the my empire Yield report, there is a breakdown for each city yield which does include Amenities, however it only shows the 5% bonus for Production and Gold, and nothing for Faith, Science, Culture…”
来源：<https://forums.civfanatics.com/threads/what-is-considered-a-non-food-yield.669662/>
对本模型够用：**产能确实吃这 5%**；科技/文化不在本模型中。

### 4.5 城市中心产出基线

B 级：`YIELD_FOOD_CITY_TERRAIN_REPLACE=2`、`YIELD_PRODUCTION_CITY_TERRAIN_REPLACE=1`。

C 级（City 页逐字）：
> “The yield of the tile occupied by the City Center is increased to 2 Food and 1 Production if either was previously lower (before any bonus yields are applied). Plains Hills add an additional point of Production (but Hills on other terrain won't).”
> “Resources of all types remain on the tile; their bonus yields continue to apply if they bring the tile's Food or Production above 2…”
> “The initial Population of the new city is 1 by default.”
> “**The City Center tile is always worked and does not require any citizen to produce yields.**”
来源：<https://civilization.fandom.com/wiki/City_(Civ6)>

`[推导]` 可编码的中心地格规则：
```
centerFood = max(terrainFood, 2) (+ resources/bonuses)
centerProd = max(terrainProd, 1) + (1 if plainsHills else 0) (+ resources/bonuses)
```
例：草原 2F → 2F/1P；平原丘陵 1F2P → 2F/2P；沙漠 → 2F/1P。
宫殿另给 +2 产能（建筑产出，不属于地格）。→ 首都 pop1 的产能 = 中心地格 P + 宫殿 2 + 所工作地块 P。

### 4.6 市民分配

- 每市民工作 1 个地块（`CITY_NORMAL_PLOT_WORKER_CAPACITY=1`；Population 页：“each Citizen can work one tile within the city's borders and 3 hexes of the City Center”）。
- **城市中心地格免费工作，不占市民**（A 级语义由 City 页 `[C]` 给出，且与 `YIELD_*_CITY_TERRAIN_REPLACE` 的设计一致）。
- 同一地块不可被两市民/两城重复工作（手册 p.104：“as long as it is not being worked by another city”；同城重复工作属实现细节，若需钉死可加 fixture）。
- 市民分配可逐回合改动（手册 p.104 “MANUALLY ASSIGNING CITIZENS TO WORK THE LAND”）。
- **未决**：改分配是否在同一回合结算中生效（应为“是”，因为结算读取当前分配），以及新市民在同回合是否立即产出（§4.9）。

### 4.7 移民（Settler）

A 级（手册 p.105，逐字）：
> “Settlers can only be constructed in cities of size 2 or larger. When completed, the city population is reduced by 1”

B 级：`Cost=80`、`PrereqPopulation=2`、`PopulationCost=1`、无科技前置、`CostProgressionModel=COST_PROGRESSION_PREVIOUS_COPIES`、`CostProgressionParam1=30`。

C 级（费用递进，两处独立）：
> “The first settler costs 80 production and each additional one costs another 30 production …, so 80 then 110 then 140 and so on.” — <https://sullla.com/Civ6/exceedsexpectations.html>
> “1st Settler = 80 (Vanilla = 80) (NoOfSettlersBuilt = 0) 2nd Settler = 95 (Vanilla = 110) (NoOfSettlersBuilt = 1)” — <https://catalogue.smods.ru/archives/76178>

`[推导]` `cost(k) = 80 + 30·k`，k = 该玩家**已完成的移民数**（起手免费移民不计；否则首个就是 110）。

**与维基冲突**：`Settler (Civ6)` 写 “x is the number of Settlers you've trained (including your initial one)”，若字面成立则首个 = 110。但上面两条实测、以及 `Cost=80` 的直读，都指向 80。故：**采用 80，并在 §7-F6 用游戏内 UI 复核**；证书中把 80/110 作为可切换参数声明。

其他已核实/待核实：
- **移民生产期间城市照常增长**（Civ V 才冻结）：C 级 “It should still go. Seperate calculation and all. Im still wrapping my head around pop growing while creating a settler. It used to freeze pop growth as you made them.” — <https://www.reddit.com/r/civ/comments/11i282s/>
- **完工 −1 人口时食物篮子保留**（不重置）：C 级 “Yes, it carries over. And because each pop requires a slightly larger number to reach, if you have enough food already stored for the new next level already, it will immediately regain that pop.” — 同上；另有 “The actual growth you have in your city isn't losed after you build the settler … it's possible that you don't lose population” — <https://www.reddit.com/r/civ/comments/vjfr96/>
  → 这意味着“settler 完工那一回合可能同时发生增长，净人口不变”，直接依赖 §4.9 的顺序。
- 未核实：若生产中途人口跌回 1（本模型不会发生），已完成产能是否继续；金币/信仰购买已排除。

### 4.8 生产

C 级（Production 页逐字）：
> “Then, at the end of each turn, the city contributes its Production power to the project until it is finished. Under normal circumstances, this happens at the beginning of a turn …”
> “Projects (and units, buildings, or anything else that the city produces) may be left half-finished. **Progress is not lost**; it is simply stalled while the city turns its production facilities to something else.”
> “If the Production gain is enough to finish the current unit or building the remaining overflow will go into the next item.”
来源：<https://civilization.fandom.com/wiki/Production_(Civ6)>

可编码：
- 每回合结束时一次性累加 `prodPerTurn`；
- 切换建造**不清零**（因此“切换”是合法动作，但 MODEL 需决定是否允许；PLAN 2.2 允许逐回合切换，M5 再加完整队列）；
- 溢出进入下一项（首版只有一项可建时无意义，但需在切换场景下建模）。

**取整**：社区实测显示产能是小数（9 → 9.4，即 9×1.05 截断到 0.1）：
> “original production is 9.4 (9+0.4amenities)”
来源：<https://forums.civfanatics.com/threads/how-do-new-citizens-work.686849/>
`[推导]` 若成立，则产能桶是浮点/定点小数，`9×1.05=9.45` 显示 9.4 → 截断而非四舍五入。但该测试是在 MOD 地图（“Age of Abundance”）上做的，只能算弱证据。→ §7-F5。

### 4.9 回合内处理顺序 —— **最大未知**

现有证据只有三条，且互相不完全一致：

1. **唯一的“顺序”重构来自 Civ5 外推**（D 级）。中文教程原文（逐字）：
   > “城市的食物、工业、金币和科研点是分轮次按顺序结算的，在城市顺序上根据建造顺序结算。举例而言，假设你有ABC三个城，那么每回合点Next Turn之后，结算顺序如下：A食物、B食物、C食物、A工业、B工业、C工业、A金币… 首先会导致城市+1微操难题。当结算一个城市的食物之后人口增长，这时候增长的这个人口会被AI自动分配到一个地块上去工作，而后续的结算（工业、科研、金币）会额外结算这个新增人口的产出”
   来源：<https://gqqnbig.me/2020/05/12/【文明6过神教程】结算顺序/>
   该文开篇即自述 “文明6结算顺序应该和文明5差不多”，并引用 Civ5 论坛帖 —— 所以这是**外推，不是 Civ6 实测**。
2. **同页另一段又说 Civ6 是“先科研、后建筑”**（牛津大学案例），与“先工业后科研”自相矛盾；说明作者对不同层级（产出 vs 建筑效果）混用。
3. 维基只说“end of each turn 贡献产能、下回合开始看到结果”，不涉及食物/增长的相对次序。

因此对模型而言，**完工与增长的相对顺序必须当成参数**，至少有 4 种候选语义：
```
S1: 食物(含增长) → 生产(含完工与 −1 人口)
S2: 生产(含完工与 −1 人口) → 食物(含增长)     # 用完工后的人口算消耗
S3: 同时按回合初人口结算食物与生产，−1 人口在末尾
S4: 逐城、逐产出类型交错（Civ5 式），单城退化为 S1
```
在单城下 S1 与 S4 等价。**S1 vs S2 的差别在“完工当回合消耗 2×pop 还是 2×(pop−1)”、以及“增长是否在 −1 之前发生”**，直接影响最早回合数。→ §7-F7 是**必做且最优先**的 fixture。

另外三个同一层面的未知（都在 §6）：
- 新建城市当回合是否结算产出（F9）；
- 改分配是否当回合生效（F10）；
- 新市民当回合是否产出（F8）。

---

## 5. 对最小 Lean 模型的结论

### 5.1 必须建模（不能省）

| 机制 | 理由 | 数据 |
|---|---|---|
| 食物消耗 2/pop | 基础 | `[A][B]` |
| 增长阈值 `15 + 8(n−1) + (n−1)^1.5` | 基础 | `[B][C]`，表已核对 |
| 篮子满后清空 | 影响连续增长 | `[A]` |
| **宜居度 Happy 档 (+10% 增长 / +5% 非食物)** | 首都恒 Happy（pop ≤4） | `[A][B]` + `[推导]` |
| 城市中心免费工作 + 下限 2F/1P（平原丘陵 +1P） | 决定基线 | `[B][C]` |
| 宫殿 +2 产能 / +1 住房 / +1 宜居 | 首都基线 | `[B][C]` |
| 移民 80 产能、需 pop≥2、完工 −1 人口、费用 +30/个 | 目标本身 | `[A][B][C]` |
| 市民每回合可重分配（1 人 1 格） | 动作空间 | `[A][B]` |
| 生产进度在切换时保留 | 动作合法性 | `[C]` |

### 5.2 有条件地排除（需在证书里写出保持条件）

| 机制 | 排除条件 | 是否可满足 |
|---|---|---|
| 住房 | 淡水首都 ⇒ 住房 6；窗口内 pop ≤4 ⇒ 倍率恒 100% | 可以，但**必须证明 pop 上界**；若最优路线会到 pop 5，则 25%…50% 档必须建模 |
| 宜居度 Displeased 及以下 | pop ≤6 ⇒ 不会低于 Content | 可以（上界同上） |
| 边界扩张、改良、砍伐、购买、宗教、科技/市政、区域、单位移动 | PLAN 2.3 已排除 | 可以（但见 5.3） |
| 饥饿/人口死亡 | 最优路线不会出现负盈余；但**模型合法性**仍需定义（可设为非法动作或封顶） | 需要决策 |

### 5.3 会打破下界的“排除项”（必须在证书中显式声明）

- **政策卡 `Urban Planning`：+1 全城产能，`CIVIC_CODE_OF_LAWS` 解锁**（B 级数据，见 §2 表）。
  法典只需少量文化（宫殿 +1 文化/回合 + 人口文化 0.2–0.3/人），在 20 回合级别完全可能拿到。若允许政策，产能从 6 → 7，最早移民至少提前 1–2 回合。
  ⇒ 证书必须写“**不含政策卡的受限动作集**”，并把 Urban Planning 列为 M5 的第一个突破实验。
- 万神殿 `Religious Settlements`（直接送 1 移民）与 `Fertility Rites`（+10% 增长）：同样必须显式排除。
- `Ilkum`/`Agoge` 不影响移民（分别加 Builder / 军事单位），可不列。

### 5.4 数值表示（Lean 侧建议）

1. **禁止 `Float`**。若 fixture 证明“阈值取整 + 产能取整”，用 `Nat` 即可，模型最干净。
2. 若 fixture 证明存在小数：把 0.1 作为最小粒度用 `Int`（×10）或直接用 `ℚ`；`(n−1)^1.5` 用**区间夹逼 + 有限 n 的分段常量**处理（n≤6 时阈值分别为 15, 24, 33.828…, 44.196…, 55, 66.180…）。
3. 把三件事做成**显式参数**（而不是埋在实现里）：`thresholdRounding ∈ {floor, exact}`、`growthBonusTarget ∈ {surplus×1.1, threshold/1.1}`、`phaseOrder ∈ {foodFirst, productionFirst}`。这样 fixture 一落地就能锁定配置，且改动可审计。

### 5.5 状态与动作（草稿，供 M1）

```
state := { t : Nat, pop : Nat, food : Rat, prod : Rat, build : Build,
           worked : Finset Tile,        -- |worked| = pop
           settlersDone : Nat, hasSettler : Bool }
action := assign worked' (|worked'|=pop) | setBuild b | endTurn
step    := 依 phaseOrder 结算：food → growth → production → completion(−1 pop)
goal    := hasSettler = true（用单调历史标记，符合 PLAN 2.1）
```
注意 PLAN 2.1 的“历史标记”要求：**`hasSettler` 一旦为真不可撤销**（即使移民被删除/移动），与“−1 人口”解耦。

---

## 6. 未决问题登记

| ID | 问题 | 影响 | 现有证据 | 定夺方式 |
|---|---|---|---|---|
| **U1** | build 号未知；`Base` 数据模块反映哪个补丁？ | 高（移民 80/110 vs 80/100） | 维基模块无版本标注；2016 版 Param1=20 | 取真实安装的 `GlobalParameters.xml`/`Units.xml` + Steam build id |
| **U2** | 住房 0% 阈值是 pop−housing ≥4 还是 ≥5？（`LEFT_ZERO=-4` vs 维基“≤−5”） | 中（本场景若 pop≤4 则无关） | `[B]` 参数 −4；`[A]` 说可超 5 | fixture F11 |
| **U3** | 增长阈值是否取整；食物篮子是否可为小数 | 高（差 1 回合） | 表=floor；社区=33.8/44.1 | fixture F2 |
| **U4** | 篮子满时溢出是否保留（手册说清空） | 中 | `[A]` 清空；社区“harvest 多级”含糊 | fixture F12 |
| **U5** | 增长 +10% 是“乘盈余”还是“除阈值”，以及取整点 | 高 | 无来源 | fixture F4 |
| **U6** | 产能 +5% 后是否保留小数、如何取整 | 高 | 弱证据（9.4） | fixture F5 |
| **U7** | 完工/增长/ −1 人口的相对顺序 | **最高** | 仅 Civ5 外推 | fixture F7（多组） |
| **U8** | 新市民当回合是否产出（产能/食物） | 高 | CFC 帖先主张后撤回，实测不清 | fixture F8 |
| **U9** | 建城当回合是否结算 | 中（影响 t 与 UI 回合映射） | 无 | fixture F9 |
| **U10** | 改分配是否当回合生效 | 中 | 无 | fixture F10 |
| **U11** | pop<3 时（需求 0）是否仍判 Happy | 高（决定是否有 ×1.05 产能） | 手册/Amenities 页没排除；`[推导]` 认为会 | fixture F3 |
| **U12** | 首个移民是否 80（起手移民是否计入 previous copies） | 高 | 两条实测 vs 维基一句 | fixture F6 |
| **U13** | 难度是否给人类增长/产能修正 | 中 | 手册只说“difficulty determines … the speed at which your civilization grows” | fixture F13 |
| **U14** | 饥饿的具体结算（篮子先减？pop 何时 −1？） | 低（最优路线不需要） | `[C]` 描述含糊 | fixture F14（可选） |
| **U15** | `CITY_HOUSING_LEFT_25PCT_GROWTH` 为空 ⇒ 25% 还是 0%？ | 低（淡水场景不触发） | `[A]` 25% | fixture F11 |

---

## 7. 必需的游戏内 fixture（判别式设计）

> 每个 fixture 都写成“能区分两种互斥语义”的形式，而不是“看看数值对不对”。
> 全部要求：原版规则集、Standard 速度、Prince、无 MOD/模式、固定种子、截图存证。

### F1 — 食物消耗（基础）
- 设置：非首都城市，pop 3，Content（该城 1 免费宜居度，需求 1），工作 3 格食物合计 4（加城市中心 2 食物，总计 6 = 3×2 消耗）。
- 观察：连续 10 回合人口与“距增长回合数”不变。
- 区分：消耗=2/pop（不增长）vs 其它（会涨或饿）。

### F2 — 阈值取整（U3）
- 设置：非首都城，pop 3，Content，食物盈余**恰好 3/回合**，篮子从 0 起（用刚涨完人口的回合作为起点）。
- 观察：以“增长发生、篮子被清空”的那个回合末为 0 点；此后第 11 个回合末篮子=33，第 12 个回合末=36。**若第 12 回合末才涨 → 阈值 >33（33.828…）；若第 11 回合末就涨 → 阈值=33**。
- 记录：同时截图“城市详情 → 距离增长所需食物”，看它显示 33 还是 34。

### F3 — 首都 pop1 的宜居度等级（U11）
- 设置：新开局，立即建都，pop 1，不做任何操作。
- 观察：城市详情 Amenities 面板：可用宜居度（应为 2：免费 1 + 宫殿 1）、需求（0）、等级（Happy/Content）。
- 区分：`pop<3 也判 Happy`（⇒ 有 +10%/+5%）vs `需求为 0 时强制 Content`（⇒ 无修正）。**这是整条路线是否带乘数的分水岭。**

### F4 — 增长乘数的算术与取整（U5）
- 设置：首都 pop 1，只工作一个 **2 食物**地块（盈余恰好 2），保持分配不变。
- 观察：第 7 回合末是否涨到 2。
  - 2.2/回合 ⇒ 7 回合末 = 15.4 ≥ 15 → **涨**
  - 2.0/回合 ⇒ 7 回合末 = 14 → 第 8 回合涨
- 记录：城市详情里“每回合增长”显示 2.2 还是 2。

### F5 — 产能小数与取整（U6）
- 设置：首都 pop 1，工作使基础产能（含宫殿 2）= 9，Happy。
- 观察：① 城市面板产能显示 9.4 / 9.45 / 9？② 一回合后产能进度条增量。
- 区分：整数截断（9）vs 一位小数截断（9.4）vs 真实值（9.45）。同时决定 Lean 用 `Nat` 还是 `ℚ×10`。

### F6 — 首个移民费用（U12）
- 设置：新开局建都，打开生产列表看 Settler 的产能/金币价格；再完成 1 个移民后看第二个价格。
- 观察：80 或 110；第二个 110 或 140。
- 记录：同时导出存档的 `Units.xml` 中 `CostProgressionParam1`（20 还是 30）。

### F7 — 完工顺序（U7，最高优先，建议做 4 组）
- **F7a（增长与完工同回合）**：pop 2，移民剩余产能 ≤ 1 回合，食物篮子剩余 ≤ 1 回合增长。
  观察完工后人口：**2**（先涨到 3 再 −1）vs **1**（先 −1，再按 pop1 判定增长）。
- **F7b（消耗用哪个人口）**：同上设置，记录完工当回合的食物净变化。用 pop2 结算 ⇒ −4；用 pop3 ⇒ −6；用 pop1 ⇒ −2。
- **F7c（新市民是否加产能）**：让 pop2→3 的增长与移民完工同回合，比较该回合产能增量是否包含新市民地块。
- **F7d（−1 后篮子）**：完工后立刻看篮子数值，确认未清零（与 §4.7 的 C 级说法对账）。
> F7 的结果直接决定 §4.9 的 S1/S2/S3 选哪个，进而决定 N。

### F8 — 新市民当回合是否产出（U8）
- 设置：某个增长回合，固定分配，记录“增长当回合”的产能增量。
- 区分：包含新市民地块的产出 vs 不含。CFC 帖中主张与撤回都在此，必须实测。

### F9 — 建城当回合（U9）
- 设置：开局第 1 回合原地建都（不移动），结束回合。
- 观察：第 2 回合开始时食物篮子 / 产能进度是否已等于 1 回合的盈余。
- 目的：确定 `t` 与 UI 回合号的映射（PLAN 2.1 要求）。

### F10 — 改分配生效时机（U10）
- 设置：某回合把市民从 1F3P 换到 3F1P，结束回合。
- 观察：当回合食物/产能增量按新分配还是旧分配。
- 目的：决定动作语义是“回合初设定”还是“结算时读取”。

### F11 — 住房档位（U2/U15）
- 设置：无水城市（住房 2，无宫殿），食物盈余固定 4/回合。
  - pop 1（Housing−Pop = 1 → 50%）⇒ 有效 2/回合 ⇒ 15 食物需 **8 回合**；
  - pop 2（Housing−Pop = 0 → 25%）⇒ 有效 1/回合 ⇒ 24 食物需 **24 回合**；
  - 若实测不是 8/24，则档位阈值或取整理解有误（例如“25% 档从 Housing−Pop=0 还是 −1 开始”）。
- 再升到 pop 4/5（Housing−Pop = −2/−3）直至增长停滞，确认 0% 出现在 `−4` 还是 `−5`（U2）。
- 目的：钉死 `LEFT_ZERO=-4` 的语义；也为 M5 双城做准备。

### F12 — 篮子溢出与清空（U4）
- 设置：某回合篮子差 1 满，盈余 5。
- 观察：下回合篮子 = 0（清空）还是 4（溢出保留）。

### F13 — 难度（U13）
- 设置：同种子，Prince 与 Deity 各开一局，pop1 盈余 2，测首次增长回合。
- 目的：确认人类侧无隐藏修正。

### F14（可选）— 饥饿
- 设置：pop 3，食物总产 3（盈余 −3），观察篮子递减与人口 −1 的时点。

---

## 8. 来源清单（含逐字证据）

**A 级**
1. 2K 官方手册 PDF：<https://downloads.2kgames.com/civilization/vi/manuals/eu/CIV_VI_25TH_ONLINE_MANUAL_ENG.pdf>
   - p.95 Amenities 段（+10% 增长 / +5% 产出；unrest 停止增长）
   - p.104 “A city requires 2 food per citizen … per turn”；“MANUALLY ASSIGNING CITIZENS…”
   - p.105 “consume 2 food for each population point … Any food left over is put into the City Growth Bucket”
   - p.105 “Settlers can only be constructed in cities of size 2 or larger. When completed, the city population is reduced by 1”
2. Civilopedia（standard-rules = vanilla 规则集）
   - Growth：<https://www.civilopedia.net/en-US/standard-rules/concepts/cities_12/>（100% / 50% / 25% / 上限 +5）
   - Food：<https://www.civilopedia.net/en-US/standard-rules/concepts/cities_13/>
   - Housing：<https://www.civilopedia.net/en-US/standard-rules/concepts/cities_14/>
   - Happiness：<https://www.civilopedia.net/en-US/standard-rules/concepts/cities_16/>
   - （对照：GS 版 Happiness 数值不同：<https://www.civilopedia.net/en-US/gathering-storm/concepts/cities_16/>）

**B 级（游戏数据自动提取，build 未知）**
3. `Module:Data/Civ6/Base/GlobalParameters`：<https://civilization.fandom.com/wiki/Module:Data/Civ6/Base/GlobalParameters>
4. `Module:Data/Civ6/Base/Units`：<https://civilization.fandom.com/wiki/Module:Data/Civ6/Base/Units>
5. `Module:Data/Civ6/Base/Buildings`：<https://civilization.fandom.com/wiki/Module:Data/Civ6/Base/Buildings>
6. `Module:Data/Civ6/Base/GameSpeeds`：<https://civilization.fandom.com/wiki/Module:Data/Civ6/Base/GameSpeeds>
7. `Module:Data/Civ6/Base/Policies`：<https://civilization.fandom.com/wiki/Module:Data/Civ6/Base/Policies>（Urban Planning）
8. `Module:Data/Civ6/GS/GlobalParameters`（对照：`CITY_AMENITIES_FOR_FREE` 为空）：<https://civilization.fandom.com/wiki/Module:Data/Civ6/GS/GlobalParameters>

**C 级（百科/社区，用于语义与取整）**
9. Population：<https://civilization.fandom.com/wiki/Population_(Civ6)>（阈值表、住房表、宜居度表、每人 1 格）
10. Housing：<https://civilization.fandom.com/wiki/Housing_(Civ6)>（档位表 + 水源值）
11. Amenities：<https://civilization.fandom.com/wiki/Amenities_(Civ6)>（vanilla vs GS 分档、需求公式）
12. City：<https://civilization.fandom.com/wiki/City_(Civ6)>（中心地格下限、免费工作、初始 pop 1）
13. Production：<https://civilization.fandom.com/wiki/Production_(Civ6)>（回合末结算、进度保留、溢出）
14. Settler：<https://civilization.fandom.com/wiki/Settler_(Civ6)>（80、递进公式、−1 人口；注意“含初始移民”表述）
15. Palace：<https://civilization.fandom.com/wiki/Palace_(Civ6)>（+2 产能 / +1 住房 / +1 宜居）
16. Speed：<https://civilization.fandom.com/wiki/Speed_(Civ6)>（Standard=normal speed）
17. CFC 公式帖：<https://forums.civfanatics.com/threads/population-growth-formula.694910/>
18. CFC 2016 费用帖（含 `Units.xml` 原文 `CostProgressionParam1="20"`）：<https://forums.civfanatics.com/threads/district-settler-builder-cost-formula-october-2016.600489/>
19. CFC 新市民帖（顺序主张→撤回→实测 9.4）：<https://forums.civfanatics.com/threads/how-do-new-citizens-work.686849/>
20. Sullla（80/110/140 + Summer patch 前为 20）：<https://sullla.com/Civ6/exceedsexpectations.html>
21. Skymods 费用递进说明（1st=80, 2nd=110）：<https://catalogue.smods.ru/archives/76178>
22. Reddit 阈值小数（44.1）：<https://www.reddit.com/r/civ/comments/hyj2ac/>
23. Reddit 篮子保留/可能不掉人口：<https://www.reddit.com/r/civ/comments/vjfr96/>、<https://www.reddit.com/r/civ/comments/11i282s/>
24. 中文结算顺序（自述由 Civ5 外推）：<https://gqqnbig.me/2020/05/12/%e3%80%90%e6%96%87%e6%98%8e6%e8%bf%87%e7%a5%9e%e6%95%99%e7%a8%8b%e3%80%91%e7%bb%93%e7%ae%97%e9%a1%ba%e5%ba%8f/>

---

## 9. 阻塞项

| ID | 阻塞 | 影响 | 解除条件 |
|---|---|---|---|
| **B1** | 本机无《文明 VI》任何游戏数据（Steam 库只有 Liftoff / SteamLinuxRuntime 等；`~/.local/share/Steam/steamapps/common` 无 Civ6） | 无法核对 build、无法执行 fixture、无法从 XML 直读 | 需要在有合法安装的机器上导出 `Base/Assets/Gameplay/Data/{GlobalParameters,Units,Buildings}.xml` 与 Steam build id |
| **B2** | 维基 `Base` 数据模块无版本标注 | 常量可能与目标 build 不符（移民递进 20 vs 30 已证明会漂移） | 同 B1；或至少记录模块页面历史版本 |
| **B3** | 回合内顺序（U7）无权威来源 | N 不唯一；`OptimalAt` 命题必须先固定语义 | fixture F7（4 组） |
| **B4** | 取整/小数（U3/U5/U6）只能靠实测 | 决定 Lean 数值类型与 N | fixture F2/F4/F5 |
| **B5** | 政策卡/万神殿会打破下界 | 只能给“受限动作集”下界 | 证书显式声明 + M5 单独扩展 |

> 在这些阻塞解除前，**不得**在 `RULES.md` / 证书里写任何具体的最早回合数 N；只能写参数化结论。

---

## 10. 建议的下一步（按依赖顺序）

1. 用一份真实安装导出三份 XML + build id → 关掉 B1/B2（半天）。
2. 做 F3、F6、F9（最便宜的三个，先固定“首回合基线 + 费用 + t 映射”）。
3. 做 F4、F2、F5（数值语义三件套），据此确定 Lean 的数值类型。
4. 做 F7（4 组），锁定 §4.9 的 phase order。
5. 以上齐了再写 `RULES.md` 与 M1 引擎；`fixtures/` 至少 5 条可直接对应 F1–F7。
6. M5 第一项扩展建议就做 `Urban Planning`（可精确计算 +1 产能的收益），它是最可能突破首版下界的单点机制。
