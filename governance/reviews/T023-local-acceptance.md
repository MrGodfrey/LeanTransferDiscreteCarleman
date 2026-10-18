# T023 — 原 Corollaries 2.2–2.3 独立本机验收

- `checked_sha`：`8706e95e3a24b09fe6e2675a0c72c827ba9a93f3`
- `reviewed_at`：`2026-10-18T15:14:51+00:00`（UTC）。
- reviewer：独立本机验收 Agent `/root/accept_spatial_foundations`。
- targets：C011/P002（`cor:general-scales`）、C012/P003（`cor:scales`）；七个新模块、23 项显式声明。
- `result`：**PASS**（完整原 Corollaries 2.2–2.3）。
- `axiom_check`：**PASS**（同 SHA 真实 CI，3224 项递归审计）。
- scope：`PAPER`；`extra_hypotheses=[]`。

本报告由非执行者独立读取固定提交的实际 Lean 类型、证明和依赖形成。源码从该 SHA 导出到 `/tmp/carleman-scales-review-8706`；不审核执行者正在继续开发的工作树。对照原 `paper/main.tex` 两条推论（599、617 行起）和原证明（1415–1455 行），以及原误差尺度、缺陷和 Theorem 2.1 两版结论。执行者 analysis 文档仅用于定位，不作为证明或验收依据。

## 原命题与完整输出

原 Corollary 2.2 在 Theorem 2.1 的解析、数值假设下，假定统一近似阶

`aE ≤ Cap h^m`，`a0+ηA ≤ Cap h^(2m)`，

并定义 `νE=max(d*,4m+d*−c0,0)`、`ν0=max(b*,4m+b*−c0,0)`。它要求存在正的 κ、h0、Δ0、C，使原载荷版 `eq:finalCE` 和原稳定右逆残差版 `eq:rawCE` 在

`h≤h0`、`dt≤Δ0`、`Q≤κ min(h^(−αx),dt^(−αt))`

下成立。固定代码的 `Section5.ScaleUniform` 保留这两个完整结论：载荷版量化任意方向 s、节点载荷 f 和满足实际方程 `D_s z+A_h z=Γf` 的完整状态 z；残差版量化任意满足原稳定性条件的普通右逆 I 和任意完整状态 z。左右两边继续使用同一 `sobolevGeometry` 的真实节点能量、载荷、观测及状态残差加权平方范数。

第二版仍明确需要原右逆条件 `Γ(Iz)=z` 和原平方范数稳定性，符合 `eq:rawCE` 的条件；未误称没有右逆假设也能得到残差版。第一版未增加右逆、线性 I、谱截止、光滑核心或指定构造解条件。两版是同一 κ、h0、Δ0、Cfinal 的合取，而不是仅保留一版或一个标量预算。

`OriginalForm.scale_uniform` 内部调用已验收的 `a.transfer_uniform`，随后用真实 `scale_uniform_of_transfer` 取得上述完整结论。中间复用引理的 `TransferUniform` 输入在最终入口中已清偿；最终原入口没有把目标估计、TransferBridges、误差估计或六项小量条件作为额外假设。

## 分母省略与指数边界

`nuEnergy`、`nuL2` 的嵌套 max 与原三项最大值完全一致。`omittedRatio cap p ν` 在 ν=0 时返回外层已有的 cap，空间为 1、时间为 1/2。由于该 cap 已参与同一 minimum，返回它恰好省略零分母项；没有以 Lean 的 `p/0=0` 代替原约定。

νE≥0 由 d*≥0 得到；ν0>0 由原 c0>0 和 b*≥c0 得到。因此原假设允许 νE=0，ν0=0 则不可能。`omittedRatio_pos` 和 `mul_le_of_le_omittedRatio` 均分别处理零分母与正分母，后一项在零分母时使用 `0≤p`，没有乘除零的漏洞。

`scale_bounds` 实际证明 αx、αt 正，αx≤1、αt≤1/2，以及四条预算不等式

`αx νE≤2m`、`αx ν0≤4m`、`αt νE≤1`、`αt ν0≤2`。

`scale_monomial_le` 在 0<x≤1、Q≥0、κ≥0、ν≥0 下，由 `Q≤κ x^(−α)` 和 `αν≤p` 推出 `x^p Q^ν≤κ^ν`。证明利用真实实数幂单调性与正底数乘法，剩余幂为非负的 `p−αν`，从而 `x^(p−αν)≤1`。该引理对 ν=0 的输出仅为 ≤1；后续并未误用此输出使零次幂变小。

## 两种误差尺度、两个缺陷与四个小量

`approximation_rates` 从原 `εE=aE+ηA+sqrt(dt)`、`ε0=a0+aE²+ηA+dt` 推出

`εE²≤M(h^(2m)+dt)`、`ε0²≤M(h^(4m)+dt²)`，

其中 `M=8Cap²+2(Cap+Cap²)²+2>0`。在 0≤h≤1 下先证明 ηA≤Cap h^(2m)≤Cap h^m；能量平方使用 `(a+b)²≤2a²+2b²`，L² 平方保留 aE²，再使用同一平方不等式。sqrt(dt) 的平方由 TimeGrid 的 dt>0 清偿。Cap=0 时 M 仍正，选阈值不出现除零。没有漏掉 ηA、交叉项或时间平方。

`defects_le_budget` 对 Q≥1 将实际 Λf 和实际 Λz **各自**控制为

`εE² Q^νE + ε0² Q^ν0`。

原状态缺陷的 `max(1,Q^(4m+d*−c0))` 和对应 L² 项均完整保留，由 ν 的 max 定义和 Q≥1 控制。特别是可能为负的原状态指数没有被直接替换成缺少 max 的 Q 幂。原证明写 Λf+Λz≤常数乘预算；代码改为分别控制二者即可同时满足其各自阈值，数学作用相同。

`exists_scale_smallness` 设 `ε=min(1,cStar)/(4M)>0`，先对正指数选取 κE、κ0，再取

`κ=min(δx,sqrt(δt),κE,κ0)>0`。

由此 κ≤δx、κ²≤δt。h0 由 m>0 和

`h^m≤r=min(ε,1/(Cap+1),ηstar/(Cap+1))`

选定；Δ0 取 `min(1,ε)`。这些量全在输入任意 TimeGrid、h、Q、误差之前选定。

四项 `h^(2m)Q^νE`、`dt Q^νE`、`h^(4m)Q^ν0`、`dt² Q^ν0` 在证明中分别 ≤ε。正指数分支调用真实幂阈值和四条指数预算；νE=0 分支直接使用 `h^(2m)≤h^m≤r≤ε` 与 `dt≤Δ0≤ε`，从未要求 κ⁰≤ε。ν0 始终正，其两项由 κ0 控制。

乘以 M 后四项总和≤`4Mε=min(1,cStar)`，因此真实 Λf≤1、Λz≤cStar。同时 h0 的选择给出 aE≤1、ηA≤ηstar；αx≤1 和 2αt≤1 给出 `hQ≤κ≤δx` 与 `dt Q²≤κ²≤δt`。六项所需小量都在内部证明，无额外 h/dt 耦合限制或最终误差前提。

## 常数顺序、原权族和热方程

`ScaleUniform` 的 κ、h0、Δ0、Cfinal 在 X/F/Y、R/J/G、A_h、刚度、Γ、B*、三类范数、TimeGrid（包括 T）、权 w、mesh、误差、载荷和状态之前存在。两方向 s 在同一输出中量化，故常数共同适用于正反方向及所有状态，并保持 T 统一性。h0、Δ0≤1 是选定阈值的加强，h>0 是原正网格参数；Cap 是固定统一近似常数，允许阈值依赖 Cap 与原固定数据。

最终入口保留原 `TimeWeightRegularity`、原 `AllowedFamily`、原 `NumericalData` 的 N1–N5 和原 A4 的实际周期弱轨迹估计；实际连续残差中的方向符号、导数和连续算子均不变，最终离散残差仍为 `D_s z+A_h z`。覆盖条件仍为 `max(d*/2,b*/2)≤τStar`。调用 Theorem 2.1 时数值权族范围、空间能量、非正交重构及实际权函数完全不变，没有扩大到新的指数族，也没有新增可积性要求。本阶段只用已经证明的完整 Theorem 2.1 作最后转移，因而不产生额外 T、节点数或时间积分因子。

`CarlemanExponents.heat` 的实际字段为 m=1、c0=3、c:Fin 1→1、o=3，满足原指数约束。`heat_scale_exponents` 由 Lean 计算证明

`(d*,b*,νE,ν0)=(1,4,2,5)`，`(αx,αt)=(4/5,2/5)`。

`OriginalForm.heat_scale_uniform` 调用完整一般推论，再用这两条指数等式改写完整 `ScaleUniform` 结论，确实得到原 Corollary 2.3 的两版估计和共同阈值。其结论仍在原解析、数值与近似假设下；这与原文相同，并不宣称本阶段已实现后续有限元/有限差分方案。

## 23 项显式声明逐项结论

表中模块路径均相对于 `Carleman/Transfer/`。C011/T023 的固定名单为全部 23 项；C012 的固定名单为其中第 11、12、23 项，共享声明只审核一次。

| # | 完整声明 | 固定模块及行 | 独立核查结论 |
| --- | --- | --- | --- |
| 1 | `Carleman.CarlemanExponents.nuEnergy` | `ScaleExponents.lean:12` | PASS；原 νE 三项 max。 |
| 2 | `Carleman.CarlemanExponents.nuL2` | `ScaleExponents.lean:13` | PASS；原 ν0 三项 max。 |
| 3 | `Carleman.CarlemanExponents.omittedRatio` | `ScaleExponents.lean:15` | PASS；零分母返回已有 cap，等价于从 minimum 省略。 |
| 4 | `Carleman.CarlemanExponents.alphaX` | `ScaleExponents.lean:17` | PASS；原三个空间上限及零分母约定。 |
| 5 | `Carleman.CarlemanExponents.alphaT` | `ScaleExponents.lean:19` | PASS；原三个时间上限及零分母约定。 |
| 6 | `Carleman.CarlemanExponents.nuEnergy_nonneg` | `ScaleExponents.lean:22` | PASS；保留可能为零的能量指数。 |
| 7 | `Carleman.CarlemanExponents.nuL2_pos` | `ScaleExponents.lean:23` | PASS；严格正性来自原 c0>0 和 b*≥c0。 |
| 8 | `Carleman.CarlemanExponents.omittedRatio_pos` | `ScaleExponents.lean:25` | PASS；零与正分母分别处理。 |
| 9 | `Carleman.CarlemanExponents.mul_le_of_le_omittedRatio` | `ScaleExponents.lean:32` | PASS；零分母仅需 0≤p，正分母合法相乘。 |
| 10 | `Carleman.CarlemanExponents.scale_bounds` | `ScaleExponents.lean:39` | PASS；两个正指数、两个 cap、四条预算全部给出。 |
| 11 | `Carleman.CarlemanExponents.heat` | `ScaleExponents.lean:56` | PASS；实际 m=1、(3,1;3) 的完整指数对象。 |
| 12 | `Carleman.CarlemanExponents.heat_scale_exponents` | `ScaleExponents.lean:66` | PASS；实际计算 1、4、2、5、4/5、2/5。 |
| 13 | `Carleman.exists_small_rpow` | `ScalePowers.lean:10` | PASS；对任意正 p、ε 真实构造正阈值≤1。 |
| 14 | `Carleman.scale_monomial_le` | `ScalePowers.lean:17` | PASS；实数幂代数和非负剩余指数；正确覆盖 ν=0。 |
| 15 | `Carleman.ErrorScales.approximationConstant` | `ScaleRates.lean:12` | PASS；固定近似常数的统一平方预算 M。 |
| 16 | `Carleman.ErrorScales.approximationConstant_pos` | `ScaleRates.lean:14` | PASS；包括 Cap=0，M 始终严格正。 |
| 17 | `Carleman.ErrorScales.approximation_rates` | `ScaleRates.lean:18` | PASS；从实际 aE/a0/ηA 推出两条正确平方率。 |
| 18 | `Carleman.ErrorScales.defects_le_budget` | `ScaleBudgets.lean:10` | PASS；实际载荷与状态缺陷分别受同一预算控制，保留 max(1,·)。 |
| 19 | `Carleman.exists_scale_smallness` | `ScaleSmallness.lean:11` | PASS；四个单项、νE=0 分支及全部六项小量内部清偿。 |
| 20 | `Carleman.Section5.ScaleUniform` | `ScaleUniform.lean:26` | PASS；原两版完整结论、全状态、两方向、T 统一的量词顺序。 |
| 21 | `Carleman.Section5.scale_uniform_of_transfer` | `ScaleUniform.lean:60` | PASS；逐项供应六个小量，调用实际完整 TransferUniform。 |
| 22 | `Carleman.OriginalForm.scale_uniform` | `ScaleUniform.lean:90` | PASS；内部取得已证原 Theorem 2.1，无剩余桥或目标估计前提。 |
| 23 | `Carleman.OriginalForm.heat_scale_uniform` | `HeatScaleUniform.lean:24` | PASS；将完整一般推论实例化为原热方程 4/5、2/5 两版估计。 |

## 固定版本与依赖

全部 23 项与固定版 T023/C011、C012 子集、`/tmp/carleman-scale-declarations.json` 及显式类型/公理审计名单相符；七个模块均由固定 `Carleman.lean` 导入。七模块本地 import 闭包含自身共 247 模块，根导入闭包共 271 模块。

与已经独立验收的原 Theorem 2.1 基线 `5fbbfa1714af4a34facdf933a0f37736a4b7e6cd` 比较，本次仅新增七个数学模块，并修改根导入与审计名单；新模块 import 闭包中没有任何既有数学依赖变化。工具链和 mathlib pin 均未变化。已读取固定树中的 [T022 独立验收报告](T022-local-acceptance.md)，并独立检查本次使用的 `OriginalUniform`、`OriginalData`、原权与误差接口及其实际实参。复用已验收且源码不变的上游结果，不把执行者说明视作依赖验收。

## 构建、公理及真实 CI 证据

本机 `/tmp/carleman-scale-full.log` 记录 `Build completed successfully (3461 jobs).`。保存的固定审计副本 `/tmp/carleman-scales-review-8706-axioms.txt` 为 909816 字节，SHA256 为 `8ae1c19c08a7052e0249209f5f6261821ffe24eb5b918a5cb6e7a5772305357c`；末尾记录 `Axiom audit passed for all 3224 Carleman declarations.`。

已逐项读取全部 23 项的 elaborated 类型与公理输出，均仅含 `propext`、`Classical.choice`、`Quot.sound`。固定 `tools/CheckAxioms.lean` 的全环境检查递归收集公理，覆盖还原私有名后的全部 Carleman 声明，任何非允许公理都会使审计失败。没有 sorryAx 或未清偿数学公理；正常基础公理不列为额外数学假设。

通过 GitHub connector 独立读取 [main CI 39139005595 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39139005595/attempts/1) 的实际 run 与 jobs：`head_sha=8706e95e3a24b09fe6e2675a0c72c827ba9a93f3`、`head_branch=main`、`event=push`、`status=completed`、`conclusion=success`。`state-check`（117709349740）、`lean`（117709349962）、`dashboard / snapshot`（117710302499）均成功。Lean 的实际 proof target 构建、checked source 记录及两项证据上传步骤均成功。

实际读取同次下载的 `/tmp/carleman-scale-main-ci/result.json`：`checked_sha` 与 `source_head_sha` 均为本次审核 SHA，`status=PASS`、目标 `Carleman`，`finished_at=2026-10-18T15:09:46.419126+00:00`。Lean 4.35.0、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定源码锁定文件一致。结果 JSON 的 SHA256 为 `2b1effccbb4bace86b5946e34f205829ad27e3ee3eed7b5802f89e07de24c961`。

最终公理证据使用同次 CI 下载的 `/tmp/carleman-scale-main-axioms/axioms.txt`，实际逐字节比较确认与上述固定本机副本完全相同，SHA256 同为 `8ae1c19c08a7052e0249209f5f6261821ffe24eb5b918a5cb6e7a5772305357c`。已在该 CI 文件再次逐名核对 23 项 elaborated 类型与基础公理集合，并核对完整 3224 声明审计结尾。未混用后续源码的审计文件。原 `paper/main.tex` SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，本阶段保持不变。

## 结论边界

C011/P002：**PASS**，完整原 Corollary 2.2。C012/P003：**PASS**，完整原 Corollary 2.3。23 项声明的独立语义核查、同 SHA 真实构建和递归公理检查均通过，未发现阻断缺陷；可在本报告固定 SHA 下升级相应 claim 与论文覆盖结果为 `REVIEWED/PAPER`，保持 `extra_hypotheses=[]`，并关联本报告与同 SHA 构建证据。

本次验收范围仅为这两条原尺度推论及其七模块依赖组合；不自动验收后续空间离散实现、可控性、收敛或整篇论文。

本次仅写入本报告，未修改数学源码、根导入、论文、台账或覆盖表，未 commit/push。
