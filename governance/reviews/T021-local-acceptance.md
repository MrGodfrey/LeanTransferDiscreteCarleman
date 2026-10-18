# T021 — 原 Theorem 4.2 独立本机验收

- `checked_sha`: `9d8230090dad2c5b5a2efa74f5d085728866d139`
- `reviewed_at`: `2026-10-18T14:44:07+00:00`（UTC）
- reviewer：独立本机验收 Agent `/root/accept_spatial_foundations`。
- targets：C009 / P010，原 `thm:combined`；四个新模块、13 项显式声明。
- `result`：**PASS**（完整原 Theorem 4.2）。
- `axiom_check`：**PASS**（同 SHA CI 产物，3125 项递归审计）。
- scope：`PAPER`；`extra_hypotheses=[]`。

本报告由非执行者的独立验收 Agent 阅读固定提交的实际类型、证明和依赖后形成。源码以 `git archive` 导出，未审核正在继续开发的工作树。对照固定版 `paper/main.tex` 的 `eq:spacetimegraphnorms`、`eq:error-scales`、Section 4 前提及 Theorem 4.2（1287 行起），并检查已有时间和空间估计的真实实参；执行者 analysis 文档仅用于定位。

## 原命题、实际误差和范数

`CombinedEstimate` 对每个原节点载荷 f、每个满足实际辅助离散方程的完整状态 z、每个满足实际冻结连续方程的周期图解 p，给出

\[
\|\sigma(U-R\bar z)\|_{L^2(\mathcal Q)}
\le K(\delta t+a_0+a_E^2+\eta_A)\|\sigma f\|_{\ell^2_{\delta t}(H)},
\]
\[
\mathcal N_{\sigma,\mathcal Q}(U-R\bar z)
\le K(\sqrt{\delta t}+a_E+\eta_A)\|\sigma f\|_{\ell^2_{\delta t}(H)}.
\]

两条结论与原 `eq:combinederror` / `eq:combined-l2-error` 一致，且附带完整误差弱 jet 的 `MemLp` 结论。真实离散方程保留 `D_s z+A_h z+(Lq_i)^(2m)Gz=Jf`，连续方程使用同方向的冻结乘子及 `extensionLp f`。没有把载荷改为连续范数，或把误差改为中间 Euler 解的误差。

`reconstructedError` 定义为 `inclusion(U.domainValue)−R(extension z)`，属于原 V。`reconstructedError_value_ae` 使用已有 `domainValue_ae`，证明其 H 值几乎处处等于真正的 `U−R bar z`。因此并未要求原 U 每时刻都在 D(A)；原周期图仍只承载 H 弱导数、a.e. 域值与 H 周期迹。原 `OriginalForm` 的模型域/算子与原关联算子的等同性由已验收的 Section 3 桥供应，未在本阶段换成更小的光滑核心。

`domainSobolevJet` 的 k 阶字段是真实弱空间导数字段。`parameterTimeField` 为 `q^(m−k) σ D^k`，`spacetimeWeightedNorm` 是各字段实际 Bochner L² 范数平方和的平方根。已有 `spacetimeWeightedSq_integral` 及空间字段积分等式识别原时空 N²；H 值的 `bochnerL2Norm` 是时间上的 L²(L²(Ω)) 范数。它们均为原 `L²(𝒬)` / `N_(σ,𝒬)` 的表达，没有以 H 范数替代 H^m，也没有调换 R 范数的求和顺序。

## 组合证明与可积性

`combined_estimate_of_spatial_temporal` 实际使用 `(hg f).1` 的存在唯一性构造中间空间连续 Euler 解 u，而后对同一 u、p、z 应用已验收的 `TemporalEstimate`、`EnergyEstimate`、`L2Estimate`。中间解、最终误差界或最终可积性不是原入口输入。

`reconstructedError_decomposition` 在 V 中逐点给出

`full error = inclusion(U.domainError u) + extension(inclusion u − Rz)`。

随后用真实线性 `domainSobolevJet` 得到同一弱 jet 分解。时间误差 jet 的 `MemLp` 来自 `TemporalEstimate`；空间误差 jet 序列有限，其两方向实际分片延拓由 `memLp_extension` 给出 `MemLp`。这两项相加，证明完整误差 jet 的 `MemLp`。

能量三角不等式的每阶加权字段 `MemLp` 也在证明内部由 `memLp_parameterTimeField` 供应；qmax 和乘子上界仅用于证明有限性，不进入最终误差常数。H 值 L² 三角所需两项 `MemLp` 分别来自原轨迹 `value_L2` 与有限序列延拓，再经真实权乘法保持。没有使用总化积分或总化 L² 范数在不可积处的默认值获得估计。

`spacetimeWeightedNorm_add_le` 先用每个字段的真实 Bochner L² 三角，再对有限字段向量使用 Cauchy–Schwarz，得到常数 1 的 N 三角不等式。`spacetimeWeightedNorm_congr_ae` 按实际字段传递 a.e. 相等，保证代表变化不改变范数。

## 单元比较、两方向及原权族

`spacetimeWeightedNorm_extension_le` 对每个 k 把平方密度写为原权乘子下的 `q^(2(m−k))` 时间密度，调用已有 `powerSq_timeSq_comparison_comp`。逐字段平方常数为 9；交换有限字段和与有限节点和后，恰为原节点 N²，开方得到统一常数 3，没有 m+1、节点数、T 或 sqrt(T) 损失。

指数计算使用 `|τ+(m−k)|≤τStar+m`，所以解析单元阈值取 `cellThreshold β (τStar+m) ρ.bound`。这仅扩大显式 q 幂密度的解析比较范围。`AllowedFamily`、`WeightedApproximation`、`WeightedTest` 的输入继续限定在原 `|τ|≤τStar`，空间正/逆权调用为 `(ρ.signed e,τ)` 与 `((ρ.signed e).neg,−τ)`；没有新增要求 N1/N3/N4 在 τStar+m 的数值权族成立。

全部扩展直接调用同一 `s : Orientation` 的既有真实分片延拓；其周期末格和 0/T 处理继承已验收的单元比较。主组合未进行未经证明的时间反射替换，也没有把 D− 改成错误符号。`CombinedUniform` 在共同阈值之后量化 s 和 profile 符号 e，因此两方向和正/逆权共用相同常数。

## 常数、阈值与假设边界

合成前真实估计为

`N(full) ≤ Kt sqrt(dt) F + 3 Ks (aE+ηA) F`，

`L2(full) ≤ Kt dt F + 3 Ks (a0+aE²+ηA) F`。

`combine_nonnegative_rates` 仅在最后一步用所有系数非负，合并为共同 `K=Kt+3Ks` 及原两种误差尺度。它没有被当成完整 Theorem 4.2 的替代证明。

`combined_uniform_of_section3` 明确选择

- `Lmin = max Ls (L₀ 1)`；
- `δt = min δs (min δ δc)`，`δc=cellThreshold β (τStar+m)ρ.bound>0`；
- 固定 L≥Lmin 后，从已证空间结果取得 `δx≤δnum`、`ηstar`、Ks，并取 `K=Kg+3Ks`。

这些选择在 X、R/J/G、A_h、刚度缺陷、TimeGrid（包括 T）、q/qmax、方向、权指数/profile 符号、mesh、aE/a0/ηA、载荷和状态之前完成。δx、ηstar、K 可依赖已固定的 L，符合原 Section 4 的次序；没有 T、网格数、qmax 或状态依赖。共同时间阈值被进一步缩小以同时满足已证时间、空间及新增解析比较条件，没有改变原最终率。

`OriginalForm.combined_uniform` 从原 A1 的域嵌入与正向椭圆界直接调用 `a.section3`，再内部调用完整空间组合。最终入口不保留 `EulerEstimate`、`TemporalEstimate`、空间能量/L² 估计、插值结论或中间解作为额外假设。`AllowedFamily` 仍是 A2/A3，`WeightedApproximation` 和 `WeightedTest` 仍是原 N3/N4，hA 和 hdef 是原 N1 质量/刚度关系及缺陷界。

估计量化所有满足实际方程的 z 和 p，不是一个指定构造解或低频状态。估计本身省去未用的离散有限维、R 单射、A_h 非负等前提是加强；原有限维辅助问题存在唯一性已由先前验收的结果负责。原无额外前提结论成立，不需要新增可积性、正交重构、Q²=Q 或 G=Id。

## 13 项显式声明逐项结论

| # | 完整声明 | 固定模块及行 | 独立核查结论 |
| --- | --- | --- | --- |
| 1 | `Carleman.WeakSobolevJet.parameterTimeField_add` | `Spatial/SpacetimeNormAlgebra.lean:15` | PASS；实际弱导数字段及乘子线性给出逐字段相加等式。 |
| 2 | `Carleman.WeakSobolevJet.spacetimeWeightedNorm_add_le` | `Spatial/SpacetimeNormAlgebra.lean:21` | PASS；显式 MemLp 下真实 Bochner 三角和有限字段 Cauchy–Schwarz，常数 1。 |
| 3 | `Carleman.WeakSobolevJet.spacetimeWeightedNorm_congr_ae` | `Spatial/SpacetimeNormAlgebra.lean:50` | PASS；a.e. jet 相等传到各加权字段及真实范数。 |
| 4 | `Carleman.WeakSobolevJet.spacetimeWeightedNorm_extension_le` | `Spatial/SpacetimeCellEnergy.lean:18` | PASS；两方向真实延拓，有限性内部证明，平方 9 / 范数 3，无额外时间或节点因子。 |
| 5 | `Carleman.Section4.reconstructedError` | `Section4/CombinedEstimate.lean:20` | PASS；实际 V 值完整误差代表。 |
| 6 | `Carleman.Section4.reconstructedError_value_ae` | `Section4/CombinedEstimate.lean:23` | PASS；与原 H 值 U−Rbarz 几乎处处一致，不加强逐时域正规性。 |
| 7 | `Carleman.Section4.reconstructedError_decomposition` | `Section4/CombinedEstimate.lean:30` | PASS；实际 V 中时间误差加空间误差延拓，两个方向精确代数等式。 |
| 8 | `Carleman.Section4.CombinedEstimate` | `Section4/CombinedEstimate.lean:41` | PASS；完整原误差的两种率与 jet MemLp；任意实际解和同一任意节点载荷。 |
| 9 | `Carleman.Section4.combine_nonnegative_rates` | `Section4/CombinedEstimate.lean:53` | PASS；正系数末步率合并，不承担解析估计。 |
| 10 | `Carleman.Section4.combined_estimate_of_spatial_temporal` | `Section4/CombinedEstimate.lean:60` | PASS；构造中间 u，调用实际已证时间/空间估计，内部清偿可积性并组合完整误差。 |
| 11 | `Carleman.Section4.CombinedUniform` | `Section4/CombinedUniform.lean:19` | PASS；原权族与全状态，常数先于 T/网格/离散数据，空间常数可依赖固定 L。 |
| 12 | `Carleman.Section4.combined_uniform_of_section3` | `Section4/CombinedUniform.lean:42` | PASS；共同 max/min 阈值、两方向及两 profile 正确供应，解析指数范围不外溢到数值假设。 |
| 13 | `Carleman.OriginalForm.combined_uniform` | `Section4/CombinedUniform.lean:87` | PASS；原 A1–A3/N1/N3/N4 最终入口，内部取得全部所需估计，原两种率不变。 |

## 版本及独立依赖验收

固定 SHA 的四个新模块均由 `Carleman.lean` 导入；全部 13 个声明与固定版 C009/T021 名单、`/tmp/carleman-combined-declarations.json` 和显式审计名单一致。四模块的本地 import 闭包含自身共 223 模块，根导入闭包为 259 模块。

相对于 `a315bdc449c58a705a982f0d009f1dde24d6af66`，数学源码仅新增这四模块；上游 import 闭包内既有文件、工具链和 mathlib pin 均未改变。已读取固定树中提交的 [Section 3 独立报告](T019-local-acceptance.md)、[C038/C039 独立报告](T020-foundations-local-acceptance.md) 与 [Lemma 4.1 独立报告](T020-lemma-local-acceptance.md)。本次检查它们的结果在新代码中的实际调用和实参；旧报告所核对的上游证明保持相同版本，没有把下游新增声明自动算作已审核。

## 构建与公理证据

本机 `/tmp/carleman-combined-full.log` 记录 `Build completed successfully (3449 jobs).`，完整审计末尾记录 3125 个 Carleman 声明。为避免主任务后续覆盖，已将本机审计产物保存为 `/tmp/carleman-combined-review-9d82-axioms.txt`：863091 字节，SHA256 为 `9b156ce390cd022093946babb6f0aeb2fec8312682c870375c0753838aeb2c75`。

实际逐名读取全部 13 项 elaborated 类型与公理输出，均仅含 `propext`、`Classical.choice`、`Quot.sound`。固定版 `tools/CheckAxioms.lean` 的全环境循环使用 `collectAxioms`，包括还原私有名后的全部 Carleman 声明，遇到任何其它公理即失败；产物末尾为 `Axiom audit passed for all 3125 Carleman declarations.`。不存在 sorryAx 或额外数学公理依赖。正常基础公理不列为额外数学假设。

通过 GitHub connector 独立读取 [main CI 39136913051 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39136913051/attempts/1) 的 run 与 jobs：`head_sha=9d8230090dad2c5b5a2efa74f5d085728866d139`、`head_branch=main`、`event=push`、`status=completed`、`conclusion=success`。`state-check`（117703174784）、`lean`（117703174947）、`dashboard / snapshot`（117703933590）均成功；Lean 的 `Build proof target` 和两项证据上传步骤也均成功。

实际读取同次下载的 `/tmp/carleman-combined-main-ci/result.json`，其 `checked_sha` 与 `source_head_sha` 均为审核 SHA，`status=PASS`、目标 `Carleman`、`finished_at=2026-10-18T14:40:56.301724+00:00`。Lean 4.35.0 和 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定源码锁定文件相符。结果 JSON 的 SHA256 为 `6f66670a6e88d389ddd09493cb1304fded87c03dae491afc651e598483a138e5`。

最终公理证据使用同次 CI 下载的 `/tmp/carleman-combined-main-axioms/axioms.txt`，逐字节等于上述已审核本机副本，SHA256 同为 `9b156ce390cd022093946babb6f0aeb2fec8312682c870375c0753838aeb2c75`。在该 CI 文件中再次按 13 项完整名称核对类型及基础公理集合，并确认完整 3125 声明审计结尾。没有混用较旧 SHA 或后续工作树的公理产物。

## 结论边界

13 项新声明的独立数学检查、同 SHA 真实构建及递归公理检查均为 PASS，未发现阻断问题。C009/P010 可在本报告固定 SHA 下升级为 `REVIEWED/PAPER`，保持 `extra_hypotheses=[]`，并同步上述构建、审核时间及报告引用。

此范围是完整原 Theorem 4.2；原 Theorem 2.1、最终 TransferBridges 的原假设实例及 Section 5 全部合成不在本报告验收范围。本次仅写入本报告，未修改源码、根导入、论文、台账或覆盖表，未 commit/push。
