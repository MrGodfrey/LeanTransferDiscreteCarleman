# T070 / C086 独立本机验收

- checked_sha: `c5e99b4f0aa241a24dcf27262fced6bc147a60d8`
- base_commit: `d13e4bc8af28b91a2c2d65091a911baa174950c4`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result: `PASS`（固定版本全部 10 项可升 REVIEWED；保持 AUXILIARY）
- axiom_check: `PASS`
- reviewed_at: `2026-10-18T22:25:23+00:00`
- scope: `AUXILIARY`。原 Dirichlet 模型 m=1 的两条 A3 加权形式估计；不提升一般 m、A1 的 H² 椭圆正则或完整 Appendix A。原文仍 **12/26**。

## 固定范围与全部 10 项声明

依项目 AGENTS 及已读治理/状态协议，直接使用 `git show` 读取固定提交三模块的全部证明和实际调用依赖，并逐名读取固定公理产物中的完整展开类型，对照原 A3（`paper/main.tex:362–372`）、Appendix A（2615–2667 行）及 `governance/analysis/T070-dirichlet-form.md`。未以执行者自检或构建成功代替数学验收，后续工作树不在范围。

三模块为 `Spatial/WeakWeightedForm`（5 项）、`Spatial/DirichletScalarForm`（2 项）、`Weights/DirichletAllowedForm`（3 项），均在 `Carleman/` 下。下列名单精确匹配固定 C086 与 `/tmp/carleman-dirichlet-form-declarations.json`；root 显式导入三模块。

| 完整声明 | 实际类型和数学核查 |
| --- | --- |
| `Carleman.weakFirstProduct_component_of_value` | 任意真实 H¹ jet v 只要其值等于 w·u，就由完整弱导数唯一性获得真实一阶乘积公式；dw_i 必须 a.e. 等于 w 的实际 fderiv 分量。 |
| `Carleman.BoundedMultiplier.map_map_comm` | 两个实有界乘子在真正标量 L² 类上交换，逐项使用 map_ae 后由 Lp.ext 证明，未进行任意代表的逐点求值推断。 |
| `Carleman.weakGradientPairing_mul_twice` | 对真实 u、v=w u、z=w v 的 H¹ jet，精确得到加权梯度平方加两倍坐标交叉项，完整梯度每个坐标仅一次。 |
| `Carleman.weakGradientPairing_weighted_lower` | 实际相对导数界 `|dw_i|≤Bq|w|`、q/B 非负，经 L² 比较、Cauchy–Schwarz、Young 与原 N 平方和给 `c=1/2`、`C=1/2+2dB²`。 |
| `Carleman.weakGradientPairing_weighted_upper` | 真互逆乘子在向量 L² 配对中抵消，梯度范数由原 N 的一阶项控制，得到常数 1 的上界。 |
| `Carleman.dirichlet_scalarForm_eq` | 原 boundedDirichletOriginalForm.scalarForm 精确等于任意具有对应真实标量值的 H¹ jet 的梯度配对；H¹₀ jet 资格由原成员资格和弱唯一性取得。 |
| `Carleman.dirichlet_scalarForm_canonical` | 将上一准确身份应用到原 domainSobolevJet，识别原 scalarForm 的 canonical 弱梯度，没有重新定义形式。 |
| `Carleman.allowed_weak_form_lower_uniform` | 原 SmoothOnClosure 内部供应全部允许权的一阶真实相对导数界；固定 C 先于 TimeWeight、τ、t、η 和三个状态，准确值身份之外无额外正规性。 |
| `Carleman.dirichlet_allowed_form_lower_uniform` | 对全部原 dirichletSubspace 状态内部供应 σu、σ²u 的成员资格和 canonical jet，再应用前项及 scalarForm 身份；不存在外加 hw、H² 或节点前提。 |
| `Carleman.dirichlet_allowed_form_upper` | 对原 scalarForm 和全部 H¹₀ 状态，使用同一 profile 及 τ/η 同时取反的真实逆权给常数 1 上界；事实上无需 profile 光滑或 |η|=1，包含全部原允许族。 |

## 实际弱梯度恒等式

`weakFirstProduct_component_of_value` 没有把 v 的导数字段作为额外自由数据：构造的 weakFirstProduct 满足原完整 SpatialTest 弱身份，v 与该构造的标量值一致，再由开域、测度集中于域的实际弱唯一性证明整个 jet 相等。调用的 `weakFirstProduct_component` 将真实 scalarZeroFiber、一阶装配和 multiplier 分量提取展开，故每个坐标是 `w D_i u+(D_i w)u`。该弱导数链不依赖 H²、网格或逐点状态光滑性。

第二次相同乘积产生

`D_i(w²u)=w²D_i u+w(D_i w)u+(D_i w)(wu)`。

新 `map_map_comm` 证明最后两项在真实 L² 中相同；真实实乘子的配对自伴身份将两项分别移到同一个配对。于是准确得到

`a(u,w²u)=‖w∇u‖₂²+2∑ᵢ〈wD_i u,(D_i w)u〉`。

已直接核查 `firstDerivativeField_inner` 通过 `Sym.oneEquiv` 对全部一阶 Euclidean 坐标恰求和一次，`derivativeField_inner` 在积分交换有限和时具有每项真实 L² 内积可积性。平方主项由 `inner_map_twice` 给出；未漏系数 2、没有把坐标平方和换成 L¹ 和或错误的多重指标重复计数。一般乘子可有符号，等式仍是实乘子自伴公式；允许 σ 为正是后续确立相对界与逆权所用。

平方权由同一实际 σ 连续作用两次形成，既没有把双指数当作仍需满足 |η|=1 的单次允许权，也没有扩大原数值允许权族。

## Young 下界与原 N 平方和

记 `U=‖wu‖₂`、`a_i=wD_i u`、`b_i=(D_i w)u`。真实有界乘子的 a.e. 相对比较给 `‖b_i‖₂≤BqU`。代码先用实际内积 Cauchy–Schwarz 得 `〈a_i,b_i〉≥−‖a_i‖‖b_i‖`，再结合 `(‖a_i‖−2‖b_i‖)²≥0` 得

`‖a_i‖²+2〈a_i,b_i〉≥(1/2)‖a_i‖²−2(BqU)²`。

这里 hq、hB 和 seminorm 非负性先保证平方比较方向合法，未对任意有符号量直接平方。有限坐标求和准确产生 d，得到 `(1/2)‖w∇u‖²−2dB²(qU)²`。

已直接读取 `WeightedSobolevNorm` 和 `HeatNormSquare`：N 是实际加权导数字段平方和的平方根，m=1 时严格等于

`N_w(u)²=q²‖wu‖₂²+‖w∇u‖₂²`。

将上式代入，恰得 `(1/2)N_w(u)²−(1/2+2dB²)(q‖wu‖₂)²`，正是原 A3 m=1 的低阶扣除项。没有将 parameterNorm 的 L¹ 和误当成 N，也没有遗漏质量项导致 C 少掉 1/2。`q‖σu‖₂=‖qσu‖₂` 由 q≥0 的真实标量范数恒等式成立。

所有量均来自已构成的 L² 状态/导数字段及有界乘子，配对和平方密度真实可积；没有利用不可积函数积分默认值为零。底层结论允许 q=0、d=0，有限和和非负性分支仍合法；最终原 scalarForm 实例明确要求 d>0，恰符合原论文 d≥1。

## 实际逆权上界

`weakGradientPairing_weighted_upper` 对完整一阶向量字段使用 `BoundedMultiplier.inner_inverse`：由 w(x)ξ(x)=1 a.e. 得加权配对等于原配对，再用真实 Hilbert Cauchy–Schwarz。两侧完整梯度范数分别不超过 N_w(u)、N_ξ(v)，因此上界常数确为 1，不含维数、q 或状态因子。

最终 ξ 的实际值为 `q(t)^(-τ) exp((-η)ρq(t))`。代码逐点以 q(t)>0、实幂取负及 exp 取负证明 σξ=1；没有把仅 η 取反遗漏 q 的倒数幂。上界不涉及乘积状态的弱导数，故无需光滑性或权保持条件；省掉 hρ/hη 是有效的更强上界，不是遗漏它们而错误使用依赖。

## 原 scalarForm 与全部 H¹₀ 状态

已直接读取 `OriginalForm`、`DirichletForm`、`DirichletDistribution`、`SobolevHilbert` 和 `domainSobolevJet`。`boundedDirichletOriginalForm` 的 V 是原 `dirichletSubspace S`；其 Hilbert 能量态由真实 H¹₀ jet 实现，形式定义就是 L² 梯度内积，已证有界对称及 Poincaré 强制性。`OriginalForm.scalarForm` 通过真实双向 valueEquiv 将此形式拉回 V，并非一个新选的估计目标。

`dirichlet_scalarForm_eq` 由输入 u、v∈原 V 及 U、V 的准确值身份，先使用 `mem_dirichletJetSpace_iff` 内部证明 U、V 属于原 H¹₀ 闭包，再形成 `dirichletJetEnergy`。valueEquiv 在这两个能量态上的值恰是原 u、v；调用 `scalarForm_value` 后，展开能量态的真实 gradient 恰得 weakGradientPairing U V。PiLp 的 H¹ Hilbert 范数转换没有改变字段或形式。

canonical 版本使用 `domainSobolevJet`——原标量值映射线性等价的逆——及其准确值定理。下界 wrapper 对同一 u 形成 J(u)、J(σu)、J(σ(σu))，这三个 canonical jet 的值关系均由实际 conformingWeight 定义及 domainSobolevJet_value 内部证明；`conformingWeightedNorm` 正是该 J 上的原 N。没有选一个有利梯度来减小 N，或把全 V 缩到节点态/算子域。

`hp` 是内部定义的函数，调用已证明 `allowed_weight_mem_dirichlet` 对每个 v∈H¹₀ 供应 σv∈H¹₀；它不是最终定理的额外输入假设。两次 hp 使右端 σ²u 合法，而整个结论量化全部原 dirichletSubspace 状态。没有 H²、Laplacian 存在、网格、节点或边界点值条件。

## 统一常数与原假设

`allowed_weak_form_lower_uniform` 在引入任何 w、τ、t、η 或状态之前，从 `(hρ.boundedSmoothOn hb).allowedWeight_word_uniform hS 1` 取得 B>0，再固定 `C=1/2+2dB²>0`。已核查该实际依赖：原 SmoothOnClosure 的域内真实导数通过有界域紧闭包连续延拓给固定有限阶界；真实允许权的相对 wordDerivative 界是 `|D_iσ|≤Bqσ`，B 先于 q≥1、所有实 τ 和两种符号。q^τ 是纯空间常数，不进入 B；η 的绝对值为 1。

之后才用当前参数形成真实 σ 的 BoundedSmoothOn、选择实际 `intrinsicWordMultiplier [i]` 并证明 hdw。固定权的绝对乘子界可依赖 q、τ；这里只用于构成 L² 乘子和成员资格，未进入上述统一 B/C。最终 wrapper 原样沿用此 C，选择顺序保持。故 C 可依赖固定 d、域和 profile，但不含 T、qmax、β、τ、时刻、符号、状态或任何网格。

SmoothOnClosure 是原 ρ∈C∞(closure Ω) 的内在表达，域外不需光滑延拓。原有界 Lipschitz 域满足所需有界开域；d>0 对应原 d≥1。最终对所有实 τ 和所有时刻成立，包含原 |τ|≤τ*、t∈[0,T]；不要求缩小允许族。ρ 的原负性、域凸性等在本阶段不必要，省略不削弱所需原结论。空开域没有挑选状态或单元的问题，所有真实限制 L² 类及形式仍合法。

## 原文范围、依赖和构建

本批直接证明原 A3 的 `eq:unshiftedformbound` 与 `eq:unshiftedcoercive`，限定实际 Dirichlet 梯度形式与 m=1。采用精确弱乘积和 Young 的专用证明，不需要一般 m 的 Sobolev 插值路线，结论、全状态和统一性均保留。

已读取 [T069 独立验收](T069-local-acceptance.md)，其 checked SHA 正是本阶段基线，确认其所界定原 Dirichlet m=1 A2 范围。另直接核对本批对 `WeakProductComponents`、`DirichletAllowedWeight`、`IntrinsicDerivatives`、真实配对/范数及 original form 的使用；T067 已验收权保持模块的 51 模块依赖闭包与 SHA `604328efce1cc28e4d6fe6cadcdaa039ee0e76a3` 逐字节一致。本批不需要把旧算子域假设或 H² 正则作为 A3 的隐藏前提。

三新模块的项目导入闭包共 87 模块，84 个既有模块与基线逐字节不变。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；治理协议、CI workflow 和工具链 pin 未改。Lean 为 `leanprover/lean4:v4.35.0`，mathlib pin/本机实际 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 mathlib 工作树干净。

固定 `CheckAxioms` 仅增加本批逐项 `#check @...` 和 `#print axioms ...`；原 namespace/privateToUserName 全量递归 collectAxioms 保留。10 项完整展开类型逐项检查，公理集合均仅 `propext`、`Classical.choice`、`Quot.sound`；固定产物全部 1474 条显式公理输出也仅含标准基础公理，无 sorryAx。新模块无 sorry/admit 或新数学公理。

实际 `/tmp/carleman-dirichlet-form-full.log` 包含 `Build completed successfully (3674 jobs).`，末行全部 **5141** 声明递归审计 PASS。固定 `/tmp/carleman-dirichlet-form-local-axioms.txt` 为 **1,518,792 bytes**，SHA256 **`23b9fd771987e87ebaa7c492e7678987142ca8f81dd74fd969f808f03bae0b39`**。

已独立读取 GitHub 实际 run、jobs 和 artifacts API：[main/push run 39171869831 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39171869831/attempts/1) 为 completed/success，head SHA 与 proof SHA 精确匹配。全部三个 jobs 同 SHA 且 completed/success：state-check（117806444255，2026-10-18T22:21:40Z）、lean（117806444384，22:24:48Z）、dashboard / snapshot（117807159464，22:24:59Z）。未因产物先可下载就将仍运行的 job 判为通过；本次在全部完成后签发。

实际 artifacts API 中 `lean-ci-result`（12153295357）及 `lean-declaration-evidence`（12152504319）均绑定上述 run、main 和同一 SHA，且未过期。已直接读取 `/tmp/carleman-dirichlet-form-main-ci/result.json`：status PASS，checked_sha=source_head_sha=`c5e99b4f0aa241a24dcf27262fced6bc147a60d8`，ci_url 精确对应该 attempt，finished_at=`2026-10-18T22:23:56.503159+00:00`，targets 为 Carleman。实际 Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）与 mathlib pin 均匹配；此 result 生成时间与最终 jobs 完成时间分开记录。

已读取原始 `/tmp/carleman-dirichlet-form-main-axioms/axioms.txt`，与固定本机副本逐字节完全相同：**1,518,792 bytes**、SHA256 **`23b9fd771987e87ebaa7c492e7678987142ca8f81dd74fd969f808f03bae0b39`**。再次逐名核对远端 10 项公理，并检查全部 1474 条显式公理输出，均只含正常基础公理；末行实际为全部 **5141** 声明递归审计 PASS。未混用后续工作树产物。

## 验收决定

**T070 / C086：PASS，可升 REVIEWED，scope 保持 AUXILIARY。** 固定 10 项及其所声称 Dirichlet m=1 A3 范围均已通过，未发现原形式、完整状态、真实弱导数/逆权、常数量词或依赖中的数学缺陷。

本阶段下界 c=1/2，C 由固定 profile 导数界先于所有权参数及状态选择；上界常数为 1。两条估计直接针对原 scalarForm、原 canonical N 范数和全部 H¹₀ 状态。完整 A1/H² 椭圆正则、一般 m、完整 Appendix A 及相应完整原文命题不因此提升，原文仍 12/26。本次仅写本报告，未修改实现、台账、原稿或 root，未 commit/push。
