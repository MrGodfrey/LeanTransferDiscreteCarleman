# T222 / C238 独立本机验收

- checked_sha: `a3993a7a580ebab556f2a780ecb0ac3f81942390`
- mathematical_base: `e9e50330857e19ec60f3f65e664f9b240029fdcc`
- reviewed_at: `2026-10-20T05:49:36+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，13/13 显式声明（9 定理、4 定义），无阻断缺陷。**
- scope: **AUXILIARY；C238 可按本范围验收，原文 17/26 不变。**

已完整读取固定 Git 对象中的两新模块、13 项 raw 类型及公理记录、相关原定义和关键证明，核对固定分析、MATH_SPEC、C238/T222 清单及 `paper/main.tex:2624–2635`。本批为原 W^{2m,∞} 系数的 Leibniz 步骤提供真实的一阶分布乘积法则，不代表一般阶算子展开、严格降阶交换子或完整 Proposition A.1 已完成。

## 数学核对

1. **原测试、原 L² 类与系数范围。** `SpatialTest S` 是所有全空间 C∞、紧支且拓扑支撑包含于 S 的实际函数；`IsWeakSpatialDerivative` 对每个这样的测试要求真实 L² 内积的分部积分等式。`BoundedMultiplier` 仅包含实际函数、a.e. 强可测性及 a.e. 有界性，`map` 是真实乘积的 L² 类。最终定理对任意开域 S、任意方向 e 和任意 u,v∈L²(S)，仅要求 D_eu=v；没有全梯度、H¹₀、迹、状态光滑性或光滑系数代表前提。
2. **紧支磨光测试确实可用。** `mollifiedProduct` 为 φ 乘实际全空间卷积 U_n=(E₀u)*κ_n；核是既有真实归一化、收缩紧支的光滑核。卷积光滑性来自原 L² 局部可积性和核的 C∞ 性，紧支与支撑包含关系来自 φ；`mulOn` 的实际值是 U_nφ。`valueMultiplier` 的界来自 φ 的真实连续紧支性质，未输入目标估计。`mollifiedProduct_toLp` 通过实际卷积、限制和乘子的 a.e. 身份识别原测试 L² 类，无 L² 点值假设。
3. **局部导数交换，没有跨边界延拓错误。** `compact_mollifier_eventually_inside` 从紧支 K=tsupport φ⊆S 的正缓冲和核半径趋零，给某个最终 n 以后所有 x∈K 的完整反射核支撑包含于 S。`DomainConvolution.zeroExtend` 的结论仍是 `IsWeakSpatialDerivative volume S`，测试域是 S，绝非 univ。随后 `reflectedWithin` 才能作为原弱导数的真实测试；反射导数负号与分部积分负号相消，得 D_eU_n=V_n。新证明只在 K 内使用该公式；K 外 φ 与其真实 Fréchet 导数均为零。因此最终 L² 等式 D_e(φU_n)=φV_n+(D_eφ)U_n 对全部域成立，而不要求 E₀u 跨边界属于 Sobolev 空间。阈值允许依赖 φ；没有将逐测试的最终性交换成所有测试的统一阈值。
4. **两项都是实际强 L² 极限。** 已直接核对 `StrongMollifierLimit`：真实卷积的 L² 成员、范数收缩和 a.e. 收敛给平方误差及 L² 范数趋零，继而得到 `spatialMollificationLp_tendsto`。限制恢复 E₀u=u，限制 CLM 与实际有界乘子 CLM 的连续性给 φU_n→φu；分别对 v 和 u 应用这一结果，结合上一项最终精确等式，得到 D_e(φU_n)→φv+(D_eφ)u。没有仅凭弱收敛通过内积，也没有要求 u 的连续代表、紧支或域外弱导数。
5. **真实弱系数测试及符号。** 对 W,DW∈L²(S) 的原弱身份逐 n 代入 φU_n，得到 ⟨W,D_e(φU_n)⟩=−⟨DW,φU_n⟩。两侧由上述强收敛和固定 W,DW 的内积连续性取极限，再以 a.e. 系数身份和 `inner_valueMultiplier` 改写，精确得到 ⟨wv,φ⟩+⟨wu,D_eφ⟩=−⟨(dw)u,φ⟩。移项即 ⟨wu,D_eφ⟩=−⟨wv+(dw)u,φ⟩，与原弱导数方向完全一致。φ 任意，最终结论是全部原测试上的 D_e(wu)=wv+(dw)u；目标乘积公式不是输入。此中间定理无需有限测度，但明确输入 W,DW 的 L² 代表身份。
6. **从有界可测系数内部供应 L² 代表。** `BoundedMultiplier.toLp` 在有限测度下由真实 a.e. 界和 `MemLp.of_bound` 构造，`toLp_ae` 保留同一原函数。`IsWeakMultiplierDerivative` 明确定义为全部原测试的 Lebesgue 积分身份 ∫_S D_eφ·w=−∫_S φ·dw；不是任意替代算子或目标状态乘积关系。`isWeakMultiplierDerivative_iff` 通过 a.e. 代表替换和原 `iff_integral` 识别为 W,DW 的 L² 弱导数。测试及其导数都属于 L²，系数代表也属于 L²，相关乘积可积；没有利用非可积积分的约定值制造空泛等式。最终 wrapper 在内部完成这一步，不额外索取系数光滑性或独立 L² 见证。
7. **量词、退化和原文范围。** 最终有限测度假设是原有界 Ω 的既有性质；开域没有增加凸性、边界正则性或延拓算子前提。所有系数代表身份均为 a.e.；不存在对不可数全部状态/测试合并零测集的步骤。e=0、空域、零测度及 d=0 未被排除，也没有正体积或非零除数要求。本批是精确身份，不引入 q、T、网格或状态相关的统一估计常数；磨光阈值和测试乘子界只用于本测试的极限。本结论可迭代的高阶系数链和实际一般系数算子交换子仍需后续证明，不能以此提升完整 A.1。

## 13 项清单

源行相对于固定 `Carleman/Spatial/` 内模块；raw 行相对于固定 `weak-coefficient-product-local-axioms.txt`。每项完整类型及实际证明/定义均已核对。

| 源码位置 | 声明 | raw 行 | 逐项结论 |
|---|---|---:|---|
| MollifiedProductTests:20 | `Carleman.SpatialTest.valueMultiplier` | 40832 | PASS；实际测试函数的有界可测乘子。 |
| MollifiedProductTests:30 | `Carleman.SpatialTest.mollifiedProduct` | 40836 | PASS；实际 φU_n，紧支光滑测试资格内部构造。 |
| MollifiedProductTests:34 | `Carleman.SpatialTest.mollifiedProduct_toLp` | 40841 | PASS；与限制后的真实卷积乘积 L² 类相等。 |
| MollifiedProductTests:50 | `Carleman.SpatialTest.mollifiedProduct_derivativeLp_eventually` | 40847 | PASS；紧支内局部导数交换，保留两个乘积项。 |
| MollifiedProductTests:83 | `Carleman.SpatialTest.mollifiedProduct_toLp_tendsto` | 40860 | PASS；真实值场强 L² 收敛。 |
| MollifiedProductTests:98 | `Carleman.SpatialTest.mollifiedProduct_derivativeLp_tendsto` | 40865 | PASS；真实方向导数强 L² 收敛。 |
| WeakCoefficientProduct:16 | `Carleman.SpatialTest.inner_valueMultiplier` | 40874 | PASS；按 a.e. 代表识别真实乘法内积，顺序正确。 |
| WeakCoefficientProduct:32 | `Carleman.IsWeakSpatialDerivative.mul_bounded_of_weakLp` | 40881 | PASS；从原系数弱身份和强极限证明状态乘积公式。 |
| WeakCoefficientProduct:58 | `Carleman.BoundedMultiplier.toLp` | 40891 | PASS；有限测度下内部构造同一系数 L² 类。 |
| WeakCoefficientProduct:61 | `Carleman.BoundedMultiplier.toLp_ae` | 40895 | PASS；与原有界可测函数 a.e. 一致。 |
| WeakCoefficientProduct:65 | `Carleman.IsWeakMultiplierDerivative` | 40898 | PASS；全部原测试的实际分布积分身份。 |
| WeakCoefficientProduct:70 | `Carleman.isWeakMultiplierDerivative_iff` | 40904 | PASS；真实系数分布身份与 L² 弱导数等价。 |
| WeakCoefficientProduct:87 | `Carleman.IsWeakSpatialDerivative.mul_weakCoefficient` | 40910 | PASS；最终只输入原弱系数及状态的该方向弱导数。 |

## 固定依赖与本地证据

实际 Carleman 导入闭包为 **123 个模块**；两新模块之外的 **121 个旧模块与数学基线逐 Git blob 不变**。已直接重读本批所用 `WeakDerivative`、`SpatialTestDerivative`、`WeightedL2`、`WeakProduct.mulOn`、`DomainConvolution`、`ZeroExtensionLp`、实际限制 CLM、`StrongMollifierLimit` 与紧支核缓冲结论；不重复无关旧证明。固定 T221 报告亦已读取，其范围是允许权形式下界，未把它当作本批弱系数乘积法则的替代证明。后续 T223 工作树及动态审计不参与本次验收。

- `/tmp/carleman-t222-local-evidence.json`：source=local、PASS，checked/source 均为上述 proof，finished_at=`2026-10-20T05:43:33.667857+00:00`；实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 记录 exit 0。本次独立读取执行记录并绑定固定源码，不声称重新执行全库，也未查询远端 CI。
- 独立枚举固定提交所有 tracked Lean 文件及三项构建配置，核对 `/tmp/carleman-t222-local-source-manifest.txt` 的路径完整性、唯一性及每个 Git blob 字节摘要：**1013 项全部相同**，109892 bytes，SHA256 `af8155178bdb798899dc6f27bc5549d25ab1d5bf419c4d1c1d1a2327b715110f`。
- 实际定向 `/tmp/carleman-t222-target-build.log`：**3295 jobs** 成功，179 bytes，SHA256 `07cd37a31ce079d029b0e6d0ed709f1b4fed7ffa083661a005794ced9e0e5a62`；实际全库 `/tmp/carleman-t222-build.log`：**4249 jobs** 成功，80 bytes，SHA256 `5b537f4e5d91695ceefde49b6dc1a8cea08e8ddde02257efb7eaa8dd7f6ca277`；`/tmp/carleman-t222-axioms.log` 为 0 bytes。
- 固定 raw `/tmp/carleman-t222-weak-coefficient-product-local-axioms.txt`：**3140762 bytes**，SHA256 `582b47b98a985203f3f98486df9c27fe3e3968ae2ea460a8294b54e7e27191a0`。13 项完整展开类型逐项读取；扫描全部 **3658 个显式公理记录**，仅正常 `propext`、`Classical.choice`、`Quot.sound` 或无公理，无 sorryAx 或新增数学公理。末行确认 **9323 个 Carleman 声明递归审计 PASS**。固定 `CheckAxioms` 的原全命名空间 `privateToUserName`/`collectAxioms` 白名单循环与基线不变；两模块根导入、13 项 #check/#print axioms 齐全。
- 固定配置为 Lean 4.35.0（编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，与证据一致。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。

本报告接受真实一阶弱有界系数乘积法则，保持 AUXILIARY / 17 of 26。签发后正文与 reviewed_at 冻结；仅提交本报告，不改数学、台账、根导入或原稿，不 push。
