# T266 / C282 独立本机数学验收

- checked_sha / source_sha：`eb792343d4c1d275d0341ca5dc93e17b4bc89b7d`
- mathematical_base：`307dfe985c233861eaa26acda1cc2f6ab30596d7`
- reviewed_at：`2026-10-20T12:04:34+00:00`
- reviewer：独立 Agent `/root/accept_section3`，未参与实现。
- result：**PASS，23 / 23 显式声明，无修复项**；axiom_check：**PASS**。
- scope：**AUXILIARY**。C282 可登记 REVIEWED；P024 不提升，原文覆盖保持 **20 / 26**。
- evidence_source：**local**；未查询 CI / 看板，未重复整库构建。

已直接读取固定 Git 对象中五个新模块的全部实现、raw 中全部实际类型、分析文件、MATH_SPEC 相应段落、原稿和关键实际依赖。固定 AGENTS、PROJECT_OPERATIONS、state/README 与此前已读版本不变。仅提交本报告；冻结正文与 reviewed_at，不修改实现、台账、根导入或原稿，不推送。后续 `ExhaustionHeatTransfer`、`ExhaustionPeriodicDensity`、`HeatFieldEnergies` 草稿及动态 `.ci` 不属于本次审查。

## 原文对应与实际完成范围

原 `paper/main.tex:2672–2731` 的 Proposition A.3 要求原域全部弱周期轨道、实际梯度及两个方向热残差的 \((3,1;3)\) 估计，常数先于 T；末尾的密度步骤不能省略原状态与真实场的连接。本批完成域穷竭路线中从 T265 空间系数强极限到实际周期谐波四场极限的接口，并证明零延拓下实际权范数及观察截断的精确身份。

对有界开域 S、d>0、任意递增开穷竭 \(U_n\subset S\)，设 B、\(B_n\) 分别为 S、\(U_n\) 上原 Dirichlet 梯度形式的关联模型。对每个固定 TimeGrid g、任意整数 j、任意两个原图系数 \(x,y\in B.\mathrm{operatorGraph}\)，最终定理内部构造
\[
P_n\in B_n.\mathrm{PeriodicGraph}(g),
\qquad
E_n\mathcal F_n(P_n)\longrightarrow
\mathcal F\bigl(B.\mathrm{harmonicGraph}(g,j,x,y)\bigr)
\]
于同一外域的真实四个 Bochner \(L^2\) 场的乘积拓扑。其中
\[
\mathcal F(p)=(p,\partial_t p,Ap,\nabla p),
\]
第一项准确地由原连续迹的 `pathL2` 给出，第二项是原弱时间导数，第三项是原关联算子作用，第四项是同一状态 canonical H¹ jet 的完整一阶字段；\(E_n\) 对四场逐项作真实空间零延拓。

**没有断言 \(E_nP_n\in D(A_S)\)，也没有断言 \(A_S E_nP_n=E_nA_nP_n\)。** 第三场的零延拓是一个 L² 载荷场；并未将它宣布为延拓状态的外域 Laplacian。最终结论没有 H² 零延拓、原解光滑、内域正则性或额外逼近序列输入。它仍只构造每个原谐波的四场极限；有限和、完整周期图闭包及应用统一内域 CE 到原域尚待后续，因此不能据此计 P024 完成。

## 全部声明逐项核对

名称均在 `Carleman` 命名空间；路径前缀 `Carleman/`，行号指 checked_sha。实际清单为 **17 theorem、5 def、1 abbrev，共 23 项**，与固定 C282/T266、根导入及审计打印项一致。

| 模块 / 行 | 声明 | 独立核对 |
|---|---|---|
| Spatial/SubdomainWeightedExtension:12 | `subdomainZeroExtendCLM` | **PASS**。原全空间限制算子的真实 Hilbert 伴随先延拓到全空间，再实际限制到 S；类型仅为 L²→L²。 |
| :17 | `subdomainZeroExtendCLM_apply` | **PASS**。可测内域下由实际 `restrictRegion_adjoint` 识别为既有真实零延拓，没有仅凭名称认定伴随。 |
| :23 | `subdomainZeroExtend_multiplier` | **PASS**。两个真实有界乘子的值在内域 a.e. 一致即交换；将内域 a.e. 身份转为外域中的条件身份，内外两支处理准确。 |
| :38 | `subdomainZeroExtend_seminorm` | **PASS**。在 U⊆S 的明确前提下，用上一项及真实零延拓等距性，精确保持乘权半范数，常数 1。 |
| :45 | `subdomainZeroExtend_cutoff` | **PASS**。两侧都是同一个可测 W 的实际 indicator 乘子；不要求 W⊆U，不改变观察集。 |
| :52 | `timeSq_subdomainZeroExtend` | **PASS**。使用真实 `compLp` 时间代表、同一 q、τ、s 及内域 a.e. 相同的空间 profile，真实积分精确相等，无时间或权因子损失。 |
| :68 | `subdomainTimeZeroExtend_cutoff` | **PASS**。四个实际 `coeFn_compLp` 身份在共同时间 a.e. 集上合并，应用空间交换式，得到 Bochner L² 类相等。 |
| Continuous/HarmonicLpMap:11 | `harmonicValue_norm_le` | **PASS**。实际 cos/sin 组合、三角不等式和 \(|\cos|,|\sin|\le1\) 给全频率、全时间界。 |
| :22 | `TimeGrid.harmonicLpLinear` | **PASS**。原实际谐波 L² 类的加法及数乘线性性，经实际 a.e. 代表逐项证明。 |
| :42 | `TimeGrid.harmonicLp_norm_le` | **PASS**。用真实常数函数 `timeUnit` 的范数 \(\sqrt T\) 得 \(\|h_j(x,y)\|_{L²_t}\le(\|x\|+\|y\|)\sqrt T\)，时间测度没有归一化。 |
| :50 | `TimeGrid.harmonicLpCLM` | **PASS**。原系数乘积范数下取 \(2\sqrt T\) 的连续界；实际 map 仍是同一个谐波 L² 类。 |
| :59 | `TimeGrid.harmonicLp_tendsto` | **PASS**。固定 g/j，由前项连续性把两个系数的完整序列强极限传到实际时间 L² 强极限。 |
| :64 | `TimeGrid.compLp_harmonic` | **PASS**。任意真实空间 CLM 与谐波构造交换，通过 `compLp` 的实际 a.e. 代表及线性性证明。 |
| Spatial/DirichletHarmonicFields:14 | `dirichlet_harmonic_value_Lp` | **PASS**。实际时间 Ioo 上 clamp 等于原闭区间迹，给原 harmonicGraph 的值场身份。 |
| :24 | `dirichlet_harmonic_derivative_Lp` | **PASS**。真实导数场是 \(h_j(\omega_j\,y,-\omega_j\,x)\)，两系数及负号准确；不是任意指定的导数字段。 |
| :37 | `dirichlet_harmonic_operator_Lp` | **PASS**。同一真实 domain 代表及原算子线性性给 \(h_j(Ax,Ay)\)。 |
| :43 | `dirichlet_harmonic_gradient_Lp` | **PASS**。原 trajectory 的 canonical 梯度身份、完整弱 jet 的值唯一性及真实 field CLM 给 \(h_j(\nabla x,\nabla y)\)，不使用假梯度或光滑系数假设。 |
| Spatial/DirichletHeatFields:12 | `DirichletHeatFields` | **PASS**。三个标量空间 L² 的时间 L² 与一个完整一阶导数纤维 L² 的时间 L² 的实际乘积。未把其乘积范数说成某个未经证明的平方和。 |
| :18 | `dirichletHeatFields` | **PASS**。从完整原 PeriodicGraph 到上述四场的真实 CLM，前三个字段投影与原 canonical 梯度 CLM 正确组装。 |
| :27 | `dirichletHeatFields_apply` | **PASS**。展开后严格为原 pathL2、弱时间导数、原 A 场和原梯度四元组。 |
| :33 | `subdomainHeatFields` | **PASS**。标量三场和导数纤维场分别用实际零延拓 `compLpL`，只映射公共 L² 乘积。 |
| :39 | `subdomainHeatFields_apply` | **PASS**。嵌套乘积四个位置逐项正确，没有交换 A/梯度或遗漏一个字段。 |
| Spatial/HarmonicDomainLimit:15 | `exists_dirichlet_exhaustion_harmonic_field_approximation` | **PASS**。对同一 x/y 各内部调用真实 resolvent 系数逼近，构造每个内域的实际谐波 PeriodicGraph，再将四个真实字段分别传极限并组装。没有把目标收敛作为输入。 |

所有 23 项完整打印类型均从固定 raw 第 45820 行起实际读取；最后定理的依赖类型和 P 的逐 n 原周期图资格同时与源码核对，未被打印时省略的隐参数误导。独立摘录保存在 `/tmp/carleman-t266-reviewed-types.txt`。

## 关键证明与量词

**真实零延拓与乘权。** 已直接读取 `ObservedRegionLp`、`SubdomainZeroExtension` 的定义、a.e. 身份、范数及伴随证明。`subdomainZeroExtendCLM S U` 等于 \(R_S R_U^*\)；可测 U 下 \(R_U^*\) 的实际代表为 \(1_Uu\)。一般定义不要求 U⊆S，只给限制后的扩展；精确范数保存的定理明确需要 U⊆S，最终穷竭内部提供此条件。

`subdomainZeroExtend_multiplier` 先把 U 测度下的乘子及代表身份转换为“x∈U 时成立”的全空间 a.e. 条件，再限制到 S。U 内按原代表相乘，U 外两边都是零。权函数在 U 外无须相同，所选有界常数也无须相同；只有真正的内域 a.e. 函数值一致。这正适用于同一个 Gaussian 函数在不同域上的 profile 数据。已核对 `SpatialProfile.multiplier` 的真实值是 \(q(t)^\tau e^{\rho(x)q(t)}\)，不是未指定的权族。

**时间能量与观察。** `timeSq` 的实际定义是 \(\int q(t)^s p_t(u(t))^2\,dt\)。新身份对任意实 τ/s 成立，保留同一 q 的幂次；并不是用一个常数比较时间积分。`compLp` 的时间 a.e. 身份后应用每个时间的空间精确半范数身份即可，未交换不可数 a.e. 量词。将同一 W cutoff 与该等式组合，观察始终是 U∩W；既不要求整块 W 落在 U，也不把 U 外扩展值当作额外观察质量。

通用 `timeSq` 等式本身没有额外要求 q 可测，因为它是实际积分的 a.e. congruence，并未在这里声称任意非可测 q 都有有限加权范数。对原 C² 权，真实可测性成立；已读 `WeightedTimeContinuity`，其在 `AEStronglyMeasurable w.q` 下把同一 timeSq 精确识别为真实有界加权时间 CLM 的范数平方，从而提供有限性。此处没有利用非可积时积分默认值来获得 CE 或强收敛。

**同一原谐波的四场。** 原 `harmonicValue` 是 \(\cos(\omega t)x+\sin(\omega t)y\)，`harmonicDerivative` 是 \(-\omega\sin(\omega t)x+\omega\cos(\omega t)y\)，\(\omega_j=2\pi j/T\)。已读真实 `HarmonicTrajectory`：domain 线性组合逐时合法，整数频率给周期端点相等，经典真实导数给弱时间导数，可积性由有限区间连续性内部供应。`harmonicGraph` 是该原轨道的 `toPeriodicGraph`，不是另设一个满足预期公式的对象。

梯度识别的关键是：对同一原 domain 线性组合，`dirichletDomainJet_value` 给出其实际 L² 值；`WeakSobolevJet.value_injective` 在原开域及真实限制测度上把该 jet 识别为 \(\cos(\omega t)X+\sin(\omega t)Y\)。随后实际一阶 field CLM 线性性给对应梯度组合。`dirichletTrajectory_gradient_ae` 把这个同值 jet 的字段与原周期能量载体的梯度对齐，因此输出是同一状态的真实弱梯度。全过程没有假设系数具有光滑代表或二阶零延拓。

**完整序列极限。** T265 的实际 `exists_dirichlet_exhaustion_graph_approximation` 对每个原系数 z 用内域 coercive `resolvent 0` 和实际限制的 \(Az\) 构造 \(Z_n\)，给真实值、弱梯度和算子载荷三条强极限。这里对 x 和 y 分别调用它，取 \(P_n=B_n.\mathrm{harmonicGraph}(g,j,X_n,Y_n)\)。值场和 A 场用对应两条空间极限；时间导数场用同一值极限乘固定 \(\omega_j\) 与 \(-\omega_j\)；梯度场用完整一阶字段极限。空间 CLM 与实际谐波的交换把这些极限严格识别为四个零延拓场，最后用实际乘积拓扑合并。没有选择子列、替换原极限或让四个场来自不同内域状态。

g、j 在这次极限中固定；\(2\sqrt T\) 与 \(|\omega_j|\) 仅用于连续映射传极限，可以依赖 T/j。本批没有产生或修改 CE 常数，也没有以这类常数乘上 T264 的统一 C。零延拓保权/截断身份的常数始终是 1。最终 x/y 为全部原算子图系数，包括 j=0 及负频率；没有频率除法或过滤假设。最终需要 d>0（原 Dirichlet 构造），通用 L²/谐波工具不附加维数限制。允许原域或早期内域为空，不假设每个内域有中心、光滑边界或 H² 正则性。

## 固定依赖与独立前置报告

从五个新模块递归解析 Carleman imports 得 **386** 个源模块；其中 **381** 个旧模块与 mathematical_base 的 Git blob 全部一致。实际关键入口 `InnerGraphLimit` 的 **338** 模块完整闭包与已验收 T265 proof `307dfe985c233861eaa26acda1cc2f6ab30596d7` 全不变。已重新读取其实际 resolvent 构造、原 jet/graph 身份、三条极限，以及本批实际使用的 `HarmonicGraphFields`、`HarmonicGraphContinuity`、`RegularTimeCore`、`WeakTrajectoryHeatEnergies`、`DirichletPeriodicGradient`、`DirichletHeatContinuity` 等关键连接证明。

T264 是阶段前置，其 `UniformInnerWeakHeat` **不在本批数学 import 闭包中**；本批没有暗中依赖一个待传递的 CE。另独立确认该入口 **418** 模块闭包与 T264 proof `a53469931caaf52a06accc38b94778d5e007a5b8` 全不变，供后续实际应用共同内域估计的版本边界使用。

以下冻结报告已读取，并逐字节确认固定 proof 树中的副本等于其报告提交：

| 报告 | 冻结提交 / reviewed_at | 文件大小与 SHA256 |
|---|---|---|
| T264，13/13 PASS | `128807c3503e575763831f7e3a450ecf11db7c3f` / `2026-10-20T11:33:57+00:00` | 14020 bytes；`abc484e80eb127bde959a3ac31e19d1263a67178cf69fddec6b4f3aa1af944b1` |
| T265，10/10 PASS | `eab02b1c24f9bce07a28db6e9a50c511368f3715` / `2026-10-20T11:36:44+00:00` | 11853 bytes；`5721cdd3da22b11dfd7b67b3a368cde5930a5902875a16eec83895ea4d655161` |

两批均为 AUXILIARY；既有报告没有替代本次新类型、实际调用及版本闭包核对。

## 固定本地执行与公理证据

实际读取 `/tmp/carleman-t266-local-evidence.json`：source=`local`、status=`PASS`、checked/source SHA 均为本报告 proof，`lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 记录 exit 0；finished_at=`2026-10-20T11:55:39.219022+00:00`。该 JSON 为 932 bytes，SHA256=`2d9f1e4870c93dc934c3dfd864a4f28c2f24a87dd9f0d1925624944c3d905030`。本次核对固定执行结果，没有重复构建或把本地结果称为远端结果。

| 证据（前缀 `/tmp/carleman-t266`） | 独立读取及核验 |
|---|---|
| `-local-source-manifest.txt` | **1075 条、116662 bytes**；固定树全部 tracked Lean 源及三个工具链配置的路径集合无重复/遗漏，逐 Git blob SHA256 全匹配；整体 **`8afb1f19f7e2ea638f78500bf4db97442035a053b292076c8d2bc036ecbaacd2`**。 |
| `-foundation-build.log` | 实际两个基础模块成功，**3273 jobs**；178 bytes；`9dee927efa5b434e4b3565495e26fbd1b93e9c46708e2ee80e6168403daf8d88`。 |
| `-fields-build.log` | 实际两个字段模块成功，**3539 jobs**；177 bytes；`8d42a7423d6aac24810487c394dde9b5e7d6c255e7dc512e406968d18d69a1c1`。 |
| `-target-build.log` | `HarmonicDomainLimit` 成功，**3610 jobs**；108 bytes；`4e5cf3f78180d4080c7cd6f8e046f19eb0e9ef42d57ab0615bad8fb19c5831e3`。 |
| `-root-build.log` | 根 `Carleman` 成功，**4317 jobs**；80 bytes；`f04ea5cb629a123e09a4c9a9ca148e5a42da2e20fb987397027845759b20e5e7`。 |
| `-harmonic-domain-limit-local-axioms.txt` | **3542344 bytes**；SHA256 **`e369589bd7fa47fcd461b303c16565fc8f36a7c5cff5b4e0b50b23a670465dc5`**；实际末行 **`Axiom audit passed for all 10480 Carleman declarations.`**。 |

全部 **4232** 个有公理的显式列表只含 `propext`、`Classical.choice`、`Quot.sound`，另 **10** 项无需公理。23 个新声明逐项打印并全部由固定根导入；递归审计仍遍历全部 Carleman 命名空间，含私有名还原及递归 `collectAxioms`，未缩小检查范围。没有 `sorryAx` 或新数学公理。独立复核记录为 `/tmp/carleman-t266-independent-verification.json`。临时 probe 草稿日志不作为固定版本构建证据。

Lean 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；固定 lock 与实际干净 mathlib HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿、治理协议和工具链配置相对上次已验收固定版本逐字节不变；原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 签发决定

**23 / 23 PASS，无修复项。** 本批完成真实乘权/观察零延拓身份、同一原谐波四场的精确识别及内域实际周期图四场强收敛；C282 可按此固定提交登记 REVIEWED / AUXILIARY。没有外域 H² 或 D(A) 零延拓主张，固定 T 的谐波连续界不成为统一 CE 常数。完整原域全弱周期估计尚待有限和与闭包步骤，**P024 不提升、20/26 不变**。
