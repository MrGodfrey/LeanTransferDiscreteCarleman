# T242 / C258 独立本机验收

- checked_sha: `4acd24f5158fda6688403c600ddbd9d2a131c379`
- mathematical_base: `e445f7d9d5e46db8b7a68a46769ac05442ee75bc`
- reviewed_at: `2026-10-20T08:30:14+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，16/16 显式声明（12 定理、4 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；跨边界截断的真实 H¹₀ 换域、全部测试 Poisson 方程和给定上下图域的同状态局部 H²。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/BoundaryCutoffTransfer.lean`、16 项 raw 完整类型、公理、analysis/MATH_SPEC/台账，对照原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 要求完整 Dirichlet 算子域和椭圆估计；本批是边界正则性路线中的局部截断桥接，尚未构造原域的边界图、截断覆盖或统一凸域估计。

## 实际数学与假设核对

1. **截断确可跨原边界。** η 是 `SpatialTest univ`，即真实全空间 C∞ 紧支函数；并未要求其支撑包含在原 S。原 u 是完整 H¹ jet，hu 是实际 `dirichletJetSpace S` 测试闭包资格。v 字面为原 H¹₀ 零延拓到全空间后再限制到 T；这给合法完整 H¹ 状态，且不要求 S⊆T 或 T⊆S。没有将一般 H¹ 状态或 H² 状态无条件零延拓。
2. **同一全空间测试的跨域配对。** `retarget` 保留原测试函数、光滑性和紧支，只替换合法支撑证明；其 fullJet 严格不变。对原 T 测试另有 `tsupport φ⊆S` 时，先经其真实 fullJet 将限制到 T 的配对移至全空间，再用原 H¹₀ 零延拓与限制的真实伴随配对回到 S，得完全相同的梯度配对。载荷配对使用实际 L² 零延拓/限制伴随身份，结论同样精确。这里只需要该测试的共同支撑资格，没有偷偷改成全域包含。
3. **截断作用在完整弱 H¹ 图上连续。** `cutoffWeakJet` 是已验证的 `weakFirstProductCLM`，值为 ηv，每个真实弱梯度分量为 `ηD_i v+(D_iη)v`。η 及其实际一阶、二阶 `derivativeTest` 均为真实紧支光滑函数，`valueMultiplier` 从连续紧支内部提供有限界和可测性。全部乘子资格由 η 构造，不以目标梯度或自由选择系数代替；CLM 的连续性同时覆盖值和完整一阶字段，不只是 L² 值连续。
4. **H¹₀ 换域使用正确支持方向。** `S∩tsupport η⊆T` 保证每个原 φ∈SpatialTest S 的实际乘积 ηφ 是 SpatialTest T：乘积拓扑支撑同时包含于两个因子的拓扑支撑，原 φ 支撑在 S。原测试的零延拓在全空间 AE 等于同一 φ，故截断后值与 ηφ 相同；两个已合法弱 jet 通过值唯一性得到完整相等。对任意原 u∈H¹₀(S)，从真实 H¹ 图闭包取测试 span 逼近，再将每项 span 成员还原为一个原测试。实际零延拓、限制和截断 CLM 的完整图连续性给收敛；上述逐项身份及 H¹₀(T) 的闭性遂给 ηv∈H¹₀(T)。此处不需要反向支持包含，也没有用边界点值代替原闭包。
5. **完整原方程只在合法原测试上使用。** `T∩tsupport η⊆S` 使每个目标 φ∈SpatialTest T 的 χ=ηφ 成为支撑于 S 的真实测试。由第 2 项，原 `hf:IsWeakNegativeLaplacian u f` 在 χ 上给 v 的这一特定配对等式。然后调用 H¹ 层面的 `weakGradientPairing_product_test`，得到全部目标测试下 ηv 的方程。证明从未假设未截断 v 满足全 T 的 −Δv=E(f)，所以没有丢弃原边界的分布贡献；方程这一步单独只需反向包含，最终 H¹₀ 正则性调用才同时使用两个方向。
6. **载荷及全部余项准确。** 实际定义的 L² 载荷为
   `η E(f) − ∑i [2(D_iη)D_i v+(D_i²η)v]`，
   E 是零延拓后限制到 T，v 是同一实际一阶延拓状态。两个余项都处于减号下，交叉项系数为 2，二阶截断项系数为 1。已直接读取底层逐坐标弱乘积测试和求和证明：二次项来自对 `(D_iη)v` 的合法一阶弱分部积分，未要求 v 有二阶导数。所有项由真实有界乘子作用于 L² 字段得到 L² 资格，故测试配对可积；无新增可积性、目标载荷或目标 PDE 假设。
7. **局部恢复的是同一原完整状态。** `cutoff_extendDirichlet_value_ae` 精确给目标域上的值 `η·1_S u`。通用 `exists_local_H2_of_cutoff_transfer` 明确输入目标 T 的完整 H¹₀ 弱 Poisson 解 H² 正则性 hreg；它先内部供应截断状态的 H¹₀ 和方程，再取得 V∈H²(T)。在开放 R⊆S∩T 且 η=1 的区域，将 V 真正限制到 R；AE 限制、指标函数及值身份给原 u 的值，最后原弱 jet 唯一性给 **整个 H¹ 截断**等于 `restrictSubdomain hRS u`。没有只比较值而漏掉梯度，也没有把原 u 已有 H² 当作前提。
8. **两个实际图域结论内部清偿 hreg。** 上图 T={ψ(x)<x_r} 和下图 T={x_r<ψ(x)} 的开放性由 ψ 和坐标连续性内部给出；两个 final wrapper 分别调用 T241 的实际上图/下图原 H¹₀ 弱解正则性，从而不再输入 hreg。保留的是给定全局 C∞ ψ、法向平移不变、全局高度 Lipschitz C、实际各斜率的全局 Lipschitz B_i，以及真实支持重合和 η=1 的局部条件。并未假设图域上的 H² 状态或变换后矩阵方程。结论仅给同状态局部 H² 成员及准确截断身份，没有额外声称统一椭圆常数。

一般换域 helper 允许任意开放域、空域及任意维数，不需要有限体积或有界域；全部载荷和积分通过 L² 构造合法。两个图域 wrapper 的 r:Fin d 明确需要实际法向，d=1 可用，未虚构 d=0 法向。η 不必非负或≤1。各几何输入先于任意原 u/f，未从待证正则性倒推截断资格。原边界图及这些截断的几何构造、有限局部拼接与凸域统一控制仍需后续证明。

## 全部声明逐项结论

名称统一带前缀 `Carleman.SpatialTest.`。源码行为固定 `BoundaryCutoffTransfer.lean`；raw 行为固定审计文件的完整类型位置。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 17 / 43044 | `retarget` | PASS；同一全局测试的真实支持重定域。 |
| 20 / 43048 | `retarget_fullJet` | PASS；完整全空间测试 jet 严格不变。 |
| 23 / 43051 | `extendDirichlet_pairing_of_support` | PASS；共同支持测试的真实梯度配对换域。 |
| 37 / 43059 | `subdomainZeroExtend_inner_of_support` | PASS；同一 L² 载荷及实际测试的配对换域。 |
| 45 / 43067 | `cutoffWeakJet` | PASS；真实完整弱 H¹ 乘法 CLM。 |
| 51 / 43074 | `cutoffWeakJet_value` | PASS；原乘法值身份。 |
| 58 / 43080 | `cutoffWeakJet_gradient` | PASS；全部一阶弱梯度与实际截断导数。 |
| 67 / 43089 | `cutoffTransfer` | PASS；正向支持包含给真实目标域乘积测试。 |
| 74 / 43093 | `cutoff_extendDirichlet_test` | PASS；原测试延拓截断后等于完整真实乘积 jet。 |
| 90 / 43099 | `cutoff_extendDirichlet_mem` | PASS；原 H¹ 图闭包与完整连续性给目标 H¹₀。 |
| 107 / 43105 | `cutoffTransferredLoad` | PASS；真实 L² 载荷及完整两项负号余项。 |
| 117 / 43114 | `cutoff_extendDirichlet_equation` | PASS；反向支持包含与全部原测试内部给目标方程。 |
| 146 / 43123 | `cutoff_extendDirichlet_value_ae` | PASS；目标限制测度上的 η·1_S u 精确代表。 |
| 160 / 43131 | `exists_local_H2_of_cutoff_transfer` | PASS；hreg 明示，取得同一原状态的局部 H² 和完整截断身份。 |
| 190 / 43158 | `exists_local_H2_of_cutoff_graph_epigraph` | PASS；实际上图域内部给目标正则性，无目标 H² 假设。 |
| 208 / 43183 | `exists_local_H2_of_cutoff_graph_hypograph` | PASS；实际下图域内部给目标正则性，保留同一原状态。 |

## 固定依赖与本地证据

导入闭包 **225 个 Carleman 文件**，其中 **224 个旧文件**相对 base 逐 Git blob 不变，唯一新模块为 `BoundaryCutoffTransfer`。本次完整读取该模块、`GraphDomainRegularity`、`DirichletExtensionPairing`、`DirichletSubdomainExtension`、`DirichletExtensionContinuity`、`FullSpaceTestPairing`、`FirstWeakProduct`、`WeakProductComponents`、`WeakLaplacianProduct` 和 `MollifiedProductTests` 的实际实现，核对所用弱方程、闭包、真实乘子及配对接口。T241 冻结报告全文读取并核对提交 `ac2416736394ed41c57f349c96379bf4ae4a3718`；checked_sha 为本报告 base，reviewed_at=`2026-10-20T08:23:52+00:00`，4/4 PASS。没有用该报告替代本批实际调用审查。

Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入、16 项 `#check`/`#print axioms` 均齐全。

- `/tmp/carleman-t242-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T08:27:31.051936+00:00`；`lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 实际执行记录均 exit 0。
- `/tmp/carleman-t242-local-source-manifest.txt`：**1039 项、112765 bytes**，SHA256 `370ec7632fbee07e5da5db771bead8e58311531ed850725804d6d797627514ac`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性和逐项摘要均与固定 Git blob 匹配。
- `/tmp/carleman-t242-target-build.log`：**3405 jobs** 成功，111 bytes，SHA256 `f68212c9737d144390b613c71e1e039c177ad5a2791049f4dd81b644c95cb4c3`。`/tmp/carleman-t242-build.log`：**4281 jobs** 成功，80 bytes，SHA256 `4adc476afa3f642e4b1b3dc9af55bdf43d2a08006b8bb34998a340fefac88334`。`/tmp/carleman-t242-axioms.log` 为 0 bytes。
- `/tmp/carleman-t242-boundary-cutoff-transfer-local-axioms.txt`：**3321605 bytes**，SHA256 `ea189e3d10e6d991b26c44928dfe24e9c1ab695a8983dc428429b6b432234f2c`。16 项完整类型逐项核对；全部 **3934 个显式公理记录**仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，实际尾部确认 **9937 声明递归审计 PASS**，无 sorryAx 或额外数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，未重跑全库，未查询远端 CI/看板，也未把本地成功称作 CI。

无修复项。接受本批 **AUXILIARY 边界截断弱解换域与给定图域局部 H²**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告；不修改数学、台账、原稿、根导入、公理工具或其他报告，不 push。
