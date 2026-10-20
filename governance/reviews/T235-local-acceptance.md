# T235 / C251 独立本机验收

- checked_sha: `ceba934191acdb2f4dfda0882a67b80094f2e23d`
- mathematical_base: `528c5bf683ace24836aecdf64ddd73422a000473`
- reviewed_at: `2026-10-20T07:30:32+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，19/19 显式声明（15 定理、4 定义），未发现阻断缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；真实全空间有界 Lipschitz 系数的差商乘积、矩阵椭圆形式及合法 Dirichlet 切向能量/测试界。覆盖保持 18/26，P023 不提升。**

已全文读取固定 `Carleman/Spatial/VariableCoefficientDifference.lean`、19 项 raw 完整类型与公理、分析/MATH_SPEC/声明清单及原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 要求一般凸多面体或盒上完整 A1–A3；本批是其边界正则性路线的变系数切向步骤，未证明一般域或曲边图上的完整 H²。只核对固定源码与本地真实执行证据，没有混入后续法向恢复代码，没有查询 CI/看板或重新构建旧闭包。

## 实际数学与前提边界

1. **真实乘子及差商乘积。** `spatialTranslate` 保留同一 a 的实际值 `a(x+z)`、原 bound 和由保测度复合得到的 AE 可测/有界资格。`spatialTranslate_map` 是原 L² 类上的乘法和平移交换身份。对代表函数的真实 `LipschitzWith C`，`|h⁻¹(a(x+hz)−a(x))|≤C‖z‖` 来自 Lipschitz 界和 `‖hz‖=|h|‖z‖`；h=0 单独处理，非零时才消去 |h|。`spatialDifference` 使用这个同一函数并内部供给可测性与步长统一 bound。随后有限个 AE 代表身份与 Lp.ext 给
   `δ_h(au)=(T_h a)δ_hu+(δ_h a)u`。
   主项明确是平移后的系数，不是 a 本身；两个项使用同一原 u。余项范数由实际乘子界给 `C‖z‖‖u‖`。没有假设系数经典可微、预设差商乘积或对任意 Lp 类取逐点值；没有在不可数 h 上合并零测集。
2. **完整矩阵实际积分与椭圆性。** `matrixL2Pairing` 定义为全部 i,j 的 `⟨aᵢⱼGᵢ,Hⱼ⟩` 有限和，保留所有非对角项与该索引次序。每项乘后状态为实际 L²，乘积为 L¹；积分和有限求和交换的可积性逐项给出。AE 椭圆性输入是对几乎处处 x 的全部实向量 ξ；在合并有限个乘子代表等式后才代入 `ξᵢ=Gᵢ(x)`，从而积分推出 `κΣᵢ‖Gᵢ‖²≤B_a(G,G)`，没有交换一个仅逐 ξ 的零测例外族。配对上界逐项用 Cauchy–Schwarz 和 aᵢⱼ.bound，常数为其完整有限和。一般测度版本无需总测度有限；κ 的正性只在后续除法能量定理明确要求。
3. **真实弱梯度和差商分部求和。** `matrixGradientPairing` 代入原 jet 全部一阶分量。已核对 `firstDerivativeField_inner` 通过真实 `Sym.oneEquiv` 精确恢复每个坐标一次，所以椭圆下界控制的是实际 field₁ 的 L² 范数平方。每个分量应用差商伴随和前述乘积公式，得到
   `−B_a(u,δ_(-h)v)=B_(T_h a)(δ_hu,v)+B_(δ_h a)(u,v)`。
   负步长、外部负号、系数平移和全部系数差商余项均保留。u,v 只需原全空间 H¹ jet，没有二阶导数输入；系数对称性不是该等式或本批能量估计的前提。
4. **原弱方程扩展到合法 H¹₀ 测试。** `matrixGradientPairing_tendsto_right` 使用实际 field/component 连续线性映射、固定乘后 L² 向量与内积连续性，给完整 H¹ 图拓扑下的测试连续性。原方程 `hf` 只量化全部 `SpatialTest S`。`matrixGradient_equation_dirichlet` 从原 H¹₀ 测试 span 的闭包取序列；每个 span 成员仍是真实紧支光滑测试。真实 H¹ 零延拓连续性及原值映射连续性传两边极限，得到全部原 H¹₀ 测试的同一方程，没有另假设推广后的弱方程或二次差商可测试。
5. **同一原方程的精确积分身份。** `matrixGradientPairing_dirichlet_integral` 将两原 H¹₀ 状态零延拓后的配对逐项化为 `∫_S aᵢⱼ(∂ᵢu)(∂ⱼv)`：梯度分量与实际 L² 零延拓交换，乘子 AE 公式、真实零延拓积分身份和限制代表恢复原 S 内分量。对测试 φ，再识别 `φ.fullJet` 与其原零延拓，并将分量换成实际 `fderiv φ`，得到 `matrixGradientPairing_test_integral`。因此 hf 的左边确为该完整散度型积分形式，右边是原载荷与测试的 L² 配对，不是抽象占位形式。全部积分的实际可积性由有界系数和 L² 分量保证。
6. **合法二次差商、符号和能量消去。** 令 U=E₀u、W=δ_hU、w=W|S。正步平移原像包含条件经 T234 给 w∈H¹₀ 及 E₀w=W；再由负步包含给 Q=δ_(-h)W 的限制 q∈H¹₀ 及 E₀q=Q。原方程遂给 `B_a(U,Q)=⟨f,value q⟩`。前项差商等式给
   `B_(T_h a)(W,W)=−⟨f,value q⟩−B_(δ_h a)(U,W)`。
   原全空间 AE 椭圆性通过真实平移保测度传给 T_h a，故左侧≥κE²，其中 E=`‖field₁W‖`。W 的已有一阶弱链给 `‖value q‖≤‖D_iW‖≤E`，不假设原 u 已 H²。单位坐标方向的范数为 1；系数误差至多 `(Σᵢⱼ Cᵢⱼ)‖field₁u‖E`，真实 H¹₀ 零延拓使原梯度范数不变。于是
   `κE²≤(‖f‖+Σᵢⱼ Cᵢⱼ‖field₁u‖)E`。
   E=0 单独处理，E>0 才约去 E；κ>0 明确保留。得到的 `E≤κ⁻¹(‖f‖+Σᵢⱼ Cᵢⱼ‖field₁u‖)` 不含 h、u 的二阶范数、目标差商界或额外网格/时间参数。h=0 仍合法。
7. **切向测试极限及明确限制。** 最终定理要求指定坐标方向的所有实数平移原像均包含于 S，因而实际提供每个 t 的正负步资格；这是全方向平移保持域的强几何条件，不能仅凭曲边边界上某向量“切向”就调用。对 G=原 H¹ 零延拓的第 i 梯度分量，证明仅将 G 当作全空间 L² 类，其真实限制精确等于原梯度。前项界控制 G 的每个步长差商限制，T233 对 hₙ=1/(n+1) 给全部原 φ 的二阶切向分布测试界，常数保持不变；未假设 G 在全空间 H¹。

本批能量和最终测试定理的系数输入确实是**全空间**有界乘子、其选定真实代表的**全空间 Lipschitz** 条件，以及**全空间 AE** 一致椭圆性。不能把域内或局部图内系数自动当成这些输入，也没有在本批构造其保椭圆延拓/局部化。没有要求有限域体积、状态光滑或有限模式；矩阵不必对称，二次型下界足够。一般矩阵辅助式允许 d=0；需坐标 i 或 j 的定理明确含 `Fin d` 元素，不伪造零维方向。法向二阶恢复、非线性边界图的弱坐标传输、一般内域正则性及统一凸域二阶估计仍待证明。

## 全部声明逐项结论

源码行均在固定 `Carleman/Spatial/VariableCoefficientDifference.lean`；raw 行在本批固定审计文件。19 项完整类型及公理记录逐项读取。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 11 / 42152 | `Carleman.BoundedMultiplier.spatialTranslate` | PASS；同一系数的实际平移及原 bound。 |
| 19 / 42156 | `Carleman.BoundedMultiplier.spatialTranslate_map` | PASS；真实 L² 乘法和平移交换。 |
| 29 / 42160 | `Carleman.BoundedMultiplier.lipschitz_difference_bound` | PASS；全步长、全方向的 C‖z‖ 界，含 h=0。 |
| 43 / 42165 | `Carleman.BoundedMultiplier.spatialDifference` | PASS；同一差商函数及内部可测/有界资格。 |
| 52 / 42170 | `Carleman.BoundedMultiplier.differenceQuotient_product` | PASS；精确平移主系数和余项。 |
| 71 / 42176 | `Carleman.BoundedMultiplier.differenceQuotient_commutator_bound` | PASS；真实乘子余项范数，与 h 无关。 |
| 82 / 42186 | `Carleman.matrixL2Pairing` | PASS；原全部矩阵分量配对。 |
| 86 / 42193 | `Carleman.matrixL2Pairing_bound` | PASS；有限系数 bound 和的真实 L² 上界。 |
| 101 / 42199 | `Carleman.matrixL2Pairing_coercive` | PASS；AE 椭圆性与实际可积性推出完整积分下界。 |
| 137 / 42204 | `Carleman.matrixGradientPairing` | PASS；原完整弱梯度矩阵形式。 |
| 144 / 42211 | `Carleman.matrixGradientPairing_coercive` | PASS；准确 field₁ 能量，无漏项或重复坐标。 |
| 155 / 42218 | `Carleman.matrixGradientPairing_bound` | PASS；原两状态全梯度范数界。 |
| 163 / 42224 | `Carleman.matrixGradientPairing_difference` | PASS；真实分部求和、平移系数及完整误差身份。 |
| 177 / 42233 | `Carleman.matrixGradientPairing_tendsto_right` | PASS；完整 H¹ 图收敛下配对连续。 |
| 192 / 42241 | `Carleman.matrixGradient_equation_dirichlet` | PASS；原测试方程内部延伸到全部 H¹₀。 |
| 212 / 42251 | `Carleman.dirichlet_variable_tangential_difference_gradient_bound` | PASS；原方程的合法二次差商给明确步长统一界。 |
| 278 / 42274 | `Carleman.matrixGradientPairing_dirichlet_integral` | PASS；同一原状态的实际域内矩阵积分。 |
| 312 / 42286 | `Carleman.matrixGradientPairing_test_integral` | PASS；原光滑测试的真实 Fréchet 导数积分身份。 |
| 329 / 42297 | `Carleman.dirichlet_variable_tangential_test_bound` | PASS；同一梯度及同一常数的全测试切向分布界。 |

## 依赖与固定本地证据

T234 冻结报告 `7083f5cee167f63308a5b133e4a9e3ab3c7bb921` 已全文读取（checked_sha 为本批 base，reviewed_at=`2026-10-20T07:19:42+00:00`，20/20 PASS）。同时直接核对实际 H¹ 平移/差商字段、H¹₀ 闭包及平移支撑、限制再零延拓身份、`DirichletExtensionContinuity`、真实 field 范数保持、完整梯度坐标配对和 `BoundedMultiplier` 的实际 map/范数界；T233 判据沿用已核验固定实现。导入闭包 **192 个 Carleman 文件**，其中 **191 个旧文件**相对 base 的 Git blob 全部不变。

- `/tmp/carleman-t235-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T07:22:45.664562+00:00`。实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0；本验收核对该执行记录，没有声称重跑全库。
- `/tmp/carleman-t235-local-source-manifest.txt`：**1032 项、111988 bytes**，SHA256 `600972214a148d26690cc3a0d7c095f350120843fd59de9f83c358fc73248dbc`。独立枚举 fixed proof 的全部 tracked `.lean` 和三项工具链配置，路径集合完整、无重复，每项 Git blob 摘要均匹配。
- `/tmp/carleman-t235-target-build.log`：**3372 jobs** 成功，118 bytes，SHA256 `68a12723140e6f9bd4194c7c249c33d114bea2d53a4c515b46b545f59ce203ad`。`/tmp/carleman-t235-build.log`：**4274 jobs** 成功，80 bytes，SHA256 `5f073b028023217a24fa6b2bdf0a6daa512844fe55da2434ed5089748b209ff2`。`/tmp/carleman-t235-axioms.log` 为 0 bytes。
- `/tmp/carleman-t235-coefficient-difference-local-axioms.txt`：**3249971 bytes**，SHA256 `9a19797738c876accc5a145a3ddfdd587a02b2d9401270215cb0720dd07b14d5`，与固定证据摘要一致。全部显式输出 **3823 个公理列表及 10 个无公理记录**仅包含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。原全命名空间 `privateToUserName`/`collectAxioms` 白名单递归逻辑未改，末行确认 **9710 声明审计 PASS**，无 sorryAx 或额外数学公理。
- 根导入与 19 项 `#check`/`#print axioms` 齐全。Lean 4.35.0，编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；实际 mathlib checkout 无修改且与固定 lock 一致为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿相对 base 未变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

无修复项。接受本批 **AUXILIARY 变系数切向差商能量与完整测试界**；保留上述全空间系数和几何输入，不升级 P023。正文与 reviewed_at 冻结后仅单文件提交本报告，不改数学、台账、原稿或其它报告，不 push。
