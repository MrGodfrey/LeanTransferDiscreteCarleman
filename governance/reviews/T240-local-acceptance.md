# T240 / C256 独立本机验收

- checked_sha: `9160cd18d129e8d33ef644a71f5794f9df54a1c2`
- mathematical_base: `5f61d27fd056feaadbafcf3363d7c25f88036481`
- reviewed_at: `2026-10-20T08:20:41+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，31/31 显式声明（27 定理、4 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；真实图剪切的完整椭圆双线性型、系数资格和原弱 Poisson 方程传输。覆盖保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/GraphEllipticForm.lean`、31 项 raw 完整类型、公理、analysis/MATH_SPEC/台账，并对照原稿 `paper/main.tex:2659–2665`。Corollary A.2 的一般凸域正则性尚须后续边界图构造、局部化与统一估计；本批只清偿给定真实剪切下的矩阵和弱方程转换，不能据此接受整个 P023。

## 实际数学核对

1. **逆梯度方向正确。** 实际剪切为 F(x)=x+ψ(x)e_r，b 为 ψ 的真实坐标梯度。已有弱链给拉回梯度 g+b g_r；法向平移不变性给 b_r=0。因此本批定义的 `B_b ξ=ξ−ξ_r b` 正是恢复原梯度的逆映射，且证明 `B_{−b}(B_b ξ)=ξ`。没有把逆 Jacobian、转置或作用方向混用。上界 `‖B_b ξ‖≤(1+‖b‖)‖ξ‖` 与逆映射给出的下界均对全部 ξ 成立。
2. **完整双线性型与椭圆性。** `graphMetricEntry` 是实际 Gram 矩阵 `a_ij=⟨B_b e_i,B_b e_j⟩`。代码从真实正交基展开分别证明平方能量和两个任意向量的双线性恒等式，保留全部 i,j 交叉项；对称性来自真实内积。若 b_r=0、‖b‖≤D 且 D≥0，则逆梯度下界给 `(1+D)⁻²∑ξ_i²≤∑a_ij ξ_i ξ_j`，除数严格为正由输入内部推出。未假定矩阵正性或只证明对角项。
3. **斜率与系数来自原 ψ。** `graphSlopeVector` 是全部实际 `fderiv ψ x e_i` 的坐标装配，每坐标身份精确。全局 C∞ ψ 给该向量 C∞；全局 `LipschitzWith C ψ` 给各分量界及合法的较粗界 `‖b(x)‖≤d C`。给定每个真实斜率的全局 Lipschitz 常数 B_i 后，三角不等式给 b 的常数 `∑B_i`。此处 B_i 是明确剩余资格，未从 C∞ 加高度 Lipschitz 无根据地推出全局二阶界。
4. **全局系数界与 Lipschitz 界。** 基向量的 B_b 像范数≤1+‖b‖，两个斜率对应基像之差≤‖b−c‖。将两个内积之差展开为 `⟨X−V,Y⟩+⟨V,Y−W⟩`，得系数差≤`2(1+D)‖b−c‖`，同时得到单项绝对值≤`(1+‖b‖)²`。于是实际 `graphEllipticCoefficient` 是全空间 bounded multiplier，界为 `(1+d C)²`，其实际 value 全局光滑；在上述 B_i 资格下全局 Lipschitz 常数为 `2(1+d C)∑B_i`。法向平移不变性内部给 b_r=0，最终椭圆性对每个 x、每个 ξ 成立，常数 `(1+d C)⁻²>0`。这些结论未输入任意替代系数矩阵。
5. **真实 L² 双线性积分身份。** 在任意限制体积 `volume.restrict S` 上，对全部坐标 L² 类 G、H，完整矩阵配对严格等于
   `∑i ⟨G_i−w_i G_r,H_i−w_i H_r⟩`，
   其中 w_i 为同一实际斜率乘子的限制。有限求和与积分交换逐项由 bounded multiplier 和 L²×L² 的真实可积性保障。代码只合并有限坐标、有限乘子和 Lp 加减代表的 AE 身份，没有不可数例外集合并；实际点态双线性恒等式在同一 AE 集合上使用。该结论不只覆盖 G=H。
6. **完整弱 H¹ 能量精确恢复。** 对原开放 T、S=F⁻¹T，P 是已证明 Jacobian=1 的真实限制体积 L² 复合等距。`graphShearPullback_inverse_gradient` 先由真实 D_rψ=0 证明 w_r 的对应作用为零，再用已建立的全部弱梯度链得到 `D_iU−w_iD_rU=P(D_i u)`。因此对任意两个原 H¹ 状态 u、v，实际矩阵能量严格等于原 `weakGradientPairing u v`；没有 H²、H¹₀、经典导数或平滑状态假设。P 的内积等距用于全部真实弱分量，不是只用值范数近似。
7. **从原方程到所有原测试的矩阵方程。** 输入 `hf:IsWeakNegativeLaplacian u f` 是原 T 上任意 H¹ 状态与同一 L² f 的完整分布身份。对任意源域测试 φ，内部构造 χ=φ∘F⁻¹；由 `F(F⁻¹x)=x` 给真实支撑资格，逆剪切的光滑性与 homeomorphism 给紧支光滑测试。Pχ=φ 由真实复合代表和换元得到；原弱 jet 的值唯一性在开放 S 上进一步识别两个完整测试 jet。对 u、χ 使用前项能量恒等式，再使用原 hf χ 和 P 的内积等距，得同一 U 与同一 Pf 的全部测试矩阵方程。未将变换后 PDE 当作假设，也未输入 H² 或原状态边界条件。
8. **完整积分形式、负号与参数。** 最后 wrapper 将真实矩阵配对展开成 `∑i∑j∫_S a_ij D_iU D_jφ=⟨Pf,φ⟩`，测试分量用实际 `fderiv φ` 识别；因此对应原 −Δu=f 的正梯度配对，符号正确，全部混合项保留。各项均为真实可积乘积。T 只是任意开放空间域，不是时间参数，不要求有界或有限体积；空域允许。法向 r:Fin d 明确要求有实际坐标，未虚构 d=0 法向；d=1 时法向不变性使斜率为零，公式兼容平移。常数由 d、C、B_i 先于全部状态和测试给出；能量与 PDE 本身不需要额外 B_i 资格。

本批显式保留给定全局 C∞、Lipschitz 且沿法向平移不变的 ψ；只有系数 Lipschitz 声明需要各实际斜率的全局 B_i。尚未从原边界图制造这些全局输入，也未在本批组装边界 H² 正则性、一般凸域统一 Miranda–Talenti 估计或完整 Corollary A.2。导入旧 H² 传输模块不等于本批弱方程证明使用了 H² 前提。

## 全部声明逐项结论

名称统一带前缀 `Carleman.`；源码行指固定 `GraphEllipticForm.lean`，raw 行指本批固定审计文件的完整类型。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 12 / 42828 | `graphCovectorMap` | PASS；真实逆梯度 CLM 定义。 |
| 15 / 42831 | `graphCovectorMap_apply` | PASS；精确 ξ−ξ_r b。 |
| 18 / 42834 | `graphCovectorMap_inverse` | PASS；b_r=0 时真实互逆。 |
| 23 / 42838 | `graphCovectorMap_norm_bound` | PASS；全部向量的 1+‖b‖ 上界。 |
| 33 / 42841 | `graphCovectorMap_lower_bound` | PASS；由实际逆映射推出下界。 |
| 38 / 42844 | `graphMetricEntry` | PASS；真实 Gram 系数定义。 |
| 42 / 42846 | `graphMetricEntry_energy` | PASS；完整双和等于逆梯度范数平方。 |
| 58 / 42849 | `graphMetricEntry_symmetric` | PASS；真实系数对称。 |
| 61 / 42852 | `graphMetricEntry_bilinear` | PASS；两个任意向量的完整双线性身份。 |
| 78 / 42856 | `graphMetricEntry_elliptic` | PASS；严格正分母和全部方向椭圆下界。 |
| 89 / 42864 | `graphSlopeVector` | PASS；实际 fderiv 坐标装配。 |
| 92 / 42867 | `graphSlopeVector_apply` | PASS；各真实斜率坐标精确恢复。 |
| 96 / 42870 | `graphSlopeVector_contDiff` | PASS；原 C∞ 资格传到真实斜率。 |
| 102 / 42873 | `graphSlopeVector_norm` | PASS；高度 Lipschitz 内部给 d C 界。 |
| 115 / 42876 | `graphSlopeVector_lipschitz` | PASS；真实各分量 B_i 给全向量 Lipschitz。 |
| 135 / 42880 | `graphCovectorMap_basis_norm` | PASS；实际单位基像的范数界。 |
| 140 / 42883 | `graphCovectorMap_basis_sub` | PASS；斜率差控制对应基像之差。 |
| 151 / 42888 | `graphMetricEntry_norm` | PASS；全部系数的绝对值界。 |
| 159 / 42891 | `graphMetricEntry_sub_bound` | PASS；完整内积差与 2(1+D) 常数。 |
| 186 / 42896 | `graphMetricEntry_contDiff` | PASS；实际 Gram 乘积光滑。 |
| 193 / 42900 | `graphMetricEntry_lipschitz` | PASS；有界斜率和向量 Lipschitz 给系数界。 |
| 204 / 42905 | `graphEllipticCoefficient` | PASS；实际全空间 bounded multiplier 定义。 |
| 214 / 42911 | `graphEllipticCoefficient_contDiff` | PASS；同一实际系数的 C∞ 资格。 |
| 219 / 42915 | `graphEllipticCoefficient_lipschitz` | PASS；显式保留 B_i 的统一全局界。 |
| 228 / 42920 | `graphEllipticCoefficient_elliptic` | PASS；从真实法向不变性推出处处全方向椭圆。 |
| 240 / 42927 | `graphMetricEntry_bilinear_coordinates` | PASS；完整坐标双和等于逆梯度坐标乘积和。 |
| 249 / 42931 | `graphEllipticCoefficient_pairing` | PASS；全部真实 L² 向量的积分双线性身份。 |
| 304 / 42938 | `WeakSobolevJet.graphShearPullback_inverse_gradient` | PASS；同一弱拉回状态的逐坐标逆梯度。 |
| 335 / 42951 | `graphShearPullback_energy` | PASS；任意两个原 H¹ 状态的完整能量身份。 |
| 354 / 42961 | `graphShearPullback_equation` | PASS；原弱 Poisson 身份内部给全部源域测试方程。 |
| 397 / 42974 | `graphShearPullback_equation_integral` | PASS；同一状态、系数、载荷与真实测试导数的全积分形式。 |

## 固定依赖与本地证据

导入闭包 **209 个 Carleman 文件**，其中 **208 个旧文件**相对数学基线逐 Git blob 不变，唯一新模块为本批 `GraphEllipticForm`。本次直接核对原 `IsWeakNegativeLaplacian`、`weakGradientPairing_coordinates`、矩阵 L² 配对及有界乘子、真实剪切限制测度/逆测试和 T238 的弱拉回梯度/值唯一性调用。T239 冻结报告已全文读取：提交 `1ff2f759dc1ef22d08032d49f9312c17f22222a7`，checked_sha 为本报告 base，reviewed_at=`2026-10-20T08:07:12+00:00`，6/6 PASS。该报告不代替本批实际数学检查，也不把其 H² 结论混入本批 H¹ 假设。

Lean 为 **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入、31 项 `#check`/`#print axioms` 均齐全。

- `/tmp/carleman-t240-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T08:14:27.927798+00:00`；`lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 实际执行记录均 exit 0。
- `/tmp/carleman-t240-local-source-manifest.txt`：**1037 项、112546 bytes**，SHA256 `e0dd12698569ce5a9b6bfb4bd8ac474234147e296423ec72e1fc08bc26e43a0c`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性和逐项摘要均与固定 Git blob 匹配。
- `/tmp/carleman-t240-target-build.log`：**3389 jobs** 成功，106 bytes，SHA256 `3b9380e94e18ef403de05f020515d3c44c4cd6a88c819369aa05f71b11f79d45`。`/tmp/carleman-t240-build.log`：**4279 jobs** 成功，80 bytes，SHA256 `8356e376dad3207b69d2025addf96cf3acf655d7c6495b3b038b826e47092c14`。`/tmp/carleman-t240-axioms.log` 为 0 bytes。
- `/tmp/carleman-t240-graph-elliptic-form-local-axioms.txt`：**3306216 bytes**，SHA256 `a8476608383ecf5c109ef6f42f7eed49101d33fc7d413d2e74865d88e6fdb71e`。31 项完整类型逐项核对；全部 **3914 个显式公理记录**仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，实际尾部确认 **9878 声明递归审计 PASS**，无 sorryAx 或额外数学公理。
- 原稿相对基线不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次检查固定本地证据，未重跑全库，未查询远端 CI/看板，也未把本地检查称作 CI。

无修复项。接受本批实际 **AUXILIARY 图系数与弱椭圆方程传输**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告；不修改数学、总台账、根导入、公理工具、原稿或其他报告，不 push。
