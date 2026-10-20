# T237 / C253 独立本机验收

- checked_sha: `77a0dc79f9a1d256ecae73c15a7e8eebe10ce6c1`
- mathematical_base: `eeabe06b6b3e0e9a72852393be4e8f054a77ed1f`
- reviewed_at: `2026-10-20T07:50:54+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，24/24 显式声明（20 定理、4 定义），未发现阻断缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；实际非线性图剪切、Jacobian、保体积换元、光滑测试和 L² 复合身份。覆盖保持 18/26，P023 不提升。**

已全文读取固定 `Carleman/Spatial/NonlinearGraphShear.lean`、全部 raw 完整类型/公理、分析、MATH_SPEC、声明清单及原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 要求一般凸多面体或盒上的完整 Dirichlet 实现；本批仅接受其边界正则性证明路线的坐标基础。核查固定本地执行记录，没有重跑旧闭包、查询远端 CI/看板或混入后续弱坐标传输代码。

## 实际数学与前提边界

1. **同一真实剪切及逆。** `spatialGraphShear` 字面定义 F(x)=x+ψ(x)e_r、F⁻¹(x)=x−ψ(x)e_r；输入 htrans 对全部 x,t 给 ψ(x+te_r)=ψ(x)。在左逆使用 t=ψ(x)，右逆使用 t=−ψ(x)，故两边都还原原 x，且连续性由原 ψ 的连续性得到。没有假设待证逆身份或把一个局部图误作全空间双射。ψ(Fx)=ψ(x) 与 F(x)_r=x_r+ψ(x) 精确推出 F⁻¹{ψ(y)<y_r}={0<x_r}。结合真实双射，这确实覆盖整个图域；不是仅几乎处处的域对应。
2. **真实导数、法向零和单位行列式。** 由原全空间 C∞ 的实际 Fréchet 链式法则，DF(x)=Id+(Dψ(x)).smulRight(e_r)。沿 t↦x+te_r 在 t=0 求真实一维导数，并将 htrans 化为常函数身份，得 Dψ(x)e_r=0。随后在 EuclideanSpace 的实际正交基下逐项识别 DF 的矩阵为 I+evᵀ，其中 v_j=Dψ(x)e_j、e_i=1_{i=r}；真实 `LinearMap.det_toMatrix` 和矩阵行列式引理给 det DF=1+vᵀe=1。行列式的行列方向、法向指标和系数正确；没有用定义指定一个“Jacobian”。raw 的 `ContDiff ℝ ↑⊤` 对应源码 ∞，这里是 C∞，并未声称解析。
3. **实际换元和任意目标集限制。** 对 s=univ，F 的逐点真实导数、单射性和可测性满足 mathlib 的 `map_withDensity_abs_det_fderiv_eq_addHaar`。已直接读取该定理，所得确为 `map F ((volume|s).withDensity |det DF|)=volume|(F''s)`；本批用刚证明的 det=1、F 满射及 restrict_univ 消去密度和像域，得到实际 volume 的保测度性。不是假设体积保持，也不要求有限总体积。任意目标 T 的限制用 F 的可测嵌入 `restrict_map`，该 API 的实际类型对任意集合成立，不额外要求 T 可测。最后代入已证精确半空间原像，供给半空间到图域的真实限制体积保持。
4. **正逆光滑与斜率不变。** 正逆映射分别由 x±ψ(x)e_r 的真实 C∞ 运算得到。固定 t 对函数身份 ψ∘(x↦x+te_r)=ψ 求 Fréchet 导数，平移导数为 Id，故 Dψ(x+te_r)=Dψ(x)。这里先固定 t 再求导，没有对随 x 变化的位移漏掉导数。斜率乘子值是实际 Dψ(x)e_j；全空间 LipschitzWith C ψ 经真实导数算子范数界和 ‖e_j‖=1 给同一个 bound=C，C≥0 来自 NNReal，AE 可测性来自导数连续性。C∞ 斜率及其法向平移不变再给真实 D_r(D_jψ)=0。没有预设斜率的法向导数，也没有把高度 Lipschitz 当作斜率自身 Lipschitz 或全局 Hessian 有界。
5. **完整原光滑测试及正确链式符号。** 原 `SpatialTest T` 的值为全空间 C∞、紧支且 tsupport⊆T。通用拉回使用实际 φ∘F；紧支性来自 homeomorphism 的闭嵌入/紧集逆像，真实 tsupport 的原像身份及 hST: F⁻¹T⊆S 给全部支撑资格。没有用仅连续映射的逆像保紧性。全方向 e 的实际链式法则给 D(φ∘F)(x)e=Dφ(Fx)(DF(x)e)；剪切版本展开为 D_eφ(Fx)+(D_eψ(x))D_rφ(Fx)。逆版本直接对 x−ψ(x)e_r 求导并展开，得到对应减号，φ 的取值点为 F⁻¹x，ψ 的导数点仍为 x；这与实际逆函数表达式一致。没有把测试链式法则扩称为任意弱状态的链式法则。
6. **真实 L² 等价类与逆。** 通用 `homeomorphPullbackLp` 明确保留 hm: MeasurePreserving F μ ν，定义为 mathlib 的 `Lp.compMeasurePreservingₗᵢ`，因此是 Lp ℝ 2 ν 到 Lp ℝ 2 μ 的真正实线性等距映射，范数常数严格为 1。已直接读取实际 AEEqFun 复合、Lp 成员和范数实现；没有任意选择代表后的逐点定义问题。代表公式仅为 μ-a.e. u∘F。逆式由 hm 的真实可测等价逆保测度性供给资格，将前向 AE 等式沿 F⁻¹ 拉回后与逆向 AE 等式合并，再用 Lp.ext 和 F(F⁻¹y)=y。零测例外的传输有真实 quasiMeasurePreserving 依据；没有将任意代表的双重复合当作处处身份。把同一逆式应用于 F⁻¹ 也给另一侧逆，所选证明不限制状态子空间。具体剪切的 hm 由前述 Jacobian 结论内部供给。
7. **标量积分和测试 L² 身份。** 积分身份先用前向 AE 代表替换，再对实际可测等价 F 应用 `MeasurePreserving.integral_comp'` 于 g(y)=a(F⁻¹y)u(y)，利用 F⁻¹(Fx)=x 得到准确换元，无缺失密度或逆向错误。该通用声明允许任意 a，是 mathlib 全定义 Bochner 积分的等式；它不额外声称任意 a·u 可积，后续若需 L¹ 性须另供资格。这不构成本批缺陷。最后测试到 L² 的身份保留两测度 `IsFiniteMeasureOnCompacts`，原紧支光滑测试内部给真实 MemLp；两侧 toLp AE 身份和沿 F 拉回的原测试 AE 身份在同一 μ 下合并，得到严格 Lp 等式，无总体积有限假设。

量词和范围均明确：ψ 是给定的全空间光滑高度，法向平移不变是显式输入；只有斜率乘子部分另要求给定全空间 Lipschitz 常数。几何/体积结论本身不需要该 Lipschitz 界。一般 Lp helper 对全部原 L² 状态与实际测度成立，不要求有限维状态空间、光滑代表或有限测度；具体剪切需要 r:Fin d，故没有虚构 d=0 的法向，而一般 homeomorphism helper 仍可用于零维/零测度情形。所有现有界是原 C 和精确等距常数 1，不存在状态后选常数。

尚未从原解析边界图构造并延拓这样的 ψ，也未证明一般弱射流链式法则、原 PDE 的椭圆矩阵变换、H¹₀/H² 传输或一般凸域统一正则性。本报告不据此提升 P023。

## 全部声明逐项结论

下表使用完整声明名；源码行为固定 `NonlinearGraphShear.lean`，raw 行为本批固定审计文件中的完整类型起始行。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 18 / 42510 | `Carleman.spatialGraphShear` | PASS；同一真实正逆映射及连续性。 |
| 34 / 42517 | `Carleman.spatialGraphShear_psi` | PASS；沿实际剪切的高度不变。 |
| 38 / 42521 | `Carleman.spatialGraphShear_halfspace` | PASS；精确全半空间/图域原像。 |
| 48 / 42526 | `Carleman.spatialGraphShear_hasFDerivAt` | PASS；实际 Id+e_r⊗Dψ 导数。 |
| 56 / 42535 | `Carleman.spatialGraphShear_normal_derivative` | PASS；真实一维链式给 D_rψ=0。 |
| 71 / 42540 | `Carleman.spatialGraphShear_det` | PASS；完整基矩阵计算给 det=1。 |
| 94 / 42544 | `Carleman.spatialGraphShear_measurePreserving` | PASS；真实 Jacobian 换元及满射消去密度。 |
| 112 / 42549 | `Carleman.spatialGraphShear_measurePreserving_restrict` | PASS；任意目标集合的实际限制测度。 |
| 125 / 42556 | `Carleman.spatialGraphShear_halfspace_measurePreserving` | PASS；半空间到同一图域的保体积。 |
| 133 / 42562 | `Carleman.spatialGraphShear_contDiff` | PASS；实际正映射 C∞。 |
| 139 / 42567 | `Carleman.spatialGraphShear_symm_contDiff` | PASS；实际逆映射 C∞。 |
| 145 / 42572 | `Carleman.spatialGraphShear_fderiv_invariant` | PASS；固定实平移下全导数不变。 |
| 160 / 42578 | `Carleman.SpatialTest.pullbackSmoothHomeomorph` | PASS；完整光滑、紧支和域内支撑资格。 |
| 169 / 42584 | `Carleman.SpatialTest.pullbackSmoothHomeomorph_derivative` | PASS；全方向真实 Fréchet 链式。 |
| 177 / 42589 | `Carleman.SpatialTest.pullbackGraphShear_derivative` | PASS；正向完整加号链式展开。 |
| 192 / 42598 | `Carleman.SpatialTest.pullbackGraphShear_symm_derivative` | PASS；逆向减号及实际取值点。 |
| 209 / 42607 | `Carleman.graphSlopeMultiplier` | PASS；真实斜率、可测性及同一 C 上界。 |
| 221 / 42611 | `Carleman.graphSlopeMultiplier_contDiff` | PASS；真实斜率 C∞。 |
| 226 / 42614 | `Carleman.graphSlopeMultiplier_normal_derivative` | PASS；同一斜率法向导数为零。 |
| 236 / 42620 | `Carleman.homeomorphPullbackLp` | PASS；实际 AE 类线性等距复合。 |
| 240 / 42625 | `Carleman.homeomorphPullbackLp_ae` | PASS；正确源测度下的代表身份。 |
| 244 / 42629 | `Carleman.homeomorphPullbackLp_inverse` | PASS；真实逆复合及零测集合法传输。 |
| 252 / 42633 | `Carleman.integral_mul_homeomorphPullbackLp` | PASS；标量积分的准确逆向换元。 |
| 260 / 42639 | `Carleman.SpatialTest.pullbackSmoothHomeomorph_toLp` | PASS；同一原测试的严格 Lp 兼容身份。 |

## 依赖和固定本地证据

T236 冻结报告已全文读取：提交 `d366be4006b35fbcb93b93c01326fef1945c5b14`，checked_sha 为本批 base，reviewed_at=`2026-10-20T07:40:49+00:00`，10/10 PASS。本批虽导入该模块，并未把其半空间 H² 结论当作已有非线性拉回。直接核对了 `SpatialCoordinates`、`SpatialTest`/toLp、`BoundedMultiplier` 的真实定义，以及 mathlib 的实际 Jacobian 换元、矩阵行列式、可测嵌入限制、保测度逆、Lp 等距复合、标量积分换元、紧支复合及 Lipschitz 导数范数界。导入闭包 **206 个 Carleman 文件**，其中 **205 个旧文件**相对 base 的 Git blob 全部不变。

- `/tmp/carleman-t237-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T07:46:45.262935+00:00`；实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0。本验收核对这些执行记录，没有声称重新运行全库。
- `/tmp/carleman-t237-local-source-manifest.txt`：**1034 项、112216 bytes**，SHA256 `9bd493507fe89659d4253a286b7727cebb6fc8ad233a653fd186db21c5bbcd51`。独立枚举 fixed proof 的全部 tracked `.lean` 及三项工具链配置，确认路径集合完整、无重复，逐项摘要与固定 Git blob 全部一致。
- `/tmp/carleman-t237-target-build.log`：**3386 jobs** 成功，108 bytes，SHA256 `57cb8c94c81def4aae36de5011bb93af255916524559364ba35cba1095942d19`。`/tmp/carleman-t237-build.log`：**4276 jobs** 成功，80 bytes，SHA256 `45d824e8e25471258d0248afd09c38034b2ef92f0c253c551cdb52ab1596b139`。`/tmp/carleman-t237-axioms.log` 为 0 bytes。
- `/tmp/carleman-t237-graph-shear-local-axioms.txt`：**3276212 bytes**，SHA256 `bc09916c45dae93bbd6d079f3d280098d6cce54ad42e0e33943954e83b695c8e`，与固定摘要一致。24 项完整类型逐一核对；全部 **3856 个显式公理列表及 10 个无公理记录**仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。递归白名单代码与 base 相同，真实末行确认 **9775 声明审计 PASS**，无 sorryAx 或额外数学公理。
- 根导入及全部 24 项 `#check`/`#print axioms` 完整。Lean 4.35.0、编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；实际 mathlib checkout 无修改，与固定 lock 一致为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

无修复项。接受本批 **AUXILIARY 非线性图剪切及实际换元基础**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、审计或其他报告，不 push。
