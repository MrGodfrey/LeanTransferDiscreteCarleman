# T046 / C062 独立本机验收

- `checked_sha`: `0c632f37eadbcece6459555fef22a2bb4b3ca688`
- `base_commit`: `6cbca2eb3813801b491d54b7f442834ded59d83c`
- `semantic_checked_at`: `2026-10-18T19:27:49+00:00`
- `reviewed_at`: `2026-10-18T19:31:40+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- 范围：**AUXILIARY**。只接受固定参考单纯形 T 的全部真实可逆仿射像上的局部 C/h 逆估计。任意物理单纯形的统一参考参数化、全网格梯度识别与加权求和仍待；不提升 P011/P012 或其他完整原文覆盖，完成计数保持 12/26。

本报告直接读取固定提交六个新模块、28 项实际完整类型、递归公理产物、相关既有依赖及原 `paper/main.tex`。执行者说明仅用于确定范围，没有替代实际证明检查；后续未提交草稿不参与本次验收。

## 全部 28 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/Spatial/`。表中 PASS 为逐项语义结论。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `affineChange` | `AffineChangeVolume.lean:13` | PASS；实际可逆连续线性映射与平移的复合同胚。 |
| 2 | `affineChange_apply` | `AffineChangeVolume.lean:16` | PASS；点态函数精确为 Ax+b。 |
| 3 | `affineJacobian` | `AffineChangeVolume.lean:18` | PASS；真实线性行列式的绝对值。 |
| 4 | `affineJacobian_pos` | `AffineChangeVolume.lean:20` | PASS；可逆性给 det≠0，因此 J>0。 |
| 5 | `affineChange_map_volume` | `AffineChangeVolume.lean:23` | PASS；真实 Haar 换元与平移不变性给 F_*volume=J⁻¹volume，方向正确。 |
| 6 | `affineChange_map_restrict` | `AffineChangeVolume.lean:33` | PASS；可测嵌入及 F⁻¹(F(S))=S 给准确限制测度版本。 |
| 7 | `integral_comp_affineChange` | `AffineChangeVolume.lean:42` | PASS；∫S f(Fx)=J⁻¹∫F(S)f，真实积分而非指定“缩放范数”。 |
| 8 | `affineChangeEquiv` | `AffineSimplex.lean:12` | PASS；同一个 A,b 的真实仿射等价。 |
| 9 | `affineChangeEquiv_apply` | `AffineSimplex.lean:15` | PASS；仿射等价与测度换元同胚点态一致。 |
| 10 | `affineSimplex` | `AffineSimplex.lean:19` | PASS；实际仿射映射参考顶点并保持单纯形仿射独立。 |
| 11 | `affineSimplex_points` | `AffineSimplex.lean:22` | PASS；逐顶点精确为 F(T_i)。 |
| 12 | `affineSimplex_cell` | `AffineSimplex.lean:26` | PASS；物理凸包恰等于参考凸包的真实像。 |
| 13 | `affineSimplex_nodal_comp` | `AffineSimplex.lean:34` | PASS；同一节点系数下 p_phys∘F=p_ref 在全空间成立。 |
| 14 | `affineSimplex_derivative_comp` | `AffineSimplex.lean:49` | PASS；真实 Fréchet 链式法则给 Dp_phys∘A=Dp_ref。 |
| 15 | `affineSimplex_derivative` | `AffineSimplex.lean:62` | PASS；实际 CLM 身份为 Dp_phys=Dp_ref∘A⁻¹，次序正确。 |
| 16 | `derivativeOneFiber_injective` | `DerivativeFiberNorm.lean:10` | PASS；完整坐标单位基上的值确定真实标量 CLM。 |
| 17 | `derivativeOneFiber_reverse_bound` | `DerivativeFiberNorm.lean:21` | PASS；有限维单射给反范数界，正常数先于全部 CLM。 |
| 18 | `derivativeOneFiber_comp_bound` | `DerivativeFiberNorm.lean:27` | PASS；实际 fiber/算子范数比较与复合界给统一 D，未混同两种范数。 |
| 19 | `lp_two_norm_sq_integral` | `AffineSimplexNorm.lean:11` | PASS；一般 NormedAddCommGroup 值的真实 Lp 范数平方积分身份。 |
| 20 | `simplexNodalLp_norm_sq` | `AffineSimplexNorm.lean:23` | PASS；真实节点多项式在真实单元限制测度上的平方积分。 |
| 21 | `simplexNodalGradientLp_norm_sq` | `AffineSimplexNorm.lean:29` | PASS；全坐标真实常梯度 fiber 的平方积分。 |
| 22 | `affineSimplex_nodal_norm_sq` | `AffineSimplexNorm.lean:37` | PASS；准确缩放为物理范数平方=J×参考范数平方。 |
| 23 | `affineSimplex_gradient_norm_sq` | `AffineSimplexNorm.lean:45` | PASS；物理梯度平方=J×参考单元上 fiber(Dp_ref∘A⁻¹) 的真实平方积分。 |
| 24 | `affineSimplex_gradient_bound_sq` | `AffineSimplexInverse.lean:13` | PASS；积分单调性与正 J 给 D²‖A⁻¹‖² 的平方界。 |
| 25 | `affineSimplex_inverse` | `AffineSimplexInverse.lean:30` | PASS；参考逆界和两种真实缩放消去 J，C(T)>0 先于全部 A,b,c。 |
| 26 | `affineSimplex_inverse_uniform` | `AffineSimplexInverse.lean:55` | PASS；显式几何逆映射预算下得 C(T,κ)/h，预算在中间声明中明确保留。 |
| 27 | `affineSimplex_inverse_map_bound` | `AffineSimplexShapeInverse.lean:12` | PASS；实际内球包含经两点逆像证明 ‖A⁻¹‖≤4R/r，含 d=0。 |
| 28 | `affineSimplex_shape_inverse` | `AffineSimplexShapeInverse.lean:42` | PASS；参考紧性、内球和 h≤κr 内部清偿逆映射预算，C 先于 A,b,a,r,h,c。 |

## 原文映射与范围

原 `paper/main.tex:1523–1551` 的 Section 6.1 Step 2 先比较单元上的权，再用局部逆估计得到 `eq:p1-weighted-inverse`：`‖σ∇z_h‖L2≤C‖ℓ⁻¹σz_h‖L2`。本阶段证明其中固定参考单元经仿射映射、形状控制后获得局部无权 C/h 估计的部分。它尚未证明原加权全网格式，也没有给出原允许权的单元比较或 ℓ_K 与 h_K 的完整组装。

原 Section 6 的 d=2,3 非退化形状正则单纯形属于目标实例；代码对每个 d∈ℕ 和每个固定非退化 d-simplex T 给出声明。最终几何假设为真实物理像包含某个正半径球，且正尺度 h 满足 h≤κr，符合局部直径/内半径比控制的方向。不过当前 h 只是满足这些条件的正实数，未被定义为实际直径；h 可在后续几何实例中取正单元直径，但这个识别尚未在本阶段建立。

最终常数可依赖固定参考 T、其维数 d 和先置形状参数 κ。它不同时统一于所有参考 T；欲对任意物理单纯形使用一个共同常数，仍须构造其作为同一固定 T 的仿射像。当前规范和 AUXILIARY 范围准确保留了这项义务。

## Jacobian、限制测度与积分方向

F 是实际同胚 x↦Ax+b，J=|det A|。已核对所用 mathlib Haar 定理的实际方向：线性推前测度为 |det A|⁻¹volume，平移推前保持 volume。因此 F_*volume=J⁻¹volume，而不是 Jvolume。行列式可负，绝对值处理反向映射；A 的可逆性给 J 严格正，不存在 det=0 的隐藏分支。

限制测度版本来自 MeasurableEmbedding.restrict_map 和实际注入性给出的 `F⁻¹(F(S))=S`。已核对该 mathlib 嵌入定理对任意集合 S 成立，故源码没有遗漏其定理所需的 MeasurableSet 前提；后续应用的真实单纯形单元本身也已证明可测且有限测度。未将像、逆像或限制次序互换。

真实积分公式为 `∫S f(Fx)=J⁻¹∫F(S)f`。由这一方向倒回物理单元积分，确实得到物理范数平方是 J 倍参考积分。一般换元引理采用 Lean 的完整 Bochner 积分约定；实际应用中的节点多项式与常梯度均有已证 Lp/可积性，不是依赖不可积函数的默认积分为零取得空洞结论。ENNReal 与实数转换使用 J⁻¹≥0，所有消去步骤使用 J≠0。

## 真实节点多项式、导数与 Euclidean 梯度

已直接追查 SimplexNodalLp、SimplexReferenceInverse 及节点再现依赖。simplexNodalLp 是在真实凸包限制 Lebesgue 测度上由实际仿射多项式的 MemLp 证明形成的类。其系数单射性不是在任意 Lp 代表上读取顶点：先把 a.e. 相等提升为连续多项式在闭包内相等，再使用真实顶点再现；非退化单纯形的非空内部及闭包性质在此实质使用。

affineSimplex 用相同 F 映射参考顶点，凸包像身份由实际仿射映射保持凸包给出。p_phys∘F 的节点值等于同一系数 c，因此参考仿射再现给全空间多项式相等，而不只是 a.e. 成员等价。该全空间等式配合真实 Fréchet 链式法则推出 `Dp_phys∘A=Dp_ref`，再应用 A⁻¹ 得 `Dp_phys=Dp_ref∘A⁻¹`。这是协向量的准确变换；若写成 Euclidean 梯度向量即通常的逆转置关系，代码的复合次序没有遗漏转置作用。

simplexNodalDerivativeLinear 是真实重心坐标导数的线性组合，已有 HasFDerivAt 定理在每个点识别它。simplexNodalGradientLp 是 `derivativeOneFiber` 作用于该 CLM 的真实常函数 Lp 类。fiber 的一阶指标 `Sym (Fin d) 1` 通过 Sym.oneEquiv 与全部坐标单位基一一对应，故其范数是实际全梯度的 Euclidean 范数，不是任意能量或抽象状态范数。

新证明不把 CLM 的算子范数直接声明等于 fiber 范数，而是先用单位基张成证明 fiber 映射单射，再由有限维单射的反 Lipschitz 界取得 `‖L‖≤K‖fiber L‖`。与 fiber 正向算子界、CLM 复合界组合，取 `D=‖fiber‖K+1>0`，给

`∀L,B, ‖fiber(L∘B)‖≤D‖B‖‖fiber L‖`。

D 只在固定 d 后选择，先于全部 L,B；没有为每个物理映射另选 D。这个充分常数不声称最佳值。

## L2 缩放与参考逆界的组合

第 19 项从已验收的一般范数值 Lp 差平方积分式取 v=0，并正确使用零代表的 a.e. 身份。第 20–21 项再以真实节点/梯度代表替换，得到所需精确积分。不存在将平方范数与范数混淆，或漏掉单元体积。

标量缩放是 `‖p_phys‖²=J‖p_ref‖²`；梯度缩放先保留准确的 `J∫Kref‖fiber(Dp_ref∘A⁻¹)‖²`。给定的 fiber 复合界在非负两侧平方后可逐点比较，积分单调性使用的是有限测度参考单元上的可积常函数。由此得到

`‖∇p_phys‖²≤J(D‖A⁻¹‖)²‖∇p_ref‖²`。

参考逆界是既有实际固定单元结论 `∃Rref>0,∀c,‖∇p_ref‖≤Rref‖p_ref‖`；其证明由真实节点 L2 映射的系数反界和真实梯度线性算子的有限维连续性构成。代入后，标量缩放精确吸收 J，得到 `Cref=D Rref` 的物理逆界。最后两侧非负允许从平方界回到范数界，不需要除以节点函数范数，零节点系数和常函数均包含。

`affineSimplex_inverse` 的 Cref 在 A,b,c 之前选定。中间 `affineSimplex_inverse_uniform` 明确输入 `‖A⁻¹‖≤κ/h`，只做合法代入得到 Crefκ/h，不能单独称为已证明实际形状正则几何；最终第 27–28 项才清偿这一输入。

## 实际内球、尺度方向与 d=0

参考单元所有点满足 ‖x‖≤R 时，对任意 ‖x‖=1 的真实物理方向，内球条件给 a 和 `a+(r/2)x` 都属于物理单元。第二点距离中心恰为 r/2<r，因此开球而非闭球的假设足够。通过已证单元像身份取逆像 u,v∈Kref，得到

`A(v−u)=(r/2)x`，`v−u=(r/2)A⁻¹x`，`‖v−u‖≤2R`。

这里平移 b 精确抵消。r>0 给 `‖A⁻¹x‖≤4R/r`，系数 4 的两个来源分别是 r/2 和参考两点的 2R 界。代码没有假定内球中心的逆像为零，也没有把 R 错读为物理半径。

已阅读 mathlib `ContinuousLinearMap.opNorm_le_of_unit_norm`：它仅对非零向量归一化，没有 Nontrivial 或单位球面非空前提。因此该步骤覆盖 d=0；在零维空间，CLM 算子范数和梯度均为零，空单位球条件不会产生错误的正范数结论。有限维 fiber 单射与参考系数论证同样允许零维，实际类型没有暗含 0<d。最终 h 仍明确要求正，因此零维情形不把 h 宣称为零直径。

最终先从固定参考 T 的紧性选 R>0，再对先置 κ>0 调用中间统一定理，几何预算参数为 4Rκ。对于所有 A,b,a,r,h,c，在 r,h>0 和 h≤κr 下，正分母交叉相乘准确给

`4R/r ≤ 4Rκ/h`。

因此最终类型是 `∀T,∀κ>0,∃C>0,∀A,b,a,r,h,…,∀c,…`。C 的选择先于全部物理映射、平移、内球、尺度和状态；没有依赖 T 时间参数（这里 T 是参考单纯形）、权、网格单元索引或 c。C 可写为上述 Cref 与 4Rκ 的乘积，故其允许依赖正是固定参考形状和 κ。

## 尚未清偿项

本阶段没有构造任意两个非退化 d-simplex 之间的真实仿射等价；没有把每个物理单元归约到同一 T，或从某个已实现网格类自动供应内球和尺度条件。还需将真实全局分片仿射状态限制到单元并识别其弱梯度，完成全网格求和、权的单元比较、ℓ_K≈h_K 及原加权逆界。局部插值误差、H² 点值代表、加权投影稳定性、H² 椭圆正则性和连续热 CE 也不由此次局部逆估计自动完成。不得据此提升 Proposition 6.1/6.2 或任何完整原文覆盖。

## 固定依赖、构建与递归公理

六个新模块的 Carleman 导入闭包共 44 个模块，38 个既有模块相对 base 逐字节未变；全部新模块已在固定 `Carleman.lean` 显式导入。原稿、Lean/mathlib pin、两个 CI 工作流相对 base 未变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

28 项清单与固定 C062/T046、源码、显式审计项一一一致。实际完整类型均已逐项阅读，没有隐藏的目标局部逆估计或未声明的正维假设。固定 `/tmp/carleman-affine-inverse-local-axioms.txt` 为 1,295,089 bytes，SHA256 为 `8b30d1c815ded5fa429180c8250ebe0f2d60abbe9b04c9fb03eeec036e30130e`。28/28 递归依赖仅为正常基础公理 `propext`、`Classical.choice`、`Quot.sound`，实际末行为 `Axiom audit passed for all 4652 Carleman declarations.`。

固定审计脚本枚举全部经 privateToUserName 归属 Carleman 的公开/私有声明，用 collectAxioms 递归收集依赖，白名单只有上述三项基础公理，没有 sorryAx 或新数学公理。实际 `/tmp/carleman-affine-inverse-full.log` 记录 `Build completed successfully (3583 jobs).` 及随后完整递归审计 PASS；固定工具链 Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

已独立通过 GitHub connector 核对 [main CI 39158766072 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39158766072/attempts/1)：main/push，`head_sha=0c632f37eadbcece6459555fef22a2bb4b3ca688`，run 顶层为 completed/success。实际三个 jobs 全部 success：lean（117767403690）、state-check（117767403975）、dashboard / snapshot（117768342691）；Lean 证明目标构建、checked-source 记录和公理上传步骤亦 success。

同次 artifact 元数据确认 `lean-ci-result`（12148152295）和 `lean-declaration-evidence`（12147748867）均绑定上述 run 与固定 head SHA。实际读取 `/tmp/carleman-affine-inverse-main-ci/result.json`：status=PASS，`checked_sha=source_head_sha=0c632f37eadbcece6459555fef22a2bb4b3ca688`，target=Carleman，`finished_at=2026-10-18T19:29:06.480984+00:00`，CI URL 为上述 attempt 1。Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 mathlib pin 与固定源码一致。

正式 `/tmp/carleman-affine-inverse-main-axioms/axioms.txt` 为 1,295,089 bytes，SHA256 为 `8b30d1c815ded5fa429180c8250ebe0f2d60abbe9b04c9fb03eeec036e30130e`，已与固定本机副本逐字节比较，相同。另行核对远端 28/28 项实际完整类型和递归公理列表，只有上述三项正常基础公理；实际末行确认全部 4652 项审计 PASS。未采用后续源码、另一 SHA 或执行者概述替代这些固定版本证据。

## 验收决定

**C062：PASS，可升级为 REVIEWED，scope 保留 AUXILIARY。** 28 项未发现需修复的数学、代表、Jacobian、导数、范数、常数或量词缺陷；同 SHA 实际 CI、完整类型和递归公理证据已齐备。仅接受本报告的固定参考局部逆估计范围，任意单纯形的统一参数化和全网格加权估计仍待；原文完整覆盖保持 12/26。

本次仅写本报告，未修改数学源码、台账、root 导入、原稿或覆盖表，未 commit/push。
