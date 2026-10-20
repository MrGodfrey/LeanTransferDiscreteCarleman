# T236 / C252 独立本机验收

- checked_sha: `eeabe06b6b3e0e9a72852393be4e8f054a77ed1f`
- mathematical_base: `ceba934191acdb2f4dfda0882a67b80094f2e23d`
- reviewed_at: `2026-10-20T07:40:49+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，10/10 显式声明（7 定理、3 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；真实变系数法向通量恢复、同一原弱解的半空间 H² 提升及明确界。覆盖保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/VariableCoefficientNormalRecovery.lean`、全部 raw 类型、公理、analysis/MATH_SPEC/台账与原稿 `paper/main.tex:2659–2665`，并直接核对所用切向能量、弱乘积、乘子代数、Riesz 表示及对称 H² 组装。原 Corollary A.2 是一般凸多面体或盒上的完整 Dirichlet 实现；本批仅接受其边界正则性路线中的变系数半空间步骤，未把这一结果当作一般域正则性。

## 实际数学与假设边界

1. **真实倒数及导数乘子。** `reciprocal` 的值确为 a(x)⁻¹，在正 κ 和 AE 下界 κ≤|a| 下内部给 AE 可测性及 bound=κ⁻¹；不要求 a 为常数或给定任意替代乘子。`reciprocalDerivative` 的值确为 −a⁻²da，bound=κ⁻²da.bound；这个定义本身只定义候选导数，实际链式身份在 `weak_derivative_divide_coefficient` 中证明。`spatialDerivativeOn` 使用真实 `fderiv a x e_j`，域内 C∞ 和开放性给导数连续/可测，原全空间 Lipschitz 常数 C 经 `norm_fderiv_le_of_lipschitz` 和 ‖e_j‖=1 给同一个 C 上界。域外可能不可微时 fderiv 的默认零值不影响域内真实身份，且该全局范数定理仍有效。
2. **AE 椭圆性到处处法向正性。** `matrix_elliptic_diagonal` 在原 AE 椭圆不等式中代入 r 坐标单位向量，真实有限和只剩 a_rr，得 κ≤a_rr AE。Lipschitz 保证这个选定实际代表连续，所以 `{κ≤a_rr}` 闭；Euclidean volume 对每个非空开集为正，闭集 AE 等于全空间遂等于全空间。已读取 mathlib `IsClosed.ae_eq_univ_iff_eq` 的实际前提和证明，它不要求总测度有限。因而最终 κ>0 时 a_rr 在每一点都非零；没有从单纯 AE 身份直接推点值，也没有额外假设法向系数正性。矩阵不要求对称，原二次型椭圆下界足以给此对角结论。
3. **通过真实弱乘积除去系数。** 对已有弱链 D_e(ag)=v，令 b=a⁻¹、db=−a⁻²da。域内处处非零与原 smooth-on-S 使 b 在 S 光滑；实际 Fréchet 倒数链式法则给 db=D_eb AE。原 `IsWeakSpatialDerivative.mul` 用真实紧支测试 bφ 推出
   `D_e(b·ag)=b·v+db·(ag)`。
   `map_inverse` 由同一 AE 乘法身份 b(x)a(x)=1 将左侧原 L² 类精确还原为 g。故输出 w 是真实 D_eg，且
   `‖w‖≤κ⁻¹‖v‖+κ⁻² da.bound·a.bound·‖g‖`。
   已直接检查该弱乘积工具：φ 的支撑紧含 S，使 bφ 即使 b 只在 S 光滑也为全空间紧支光滑测试；所有分布测试身份均保留，没有把经典 g 导数或目标正常导数作为输入。
4. **原弱 PDE 恢复法向通量，符号与指标正确。** `exists_normal_derivative_of_matrix_equation` 在全部有序矩阵指标中删除且仅删除 (r,r)。对其余项，由真实 D_jG_i=D_ij 与系数弱乘积得到
   `V_ij=D_j(a_ijG_i)=a_ijD_ij+(D_ja_ij)G_i`。
   从原全部测试方程 `Σ_ij⟨a_ijG_i,D_jφ⟩=⟨f,φ⟩`，有限和分离 (r,r) 项，严格推出
   `D_r(a_rrG_r)=R`，`R=−f−Σ_(i,j)≠(r,r)V_ij`。
   代码逐项使用 `⟨a_ijG_i,D_jφ⟩=−⟨V_ij,φ⟩`，因此 R 的两个负号、系数导数方向 j 及梯度索引 i 均与原散度型方程一致。R 是实际有限 L² 和；没有把通量导数当作前提。其范数先在删除对角的和上估计，再由非负项扩到全部 i,j，得到保守但合法的完整系数和界。最后应用前项真实倒数链得到 G_r 的法向弱导数。
5. **切向 Riesz、混合交换及同一 H² 状态。** `exists_variable_H2_of_tangential_test_bounds` 的辅助输入确实只控制 j≠r 的二阶分布测试。若 j=r、i≠r，用原 u 的一阶弱链和实际光滑测试导数交换，转到已控制的切向 i；不预设二阶混合导数存在。随后真实有界测试 Riesz 表示为每个非 (r,r) 分量供应一个 L² 弱导数和界 K。代码对未使用的 (r,r) 位置选零，仅作完整有限函数的占位；该位置从不被当作已知导数传入法向恢复。法向导数由原方程另行构造，其界为 N。所有分量的测试界遂被 max(K,N) 控制；原 `exists_weakH2_of_gradient_test_bounds` 经真实弱混合唯一性、Sym₂ 提升和字段装配，给
   `truncate¹ U=u` 以及 `‖field₂U‖²≤card(Sym(Fin d,2))·max(K,N)²`。
   装配字面保留原 0、1 阶字段；使用的是全部原无序二阶多指标纤维，并非少量方向或另一状态。最终结论不需要将某个所选 Riesz 表示预先设为目标 Hessian。
6. **全空间与域内的同一实际方程。** `matrixGradientPairing_test_restricted` 先用已证明的实际零延拓积分公式，再用原乘子 `restrictMeasure`、Lp 乘法 AE 身份及真实 φ 导数，识别
   `B_a(E₀u,φ.fullJet)=Σ_ij⟨(a_ij|S)D_i u,D_jφ⟩`。
   限制乘子保留同一值函数、原 bound 和由 measure monotonicity 传来的资格。每项是有界系数乘 L² 再与 L² 测试导数配对，真实可积；最终原有限积分和不是未定义的形式符号或替代载荷。这里只使用 H¹₀ 的合法一阶零延拓，没有将原梯度自动零延拓成全空间 H¹。
7. **最终定理内部清偿所有辅助数据。** 一般平移不变域包装将 b_ij 定为原 a_ij 的实际限制，将 db_ij 定为实际第 j 坐标导数乘子，其 bound 恰为 C_ij，AE 导数身份为定义等式。法向正性来自前述原椭圆性和连续性。切向测试界来自 T235 原 PDE 的合法二次差商能量及 T233 判据，统一取
   `M=‖field₁u‖`，
   `K=κ⁻¹(‖f‖+(Σ_ij C_ij)M)`，
   `N=κ⁻¹(‖f‖+Σ_ij(a_ij.bound·K+C_ijM))+κ⁻²C_rr a_rr.bound·M`。
   K、N 只含原一阶能量、载荷、系数界及椭圆常数，无目标二阶能量、步长、光滑逼近或人为选择的额外导数界。已直接重读 T235 的相关证明：±h 两次差商都由原 H¹₀ 闭包合法化，平移后系数保持原 AE 椭圆性，完整系数差商误差被 ΣC_ij 控制，消去的只是非零差商能量；不存在 H² 循环。
8. **真实半空间与尚存范围。** 最终 `exists_variable_halfspace_dirichlet_H2` 的 PDE 输入是原 S={x|c<x_r} 上全部紧支光滑测试的真实积分和，系数/梯度/测试 Fréchet 导数的次序与前项一致。S 的开放性和全部切向实平移包含由坐标公式内部给出，辅助 hSS、da、hpos、K 测试界都不再是最终外部输入。仍明确要求原 u∈H¹₀、f∈L²、**全空间**有界且 Lipschitz 的实际系数、**S 内 C∞** 和**全空间 AE** 一致椭圆性；本批没有构造局部图系数的保椭圆全局延拓，不能按纯域内 Lipschitz 数据调用。d=1 时非 (r,r) 集为空，通量导数直接是 −f，恢复及保守界仍成立；r:Fin d 明确要求有法向，不虚构零维方向。半空间无界时也不需有限体积或状态光滑，但结论仅针对给定弱解，不宣称任意 f 均存在 H¹₀ 解。所得 H² 与原 H¹₀ 同状态相交；原弱 PDE 通过精确截断身份保留，最终声明并未额外声称一个新定义的强变系数算子图定理。

非线性边界图的真实弱传输、局部化和系数延拓、一般光滑内域边界正则性、凸域统一 Miranda–Talenti 估计及原穷竭装配仍未完成。本批不提升 P023，不改变原稿或覆盖数。

## 全部声明逐项结论

以下名称统一带 `Carleman.` 前缀；源码行为固定 `VariableCoefficientNormalRecovery.lean`，raw 行为本批固定完整类型的起始行。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 22 / 42313 | `BoundedMultiplier.reciprocal` | PASS；同一实际倒数，AE 可测及 κ⁻¹ 上界。 |
| 33 / 42319 | `BoundedMultiplier.reciprocalDerivative` | PASS；实际 −a⁻²da 与 κ⁻²da.bound 界，未把候选定义当导数证明。 |
| 47 / 42325 | `BoundedMultiplier.spatialDerivativeOn` | PASS；真实 fderiv、域内可测和原 Lipschitz 常数。 |
| 59 / 42332 | `matrix_elliptic_diagonal` | PASS；原 AE 二次型下界与连续性推出每点对角下界。 |
| 74 / 42340 | `weak_derivative_divide_coefficient` | PASS；真实倒数链式和全测试弱乘积恢复原 g 的导数。 |
| 113 / 42355 | `exists_normal_derivative_of_matrix_equation` | PASS；全部非 (r,r) 位置保留，原 PDE 恢复通量并除系数，符号正确。 |
| 180 / 42391 | `exists_variable_H2_of_tangential_test_bounds` | PASS；切向及混合 Riesz、法向恢复、真实同状态对称 H²。 |
| 241 / 42434 | `matrixGradientPairing_test_restricted` | PASS；同一原完整矩阵形式的域内真实乘子配对。 |
| 263 / 42446 | `exists_variable_dirichlet_H2_of_tangential_invariance` | PASS；实际系数导数、正性和原方程切向界全部内部供应。 |
| 299 / 42477 | `exists_variable_halfspace_dirichlet_H2` | PASS；真实半空间及原全部测试 PDE，完整同状态 H² 和明确常数。 |

## 固定源码、依赖与本地证据

导入闭包 **205 个 Carleman 文件**，其中 **204 个旧文件**相对数学基线的 Git blob 全部不变；唯一新增数学文件为本报告模块。已直接重读本批所用 `VariableCoefficientDifference`、`WeakProduct`、`MultiplierAlgebra`、`CellwiseInverseWeight.BoundedMultiplier.restrictMeasure`、`WeakDerivativeBoundedTest`、`WeakH2BoundedTest`、`SecondOrderJetAssembly`，并沿用已审的不变 T234 全一阶差商/闭包基础。T235 正式报告已全文读取：提交 `0c492c06911ba58258a4ec75e82b37fa10470af4`，reviewed_at=`2026-10-20T07:30:32+00:00`，19/19 PASS；报告不替代上述实际代码核对。

固定 mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，实际 checkout 同提交且无修改。Lean 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。直接读取 mathlib 的 Lipschitz 导数范数界和全支撑测度闭集 AE 提升，确认实际前提。根导入及 10 项 `#check`/`#print axioms` 完整。

- `/tmp/carleman-t236-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof；finished_at=`2026-10-20T07:37:42.598441+00:00`。真实 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 执行记录均 exit 0。
- `/tmp/carleman-t236-local-source-manifest.txt`：**1033 项、112109 bytes**，SHA256 `8abdf49a048bb6286f4fced520b7e1a7714fc365ad9ee87de817ea6d7846bdbd`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，完整路径集合、唯一性、每项摘要均与固定 Git blob 对应。
- `/tmp/carleman-t236-target-build.log`：**3385 jobs** 成功，122 bytes，SHA256 `0af904fbd6d1d13872d88ab93bec4d5581bcad430a6748a9679a4e3157d4eade`。`/tmp/carleman-t236-build.log`：**4275 jobs** 成功，80 bytes，SHA256 `80bf22f40642566a20b3f1984fa417403db6f173177dde06f629a4d65802cfc0`。`/tmp/carleman-t236-axioms.log` 为 0 bytes。
- `/tmp/carleman-t236-normal-recovery-local-axioms.txt`：**3263281 bytes**，SHA256 `a52d2f521abe302d6dd536b0eaaa959dcb2a89ac6e7e36f13b4330988cc3866a`，与固定证据摘要一致。10 项完整类型逐项核对；全部 **3842 个显式公理记录**仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。原全命名空间 `privateToUserName`/`collectAxioms` 白名单递归逻辑不变，末行实际确认 **9734 声明审计 PASS**，无 sorryAx 或额外数学公理。
- 原稿与数学基线相同，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，未重跑全库、未查询远端 CI/看板，也未将本地检查称为 CI。

无修复项。接受本批 **AUXILIARY 变系数法向恢复及半空间 H² 正则性**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、根导入、审计、原稿或其他报告，不 push。
