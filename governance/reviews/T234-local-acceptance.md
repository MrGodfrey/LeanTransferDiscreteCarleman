# T234 / C250 独立本机验收

- checked_sha: `528c5bf683ace24836aecdf64ddd73422a000473`
- mathematical_base: `27fcaabab245e49a01868aa211e5db053122cdb0`
- reviewed_at: `2026-10-20T07:19:42+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，20/20 显式声明（17 定理、3 定义），未发现缺陷。**
- axiom_check: **PASS，实际 9659 声明递归审计。**
- accepted_scope: **AUXILIARY；原 H¹₀ 合法差商测试、步长统一梯度界及坐标半空间的同状态 H² 正则性。覆盖保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/DirichletDifferenceQuotient.lean`、20 项 raw 完整类型、公理记录、analysis/MATH_SPEC/台账和原稿 `paper/main.tex:2659–2665`，并直接核对所用弱导数、H¹₀ 闭包、零延拓、差商判据、Riesz/Sym 二阶射流组装及弱 Laplacian 唯一性。本批是原 Corollary A.2 边界正则性路线的半空间步骤，确实由原弱解内部导出差商界和 H² 提升；未把半空间结论当作一般光滑内域或凸多面体的全部正则性。

## 实际对象与数学核对

1. **完整 H¹ 平移与差商。** `translateFirst` 对原全空间 jet 的值及每个梯度分量应用同一真实 L² 平移，T232 的全部弱测试交换关系供应一阶弱链，再由 `firstComponentJet` 组装。连续性证明逐一处理 0 阶和完整 1 阶纤维，使用实际分量组装连续线性映射，故是完整 H¹ 图拓扑的连续性。`differenceFirst z h u=h⁻¹(T_(hz)u−u)` 的值和每个梯度分量都精确对应原 L² 差商。逐坐标真实分部求和给梯度配对，进而给
   `⟨∇u,∇(−δ_(-h)δ_hu)⟩=‖field₁(δ_hu)‖²`。
   平移方向、负步长和外部负号一致。h=0 时差商为零，身份仍成立，未非法约去零步长。
2. **真实测试支撑与原 Dirichlet 闭包。** `SpatialTest.translateInto` 使用线性部分为 Id 的实际仿射拉回；条件 `(x↦x+z)⁻¹'S⊆T` 正是平移后测试支撑落入 T 的方向。其 C∞ 和紧支资格由原测试及仿射同构供应。`translateFirst_test` 先验证真实零延拓的 AE 值身份，再由原弱 jet 值唯一性恢复完整 jet。对任意 u∈H¹₀(S)，`translateFirst_dirichlet_mem` 从原完整 H¹ 闭包取测试逼近序列；测试线性 span 的成员仍是真实测试，连续的一阶零延拓、完整 H¹ 平移和限制使极限落在 T 的原闭子空间。没有用点态边界条件替代任意弱状态的闭包资格。
3. **差商闭包及全空间还原。** 在同域平移包含条件下，平移限制和原 u 均在 H¹₀(S)，线性组合给实际差商限制的 H¹₀ 资格。`zeroExtend_restrict_of_ae_zero` 要求全空间 w 已是 H¹、限制已在 H¹₀，且 w 的值在域外 AE 为零；实际 indicator 公式和弱 jet 值唯一性才推出其限制再零延拓等于整个 w。应用于差商时，域包含的逆否命题保证 x∉S 时 x+hz∉S，两个零延拓值同时消失。这里仅使用 H¹₀ 的合法一阶零延拓，没有假定梯度属于全空间 H¹，更没有假定原状态有 H² 零延拓。
4. **二次差商是原方程的合法测试。** 设 U=E₀u、W=δ_hU、w=W|S。正步平移资格给 w∈H¹₀(S) 以及 E₀w=W。再以负步平移对 w 应用同一结论，得到 Q=δ_(-h)W 的限制 q∈H¹₀(S)。原 `IsWeakNegativeLaplacian u f` 从全部紧支测试延伸到原 H¹₀ 闭包，因而确实可测试 −q。全空间与域内的真实梯度配对身份给
   `E²=−⟨f,value q⟩`，其中 `E=‖field₁ W‖`。
   对 W 已有的一阶弱链应用 T232，得到 `‖value q‖≤‖D_iW‖≤E`；于是 `E²≤‖f‖E`，零能量情形无需除法，正能量情形推出 `E≤‖f‖`。常数为 1，独立 h、u、f 和域；单位坐标方向的尺度已正确处理。整个推导只用原 H¹₀、原弱方程及 ±h 两个平移包含条件，无 H² 或目标差商界前提。
5. **切向二阶测试与混合交换。** 对原零延拓的一阶梯度分量 G，证明仅把 G 当作全空间 L² 类；其限制恰为原梯度分量，真实差商限制范数由前项控制。用 h_n=1/(n+1) 和 T233 的局部差商判据，得到全部原测试 φ 的切向二阶分布配对界 `‖f‖‖φ‖`。判据只在真实紧支测试上取极限，不要求 G 有全空间弱导数。另由原 u 的一阶弱链分别测试 `D_jφ`、`D_iφ`，再用实际光滑测试的二阶导数交换，推出混合配对相等；未先假定 u 的二阶混合导数存在。
6. **法向恢复与完整 H²。** 一般开域定理明确保留所有切向坐标平移不变性。切向作用的二阶测试由前项控制；法向作用于切向梯度的测试经混合交换控制。对唯一剩下的法向—法向项，将原 PDE 的完整坐标和中该项移出，右侧是真实 `⟨f,φ⟩` 减其余切向项。三角不等式、Cauchy–Schwarz 和有限求和给保守界 `(d+1)‖f‖‖φ‖`。实际 `exists_weakH2_of_gradient_test_bounds` 经有界测试的 Riesz 表示、弱混合对称性和 Sym 二阶字段组装，产生 U∈H² 且 `truncate¹ U=u`，并给
   `‖field₂ U‖²≤card(Sym(Fin d,2))((d+1)‖f‖)²`。
   值及全部一阶字段保持原 u；这里的纤维与常数是原无序多指标规范，没有把它改称最佳 Miranda–Talenti 常数。
7. **实际半空间实例及边界情形。** `exists_halfspace_dirichlet_H2` 对任意 r:Fin d、a∈ℝ 和原 S={x|a<x_r} 内部证明开放性及所有切向平移包含，因为 j≠r 时平移不改变第 r 个坐标。输出同一原 u 的 H² 提升，再用该提升的真实 `negativeLaplacian` 弱身份和全部测试 RHS 唯一性识别 `negativeLaplacian U=f`。没有额外域几何或目标正则性输入。d=1 时切向集合为空，法向二阶项直接由原 PDE 恢复，保守常数仍有效；r:Fin d 明确要求存在法向坐标，因此最终定理没有声称 d=0 存在半空间法向。一般辅助平移/差商身份允许零维。半空间可以无界，证明没有有限体积或 Poincaré 前提；结论是每个**给定**原 H¹₀ 弱解的正则性，并不为每个任意 f 宣称存在这样的 H¹ 解。
8. **原文范围。** 本批已消去条件差商界，确实完成平坦坐标半空间的原弱解提升；一般开域版本中的切向平移条件也在最终半空间版本内部清偿。尚未证明曲边非线性坐标传输、一般变系数椭圆差商估计、光滑内域全部边界正则性或凸域统一二阶估计，故不能据此完成原一般凸多面体 P023。没有时间、网格、光滑状态、紧支状态或全梯度之外的额外状态前提。

## 全部声明逐项结论

以下名称统一带 `Carleman.` 前缀；源码行为固定 `DirichletDifferenceQuotient.lean`，raw 行为固定审计文件完整类型起始行。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 17 / 42002 | `WeakSobolevJet.translateFirst` | PASS；实际值及全部梯度平移组装完整弱 H¹。 |
| 23 / 42007 | `WeakSobolevJet.translateFirst_value` | PASS；同一真实 L² 平移的值身份。 |
| 26 / 42012 | `WeakSobolevJet.translateFirst_gradient` | PASS；每个原梯度分量精确交换。 |
| 31 / 42019 | `WeakSobolevJet.translateFirst_tendsto` | PASS；完整 H¹ 图拓扑连续性。 |
| 55 / 42026 | `WeakSobolevJet.differenceFirst` | PASS；真实 H¹ 差商，含零步长。 |
| 58 / 42032 | `WeakSobolevJet.differenceFirst_value` | PASS；原 L² 差商值身份。 |
| 62 / 42037 | `WeakSobolevJet.differenceFirst_gradient` | PASS；全部真实梯度分量的差商身份。 |
| 68 / 42044 | `WeakSobolevJet.differenceFirst_gradient_pairing` | PASS；全梯度分部求和，负步长及负号正确。 |
| 76 / 42049 | `WeakSobolevJet.differenceFirst_energy` | PASS；二次差商的精确完整梯度能量。 |
| 88 / 42055 | `SpatialTest.translateInto` | PASS；真实紧支光滑测试，支撑原像方向正确。 |
| 92 / 42059 | `SpatialTest.translateFirst_test` | PASS；原测试平移与完整 jet 精确一致。 |
| 104 / 42066 | `WeakSobolevJet.translateFirst_dirichlet_mem` | PASS；原完整闭包、实际连续映射及合法测试逼近。 |
| 121 / 42076 | `WeakSobolevJet.differenceFirst_dirichlet_mem` | PASS；原 H¹₀ 空间中的合法差商。 |
| 140 / 42084 | `WeakSobolevJet.zeroExtend_restrict_of_ae_zero` | PASS；具备全部资格后由真实 AE 值身份恢复完整 H¹。 |
| 156 / 42090 | `WeakSobolevJet.differenceFirst_dirichlet_extension` | PASS；域外零值内部证明，合法一阶零延拓精确还原。 |
| 170 / 42100 | `dirichlet_tangential_difference_gradient_bound` | PASS；二次合法测试和原方程内部给步长统一常数 1。 |
| 216 / 42112 | `weakGradient_test_mixed_commute` | PASS；只用原一阶弱链及实际光滑测试混合交换。 |
| 228 / 42119 | `dirichlet_tangential_test_bound` | PASS；真实局部差商极限给所有切向二阶测试界。 |
| 254 / 42131 | `exists_dirichlet_H2_of_tangential_invariance` | PASS；原 PDE 恢复法向，实际 Riesz/Sym 组装同一状态。 |
| 307 / 42143 | `exists_halfspace_dirichlet_H2` | PASS；半空间几何内部供应，真实 H²、原状态恢复及 −ΔU=f。 |

## 固定源码、依赖与本地证据

导入闭包共 **191 个 Carleman 文件**，其中 **190 个旧文件**与数学基线逐 Git blob 相同。本批直接读取 `DifferenceQuotientCriterion`、`FullSpaceTestPairing`、`DirichletExtensionContinuity`、`DirichletZeroExtension`、`DirichletDistribution`、`DirichletSpace`、`FirstComponentJet`、`SobolevRestriction`、`SpatialTestOperations`、`SpatialTestDerivative`、`WeakProductComponents`、`WeakDerivativeBoundedTest`、`WeakH2BoundedTest`、`SecondOrderJetAssembly`、`WeakLaplacian`、`WeakLaplacianLimit`，核对上述实际调用和资格；没有重审无关历史。T232 的全空间差商工具沿用已冻结验收。T233 正式报告已全文读取，提交 `6dda937ae23e61cf0f532545283de66594758343`、reviewed_at=`2026-10-20T07:05:42+00:00`，并再次直接检查其本批使用的差商判据。

固定 mathlib 提交为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，实际 checkout 相同且无修改；Lean 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。根导入及全部 20 项 `#check`/`#print axioms` 齐全。

- `/tmp/carleman-t234-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T07:12:21.548912+00:00`；实际 `lake build Carleman`、`lake env lean tools/CheckAxioms.lean` 执行记录均 exit 0。
- `/tmp/carleman-t234-local-source-manifest.txt`：**1031 项、111871 bytes**，SHA256 `e6d23922ab6df0f1e3c337017ab3811d69e15ebdab039b3b1d4f27bd006a8853`。独立枚举固定提交全部 tracked `.lean` 和三个工具链配置，路径集合、唯一性及每项摘要均与固定 Git blob 匹配。
- `/tmp/carleman-t234-target-build.log`：**3371 jobs** 成功，116 bytes，SHA256 `8c0456eaf2a26edd9bd5675206b34ed974eedcc8b226187b92e298d645aca2ae`。`/tmp/carleman-t234-build.log`：**4273 jobs** 成功，80 bytes，SHA256 `e0fd57a8eb8210519d3935e85308f4a546bb35b85c1a1366038780b1dc8dcde9`。`/tmp/carleman-t234-axioms.log` 为 0 bytes。
- `/tmp/carleman-t234-dirichlet-difference-local-axioms.txt`：**3236539 bytes**，SHA256 `69c84178bd08406404d49fb9b96ab521db21f2f2e181146ef59224c74d1896dc`，与固定证据摘要一致。20 项完整类型逐一核对；全部 **3814 个显式公理记录**只含 `propext`、`Classical.choice`、`Quot.sound` 或无公理。原全命名空间 `privateToUserName`/`collectAxioms` 白名单循环不变，末行实际确认 **9659 声明递归审计 PASS**；没有 sorryAx 或额外数学公理。验收使用该实际计数，未采用曾误传的 9623。
- 原稿与数学基线相同，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次验证固定本地执行证据，未重跑全库、未查询远端 CI/看板，也未把本地成功称为 CI 成功。

无修复项。接受本批 **AUXILIARY 合法 Dirichlet 差商及半空间 H² 正则性**，保持 18/26，不提升 P023。正文及 reviewed_at 签发后冻结，仅单文件提交本报告，不修改数学、台账、根导入、审计、原稿或其他报告，不 push。
