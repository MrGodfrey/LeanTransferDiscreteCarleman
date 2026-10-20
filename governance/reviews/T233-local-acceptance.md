# T233 / C249 独立本机验收

- checked_sha: `27fcaabab245e49a01868aa211e5db053122cdb0`
- mathematical_base: `fb7cdb9855e940d9d275e726ce09f3beef9b20b0`
- reviewed_at: `2026-10-20T07:05:42+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，8/8 定理，未发现阻断缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；真实差商强极限与局部 L² 弱导数/H² 判据。覆盖保持 18/26，P023 不提升。**

已全文读取固定 `Carleman/Spatial/DifferenceQuotientCriterion.lean`、八项 raw 完整类型与公理记录、analysis/MATH_SPEC/声明清单及原稿 Corollary A.2（`paper/main.tex:2659–2665`）。原文要求凸多面体或盒上 Dirichlet Laplacian 的完整空间分析性质；这里仅证明差商有界推出真实弱导数的充分判据，并未从原 PDE 推出该界。依照本地协议审查固定 Git 源码与实际构建/审计记录，不重复构建旧闭包，不查询远端 CI 或看板。

## 实际数学及量词核对

1. **代表身份与变号步长。** `spatialDifferenceQuotient_ae` 展开同一真实 L² 差商 `δ_(h,z)=h⁻¹(T_(hz)−I)`，先用 x↦x+hz 的保测度性质把 `u=f` 的 AE 身份平移，再结合 Lp 的缩放/减法代表定理，得到 `δ_(h,z)u(x)=h⁻¹(f(x+hz)−f(x))` AE。没有在任意代表上直接逐点定义 Lp 算子。强极限定理要求全部 hₙ≠0 且 hₙ→0，因而可构造趋向 0 的穿孔邻域滤子；没有正步长或单调性假设。对每个固定 x，实际 `t↦f(x+tz)` 的一维导数是 `Df(x)z`，真实 slope 定理给沿该任意变号序列的点态极限。h=0 的零差商约定没有混入该极限。
2. **可数 AE 合并与真实强 L² 收敛。** `ae_all_iff` 仅对 n∈ℕ 合并每项代表身份，再与 v 的代表身份相交；没有对全部 h 或全部空间点作非法不可数零测集交换。f 的 C¹ 资格及 u、v 的实际 L² 代表身份通过全空间紧支测试积分分部，内部给 `D_zu=v` 的完整弱链。T232 的真实差商界于是给每个 n 的精确 `‖δ_(hₙ,z)u‖≤‖v‖`。所调用 Fatou/平行四边形引理已直接核对：若误差平方积分沿子列≥b>0，则和的平方积分≤`4‖v‖²−b`，而 AE 极限与 Fatou 给至少 `4‖v‖²`，矛盾。因此精确能量上界和 AE 收敛足以得到强 L²；不需要共同控制函数，也不假设有限全空间测度。最后通过实际 Lp 差的 AE 身份，将误差平方积分严格识别为 `‖δu−v‖²`，取平方根得到所声明的范数拓扑极限。这里只需 f 和一个方向导数为 L²，不暗加整个梯度的 L² 前提。
3. **全体真实紧支测试及局部配对。** `SpatialTest` 仍是原完整紧支 C∞ 测试，其支撑位于 S；真实值和 Fréchet 导数的 L² 资格由紧支及光滑性给出，所以测试差商直接满足上述强收敛。`full_toLp_inner` 用同一个测试 fullJet 的零阶值 AE 身份和实际零延拓/限制的伴随配对，得到全空间与 S 内内积相同。对 `φ.derivativeTest z` 应用同一身份得到导数配对；其导数支撑仍位于原支撑。这些零延拓资格仅用于测试，不用于任意待求导状态，也没有要求测试差商平移后仍支撑在 S。
4. **最终局部差商界给全部测试上的分布有界性。** 对固定任意全空间 u∈L²、开域 S 和方向 z，假设仅为 `‖(δ_(hₙ,z)u)|S‖≤C` 最终成立。真实全空间分部求和是 `⟨δ_(h,z)u,φ⟩=−⟨u,δ_(-h,z)φ⟩`，反步长和负号均正确。右端测试差商强收敛，连续内积给极限 `⟨u,D_zφ⟩`；紧支配对身份把另一侧精确转成 S 内内积。Cauchy–Schwarz 因而给同一 `C‖φ‖_(L²(S))`，`le_of_tendsto` 只使用最终界。没有假设差商 u 本身收敛或另选弱收敛子列，也未把只对某个有限测试族的界当作所有测试的界。
5. **真实 Riesz 弱导数，常数不损失。** 坐标方向判据明确保留 C≥0。已直接读取 `WeakDerivativeBoundedTest` 和 `BoundedTestRepresentation`：在原测试 jet 的代数 span 上定义 `L(φ)=−⟨u,D_iφ⟩`，真实值映射的单射性使其下降到 L² 测试像；有限线性组合仍由同类测试表示。上述界使该泛函连续，Hahn–Banach 给同范数延拓，实际 Hilbert Riesz 等距给 v∈L²(S)、`‖v‖≤C`。随后对每个原 `SpatialTest S` 恢复 `⟨u,D_iφ⟩=−⟨v,φ⟩`。没有将 v 的存在、测试空间完备性、状态光滑性或目标弱身份作为输入；输出范数保持同一个 C。
6. **仅 L² 梯度延拓给同一原 H² jet。** 最终定理的 u 是原 `WeakSobolevJet d 1 (volume.restrict S) S`；每个给定全空间 Gᵢ 只要求其真实限制等于 u 的原第 i 梯度分量。假设是每个坐标对 i,j 的 `δ_(hₙ,eⱼ)Gᵢ` 在 S 内最终有统一界 C，各对的最终阈值可以不同。上项只应用于这些 L² 类；没有要求 Gᵢ 在全空间具有任何弱导数，更没有假设它是全空间 H²。调用 `exists_weakH2_of_gradient_test_bounds` 后，实际 Riesz 导数 Dᵢⱼ 满足全测试身份；由原 u 的一阶弱链和真实混合弱导数交换得到 Dᵢⱼ=Dⱼᵢ，再按 Sym 无序多重指标装配。`secondOrderFields` 原样保留原零阶及全部一阶字段，故结论是完整 `truncate¹ U=u`，不是仅值相同的替代状态。实际 field₂ 范数平方是每个 Sym 分量的 L² 范数平方之和，界为 `card(Sym(Fin d,2))·C²`，没有把它错写成全有序 d² 次重复计数。
7. **边界与范围。** S 只要求开放，允许无界、非光滑、不连通或空域；有限测度不是隐藏前提。C=0、z=0 和 d=0 在适用的声明中均合法，未进行除以 C、方向范数或维数的操作。最终定理明确要求实际梯度延拓及其差商界，不声称每个任意 L² 延拓都自动满足该界；特别不能把零延拓在边界产生的跳跃忽略。尚须由椭圆方程证明合法的局部/边界差商估计、坐标弱传输及法向导数恢复，才能应用本判据完成原正则性。

## 全部声明逐项结论

源码行均位于固定 `Carleman/Spatial/DifferenceQuotientCriterion.lean`，raw 行位于本批固定审计文件。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 14 / 41911 | `Carleman.spatialDifferenceQuotient_ae` | PASS；真实平移差商的 AE 代表公式。 |
| 25 / 41916 | `Carleman.spatialDifferenceQuotient_tendsto_of_contDiff` | PASS；C¹ 且原函数/方向导数 L² 时，任意非零变号步长序列的真实强 L² 极限。 |
| 63 / 41926 | `Carleman.SpatialTest.differenceQuotient_tendsto` | PASS；全部原紧支测试及其真实方向导数。 |
| 72 / 41933 | `Carleman.SpatialTest.full_toLp_inner` | PASS；真实测试全域/限制配对精确身份。 |
| 81 / 41939 | `Carleman.SpatialTest.full_derivativeLp_inner` | PASS；同一真实导数测试的全域/限制配对。 |
| 88 / 41946 | `Carleman.differenceQuotient_test_bound` | PASS；仅最终局部差商界推出全部弱测试有界性，符号及 C 正确。 |
| 109 / 41959 | `Carleman.exists_weakSpatialDerivative_of_differenceQuotient_bound` | PASS；内部构造真实局部 L² 弱导数并保持同一范数界。 |
| 122 / 41978 | `Carleman.exists_weakH2_of_differenceQuotient_bounds` | PASS；同一原 u 的完整 H² 提升及真实 Sym Hessian 能量界，无跨界 H² 前提。 |

## 依赖与固定本地证据

T232 冻结报告 `7174f716fb09a02cc6ab4ffcac119ead1d4848bb` 已全文读取（checked_sha 为本批数学 base，reviewed_at=`2026-10-20T06:58:05+00:00`，15/15 PASS）。同时直接读取实际 `FullSpaceDifferenceQuotient`、`WeakDerivativeStrongLimit`、`StrongL2Limit`、`FullSpaceTestPairing`、`WeakDerivativeBoundedTest`、`BoundedTestRepresentation`、`WeakH2BoundedTest`、`SecondOrderJetAssembly` 及原弱测试定义，核对上述调用和身份。新模块导入闭包 **189 个 Carleman 文件**，其中 **188 个旧文件**与数学 base 逐 Git blob 不变。没有因读取旧报告而跳过本批关键前提审查。

- `/tmp/carleman-t233-local-evidence.json`：source=local、PASS；checked/source 都为本报告 proof，finished_at=`2026-10-20T07:02:41.274656+00:00`。真实 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 执行记录均 exit 0。本报告核对这些执行记录，不声称重新运行。
- `/tmp/carleman-t233-local-source-manifest.txt`：**1030 项、111756 bytes**，SHA256 `87d283362a6f5571e619c88320a612f48e4f22c342be01f17d99e4a3972278d4`。独立枚举全部 fixed proof tracked `.lean` 与三项构建配置，路径集合、唯一性及所有 Git blob 摘要全部匹配。
- `/tmp/carleman-t233-target-build.log`：**3369 jobs** 成功，116 bytes，SHA256 `5784484c39c7ae90df1c598e093e77f9223989d5c51143f284f38ef4043738ce`。`/tmp/carleman-t233-build.log`：**4272 jobs** 成功，80 bytes，SHA256 `2b10ea469a7f4066a39bf238f8c2a30103550c50614e8d8de2e8f88c0f90fca1`。`/tmp/carleman-t233-axioms.log` 为 0 bytes。
- `/tmp/carleman-t233-difference-criterion-local-axioms.txt`：**3224509 bytes**，SHA256 `dc3f3eafe7b8fdc0c780f57a015a9a3a0006fe86b4842adafd8aac59163ce610`，与固定证据摘要一致。八项完整类型与公理均核对；全部显式输出 **3784 个公理列表及 10 个无公理记录**仅含正常 `propext`、`Classical.choice`、`Quot.sound` 或无公理。原 `privateToUserName`/`collectAxioms` 全命名空间白名单逻辑未改，末行确认 **9596 声明递归审计 PASS**，没有 sorryAx 或额外数学公理。
- 固定根导入及八项 `#check`/`#print axioms` 齐全。Lean 4.35.0，编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib checkout 无修改且为固定 lock `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿相对数学 base 未变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

无修复项。接受本批 **AUXILIARY 差商强极限及局部弱导数/H² 充分判据**；保持 18/26，不提升 P023。报告正文及 reviewed_at 冻结后仅单文件提交，不改数学、台账、原稿或其它报告，不 push。
