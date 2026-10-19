# T140 / C156 独立本机验收

- checked_sha / source_sha：`e1774a58f1c57c8a3305173b5195beea5ffd53b7`
- 数学基线：`b60153e14ed7085f5828aea582fbc74ade8286aa`
- reviewed_at：`2026-10-19T08:41:13+00:00`
- 验收者：独立本机 Agent `accept_spatial_foundations`；未参与本批实现。
- 结论：**PASS — C156 可升级为 REVIEWED，scope 保持 AUXILIARY。** 未发现阻断性数学缺陷。
- 原文覆盖仍为 **16/26**。本报告不提升 P023 / `prop:analytic-realizations`，不认定全局 H² 或连续 Carleman 估计完成。

## 固定对象、原文和审查范围

源码、原稿、分析与台账均从上述 Git 对象读取；未将工作树后续增量或动态 `.ci/axioms.txt` 作为证据。已阅读 `governance/analysis/T140-odd-box-poisson.md`、`governance/MATH_SPEC.md` 的 T140 段、固定 C156 台账，以及八个新模块的全部实际定义和证明。另逐项读取固定原始公理文件中的全部 40 项展开类型，检查相关旧证明的实际实现。

原稿 `paper/main.tex:2659` 的 `prop:analytic-realizations` 要求盒域任意固定维数上的原 Dirichlet Laplacian，原证明通过凸域正则性给出 `D(A)=H²∩H¹₀` 和椭圆估计。本批是盒域路线的单个下侧面延拓步骤，忠实使用原弱 H¹₀ 解和同一个 L² 右端；它还不是该原命题的完整证明。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，本次未改稿。

令 `S=openCoordinateBox a b`，每轴 `a j < b j`，选任意 `r : Fin d`，反射为 `R(x)ᵣ=2aᵣ−xᵣ`，其它坐标不变。代码实际定义

`U = E₀u − reflectCoordinate r (a r) (E₀u)`，`F = E₀f − coordinateReflectionLp r (a r) (E₀f)`，

并将它们限制到 `T=lowerReflectedBox a b r`，其第 r 轴区间为 `(2aᵣ−bᵣ,bᵣ)`，其它轴区间不变。输入是任意原 `WeakSobolevJet d 1 (volume.restrict S) S`、其实际 `dirichletJetSpace S` 成员证明、任意原 `Lp ℝ 2 (volume.restrict S)` 右端及 `IsWeakNegativeLaplacian u f`。结论中的 U、F 是这两个指定对象，没有存在量词换成其它解。

## 全部 40 项声明

以下清单与固定 C156 的 `lean_declarations`、`/tmp/carleman-t140-odd-box-declarations.json` 完全一致。八模块均被固定 `Carleman.lean` 导入；每个名字均有固定 `tools/CheckAxioms.lean` 中的 `#check @...` 和 `#print axioms ...`，并实际出现于远端原始产物。表中位置均为固定 SHA 的源码位置。

| # | 完整声明 | 固定位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `Carleman.SpatialTest.fullJet` | `Spatial/ReflectionTest.lean:12` | PASS；实际全空间 H¹ jet，由原测试的合法 Dirichlet 零延拓构造。 |
| 2 | `Carleman.SpatialTest.fullJet_value_ae` | `Spatial/ReflectionTest.lean:16` | PASS；全空间 a.e. 值等于同一测试函数。 |
| 3 | `Carleman.SpatialTest.fullJet_restrict` | `Spatial/ReflectionTest.lean:20` | PASS；开原域上的完整 jet 限制恢复原测试 jet。 |
| 4 | `Carleman.SpatialTest.reflectCoordinate` | `Spatial/ReflectionTest.lean:24` | PASS；实际反射仿射拉回，紧支持和光滑性由真实映射传输。 |
| 5 | `Carleman.SpatialTest.reflectCoordinate_value` | `Spatial/ReflectionTest.lean:29` | PASS；点态值确为 φ(Rx)。 |
| 6 | `Carleman.SpatialTest.reflectCoordinate_fullJet` | `Spatial/ReflectionTest.lean:33` | PASS；保测 a.e. 拉回与弱唯一性给整个 jet 的反射身份。 |
| 7 | `Carleman.SpatialTest.oddReflectionTest` | `Spatial/ReflectionTest.lean:44` | PASS；实际全空间测试 φ−φ∘R。 |
| 8 | `Carleman.SpatialTest.oddReflectionTest_value` | `Spatial/ReflectionTest.lean:48` | PASS；精确点态差及符号。 |
| 9 | `Carleman.SpatialTest.oddReflectionTest_fullJet` | `Spatial/ReflectionTest.lean:54` | PASS；同一差的完整弱 jet，与反射算子一致。 |
| 10 | `Carleman.zeroExtendLp_inner` | `Spatial/FullSpaceTestPairing.lean:13` | PASS；任意完整实 Hilbert 值 L² 的真实零延拓/限制伴随身份。 |
| 11 | `Carleman.WeakSobolevJet.zeroExtendDirichlet_pairing` | `Spatial/FullSpaceTestPairing.lean:20` | PASS；完整梯度内积的零延拓配对等式。 |
| 12 | `Carleman.SpatialTest.fullJet_eq_zeroExtend` | `Spatial/FullSpaceTestPairing.lean:27` | PASS；实际测试 fullJet 与原域零延拓相等。 |
| 13 | `Carleman.SpatialTest.fullJet_pairing` | `Spatial/FullSpaceTestPairing.lean:32` | PASS；全空间梯度配对严格变为原域配对。 |
| 14 | `Carleman.SpatialTest.fullJet_inner` | `Spatial/FullSpaceTestPairing.lean:41` | PASS；右端 L² 配对同样准确限制。 |
| 15 | `Carleman.SpatialTest.fullJet_boundary_mem` | `Spatial/FullSpaceTestPairing.lean:48` | PASS；显式全边界零值经已证光滑边界引理推导真实 H¹₀ 闭包成员。 |
| 16 | `Carleman.WeakSobolevJet.oddExtend` | `Spatial/OddReflectionPoisson.lean:13` | PASS；指定实际 H¹ 奇延拓 E₀u−RE₀u。 |
| 17 | `Carleman.oddExtendLp` | `Spatial/OddReflectionPoisson.lean:18` | PASS；同一实际右端的 L² 奇延拓。 |
| 18 | `Carleman.oddExtend_poisson_full_test` | `Spatial/OddReflectionPoisson.lean:22` | PASS；完整梯度及右端反射伴随给全空间测试身份；通用引理明确保留 hzero。 |
| 19 | `Carleman.oddExtend_isWeakNegativeLaplacian` | `Spatial/OddReflectionPoisson.lean:41` | PASS；对 T 的全部原测试成立，使用显式测试边界资格。 |
| 20 | `Carleman.coordinateReflectionLp_continuous` | `Spatial/ReflectionContinuity.lean:12` | PASS；真实 L² 反射等距导出连续性。 |
| 21 | `Carleman.WeakSobolevJet.reflectCoordinate_tendsto` | `Spatial/ReflectionContinuity.lean:17` | PASS；值和全部梯度分量在原完整 H¹ 拓扑连续。 |
| 22 | `Carleman.SpatialTest.oddReflectionInto` | `Spatial/OddReflectionDirichlet.lean:15` | PASS；用 S⊆T、R⁻¹S⊆T 构造真正紧支持于 T 的奇测试。 |
| 23 | `Carleman.SpatialTest.oddReflectionInto_value` | `Spatial/OddReflectionDirichlet.lean:20` | PASS；与指定奇测试的点态函数一致。 |
| 24 | `Carleman.SpatialTest.oddExtend_test` | `Spatial/OddReflectionDirichlet.lean:24` | PASS；原测试的指定奇延拓限制等于构造出的 T 测试完整 jet。 |
| 25 | `Carleman.WeakSobolevJet.oddExtend_tendsto` | `Spatial/OddReflectionDirichlet.lean:32` | PASS；原 H¹₀ 序列的全空间奇延拓强 H¹ 收敛。 |
| 26 | `Carleman.WeakSobolevJet.oddExtend_mem` | `Spatial/OddReflectionDirichlet.lean:40` | PASS；实际紧支测试序列、连续限制和闭包闭合给 T 上 H¹₀ 成员资格。 |
| 27 | `Carleman.lowerReflectedBox` | `Geometry/LowerReflectedBox.lean:12` | PASS；仅更新所选下端点为 2aᵣ−bᵣ。 |
| 28 | `Carleman.coordinateReflection_fixed_plane` | `Geometry/LowerReflectedBox.lean:15` | PASS；平面 xᵣ=c 上反射逐坐标固定。 |
| 29 | `Carleman.lowerReflectedBox_boundary_exclusion` | `Geometry/LowerReflectedBox.lean:23` | PASS；原边界上不在反射平面的点及其反射均不属于 T，含角点、其它面和对面。 |
| 30 | `Carleman.lowerReflectedBox_no_original_overlap` | `Geometry/LowerReflectedBox.lean:51` | PASS；S 内点反射后不在 S，严格坐标不等式证明。 |
| 31 | `Carleman.lowerReflectedBox_contains_original` | `Geometry/LowerReflectedBox.lean:59` | PASS；正边长推出 S⊆T。 |
| 32 | `Carleman.lowerReflectedBox_contains_reflection` | `Geometry/LowerReflectedBox.lean:68` | PASS；实际反射原像 R⁻¹S⊆T，支撑方向正确。 |
| 33 | `Carleman.lowerReflectedBox_test_boundary` | `Spatial/BoxOddPoisson.lean:14` | PASS；任意 T 测试的奇差在原全部边界逐点为零，内部清偿通用 htest。 |
| 34 | `Carleman.lower_box_odd_poisson` | `Spatial/BoxOddPoisson.lean:25` | PASS；任意原弱 H¹₀ Poisson 解的指定延拓在扩大盒满足同一真实弱方程。 |
| 35 | `Carleman.oddExtend_restrict_original` | `Spatial/BoxOddPoisson.lean:39` | PASS；真实 L² 指示函数身份、保测反射及弱导数唯一性恢复整个原 jet。 |
| 36 | `Carleman.lower_box_odd_restrict` | `Spatial/BoxOddPoisson.lean:60` | PASS；盒几何内部供应不交条件，原状态准确恢复。 |
| 37 | `Carleman.lower_box_odd_dirichlet` | `Spatial/BoxOddPoisson.lean:68` | PASS；盒包含关系内部供应，指定扩大盒状态属于原 H¹₀。 |
| 38 | `Carleman.oddExtendLp_norm_le` | `Spatial/OddReflectionBounds.lean:12` | PASS；真实右端全空间 L² 范数≤2倍原范数。 |
| 39 | `Carleman.WeakSobolevJet.oddExtend_value_norm_le` | `Spatial/OddReflectionBounds.lean:19` | PASS；真实值字段 L² 范数≤2倍原值范数。 |
| 40 | `Carleman.WeakSobolevJet.oddExtend_gradient_norm_le` | `Spatial/OddReflectionBounds.lean:25` | PASS；完整 Euclidean 梯度字段 L² 范数≤2倍原梯度范数。 |

## 数学审查依据

**真实反射、测度与全部弱测试。** 旧 `CoordinateReflection` 使用坐标符号翻转的实际线性等距同构和实际平移；反射是保体积的自逆仿射同胚。`CoordinateReflectionLp` 的对象是真正保测 Lp 拉回，实际 a.e. 代表身份和积分换元均已核查。梯度第 r 分量携带 −1，其它分量携带 +1；`CoordinateReflectionH1` 用全部 `SpatialTest` 的仿射拉回证明弱链，不要求输入光滑。标量反射自伴和完整梯度配对中的反射自伴分别用于右端与左端，法向符号没有遗漏。

`AffineWeakTransport` 的测试拉回通过真实逆像支撑与同胚保持紧性，微分使用实际 Fréchet 链式法则；没有仅验证某个有限测试族。新 `fullJet` 将实际紧支光滑测试作为全空间 H¹ 对象，相关等式首先在实际 L² 上取得 a.e. 身份，再用开域弱导数唯一性提升成完整 jet 等式。零延拓只对已知属于原 H¹₀ 的 u 使用；没有将一般 H¹ 函数的零延拓当作 H¹。

**原 H¹₀ 测试闭包与 Poisson 方程。** 通用 `oddExtend_poisson_full_test` 的奇测试可能接触原反射面，因此它没有伪称该测试紧支于 S。它使用原完整边界零值，调用 `SmoothBoundaryDirichlet` 推出该测试限制属于实际 `dirichletJetSpace S`，随后通过 `isWeakNegativeLaplacian_iff_dirichlet` 将原分布方程作用于这个 H¹₀ 测试。已检查该旧等价确由连续配对与原紧支测试闭包推出。

`SmoothBoundaryDirichlet` 本身由真实零延拓指示函数、全空间 Lipschitz、紧支性、凸边界零测与内缩强 H¹ 逼近得到原闭包成员；边界零测只用于导数的 a.e. 资格，未用于推出边界点值。内缩后支持严格位于域内，再用实际平滑化进入紧支测试闭包。该依赖未假设待证反射 PDE 或盒全局 H² 正则性。

对任意 T 测试 φ，实际计算为 `B(E₀u−RE₀u,φ)=B(u,(φ−Rφ)|S)`，原方程给右侧 `⟨f,(φ−Rφ)|S⟩`，再由实际零延拓/限制伴随与反射自伴得到 `⟨E₀f−RE₀f,φ⟩`。最终限制 T 的左右配对分别使用精确等式，因此目标 `IsWeakNegativeLaplacian` 对 T 上全部原测试成立，负 Laplacian 约定和奇差的负号一致。

**全部盒边界的内部清偿。** 原闭盒是 S 的真实闭包。若 x 位于原边界且 xᵣ=aᵣ，实际反射固定 x，所以奇测试差为零。其余边界点由闭盒坐标条件和 x∉S 推出 x∉T 且 Rx∉T；若任一属于 T，严格坐标不等式反而会推出 x∈S。测试的真实 `tsupport⊆T` 因而给两项均零。该论证对角点、其它各面和反射面的对面统一成立，不依赖边界 a.e. 陈述，也没有留下外部 htest 假设。最终定理内部供应 S/T 开性、S 凸有界非空及两个包含关系，输入只有原正边长盒与原弱解数据。

**扩大盒 H¹₀ 资格是实际闭包极限。** `oddExtend_mem` 从 hu 的原测试 span 闭包取强 H¹ 序列，并把每个 span 元素表示为一个实际原测试。S⊆T 与 R⁻¹S⊆T 保证每个奇反射测试真正在 T 内紧支。`oddExtend_test` 精确识别其 jet；真实零延拓的强 H¹ 连续性、反射值和全部梯度分量的连续性、限制连续性一起给原指定 U 的极限。T 上原 Dirichlet 图闭包的闭合性完成证明。此部分独立于 Poisson 方程，没有用“边界为零”直接替代 H¹₀ 成员资格。

**恢复、范数及量词。** S 内反射点位于原下端点之外，故实际 E₀u 在这些反射点 a.e. 为零。证明通过保测反射传递零延拓 a.e. 身份，严格在 Lp 商空间中计算；随后 `value_injective` 恢复完整原一阶 jet，而非只恢复值。U|S=u 是显式定理；T 中的状态是同一全空间 U 的限制。右端、值、完整梯度各自使用三角不等式、零延拓等距与反射等距取得全空间系数 2。再限制到 T 的范数不增，因此同一上界适用；本批没有声称更锐常数。常数 2 不依赖边长、平移、轴、原 u/f 或维数，也没有体积或节点数因子。

所有面结论量化任意 `d : ℕ` 与 `r : Fin d`。当 d=0 时不存在可选择的 r，面特定陈述为空量化；没有虚构零维面的构造。任意正边长、任意平移和任意所选下侧面均在实际类型中。通用辅助定理保留的几何或边界条件，在最终盒定理内部均已清偿。本批未假设原 u 光滑、H²、有经典迹或满足延拓方程。

## 依赖版本与公理

新八模块的 `Carleman` import 递归闭包共 163 模块，其中 155 个旧模块与固定基线逐文件内容相同。另对关键依赖的完整 import 闭包逐文件比较其已验收 `declaration_version`，均无变化：

| 依赖 | 已验收版本 | 本次核查根与闭包规模 | 结果 |
|---|---|---|---|
| C155 | `b60153e14ed7085f5828aea582fbc74ade8286aa` | `CoordinateReflectionH1`，77 模块 | 内容全部相同 |
| C154 | `d1dca8884990c684f923a4938e40a6cc88e1645f` | `SmoothBoundaryDirichlet`，118 模块 | 内容全部相同 |
| C146 | `5c1c62ee09ab89d7e28c0b484c02494958856b33` | `DirichletExtensionContinuity`，70 模块 | 内容全部相同 |
| C073 | `fbcd888532fe88caff4907495fad399fe6feeb55` | `DirichletZeroExtension`，69 模块 | 内容全部相同 |
| C057 | `3d5aa9cec281974bef7da9d37ffa11a8f9f75670` | `DirichletDistribution`，57 模块 | 内容全部相同 |

固定 Lean 为 `leanprover/lean4:v4.35.0`，编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；本机实际 `lake env lean --version` 与远端 result 相符。mathlib 固定于 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 checkout 同 SHA 且无本地修改。

固定原始产物含 2,582 条显式公理打印记录：2,573 条仅依赖正常基础公理的子集，9 条无公理；独立解析未发现 `propext`、`Classical.choice`、`Quot.sound` 之外的公理。40 项本批声明均在其中。末行实际为 `Axiom audit passed for all 7229 Carleman declarations.`，覆盖递归声明而非仅本批公开名称，没有 `sorryAx` 或新增公理。

## 构建及同 SHA 远端证据

已读取固定 `/tmp/carleman-t140-final-target.log`，实际记录最终 `BoxOddPoisson` 定向构建成功，共 **3,334 jobs**。已读取 `/tmp/carleman-t140-odd-box-full.log`，实际记录全库构建成功 **3,956 jobs** 和 **7,229** 声明公理审计通过。这些是核对既有固定日志，本报告不声称另行重跑完整构建。

独立查询 GitHub 后确认：push/main 的 [run 39223664696，attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39223664696/attempts/1) 的 head SHA 精确等于 checked_sha，run 为 `completed/success`，更新于 `2026-10-19T08:37:52Z`。三个实际 jobs 均已最终完成：

| job | ID | 实际状态 |
|---|---|---|
| lean | `117964646733` | completed / success |
| state-check | `117964646882` | completed / success |
| dashboard / snapshot | `117966113828` | completed / success |

本人分别通过 `gh run download` 从该 run 下载两项原始 artifact，未使用主执行者复制的结论替代下载：

| artifact | ID | 本机独立下载位置 |
|---|---|---|
| lean-ci-result | `12172742669` | `/tmp/carleman-t140-odd-box-main-ci/result.json` |
| lean-declaration-evidence | `12172513557` | `/tmp/carleman-t140-odd-box-main-axioms/axioms.txt` |

实际 result 为 `status=PASS`，`checked_sha=source_head_sha=e1774a58f1c57c8a3305173b5195beea5ffd53b7`，`finished_at=2026-10-19T08:36:35.891750+00:00`，目标 `Carleman`。远端原始 axioms 与固定 `/tmp/carleman-t140-odd-box-local-axioms.txt` 独立逐字节比较完全相同：两者均 **2,200,273 bytes**，SHA256 均为 **`1157dd43a7aa83b91a304275b8223e495a7f4c767ae33436c4548b062801573e`**。

## 签发范围

C156 在上述固定 SHA 上通过实际类型、逐项证明、原对象对应、关键依赖版本、公理、构建与同 SHA 正式 CI 的独立验收，可登记 REVIEWED / AUXILIARY。没有阻断性发现。单个下侧面的完整弱 Dirichlet Poisson 延拓已证明；全部上下盒面的迭代、与内部 H² 定理拼接及全局正则性仍待完成，P023 和其它原文条目不得因此提升。

本报告只新增本文件；未修改实现、台账、导入或原稿，未 commit/push。签发时间及内容在通知主 Agent 后冻结。
