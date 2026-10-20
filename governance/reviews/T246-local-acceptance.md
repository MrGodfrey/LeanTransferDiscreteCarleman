# T246 / C262 独立本机验收

- checked_sha: `ebc85ddad04c9b4008fa5b3e89a05696eff19bfb`
- mathematical_base: `108394721c27094589e1eea0c77c63083625340d`
- reviewed_at: `2026-10-20T09:06:02+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，11/11 定理，未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；真实有限光滑分割和同状态 H² 拼接，原有界指数和光滑内域上全部已给定 H¹₀ 弱 Poisson 解的全域 H² 及原负 Laplacian 身份。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/FiniteLocalH2Gluing.lean`、11 项 raw 完整类型、公理、analysis/MATH_SPEC/台账，并核对原稿 `paper/main.tex:2659–2665`。本批完成每个所述光滑内域的全域 H² 成员资格；原 Corollary A.2 所需的凸域统一估计、穷竭传递及原多面体完整实现尚未完成。

## 实际数学与量词

1. **分片由真实定理构造。** 输入为闭 K、同一有限指标集上的开放有界 V_i 和覆盖 K 的资格。调用实际 mathlib `SmoothPartitionOfUnity.exists_isSubordinate`，不是输入一个假定的 partition。已核对其 `IsSubordinate` 指整个拓扑支撑包含于 V_i；欧氏空间的真实光滑结构供应所需实例。各支撑是闭集且包含于有界 V_i 的紧闭包，因而实际紧。所得 η_i 均为 `SpatialTest univ`，全局 C∞、0≤η_i≤1；有限总和在 K 上为 1。没有把仅局部光滑或普通 support 包含误认成完整测试资格。
2. **限制配对只延拓合法测试。** `monoDomain_inner` 对 T⊆S、φ∈SpatialTest T 和任意原 S 上 L² v，利用原测试的实际零延拓与限制伴随，证明配对等于限制 v 后在 T 上的同一配对。导数版本把实际 `derivativeTest e` 代入，因其仍紧支于 T，所得任意方向导数的身份同样合法。这里没有给 v 添加导数，也没有零延拓局域 H² 状态。所有配对在各自真实限制体积上进行。
3. **局域测试和 L² 收缩真实。** 对任意原 φ，χ_i=η_iφ 由整个支持包含成为 R_i 内的真实紧支光滑测试；`R_i⊆S` 使其可重新标记为 S 内的同一函数。实际 Lp 代表、原限制以及 |η_i|≤1 给 `‖χ_i‖_{L²(R_i)}≤‖φ‖_{L²(S)}`。不是凭测试名字认定范数相同，也没有以裁剪区域的体积因子或任意常数替代真实收缩。
4. **完整 H¹ 测试恒等式保留所有截断导数。** `partition_jet` 先在 S 上由 Ση_i=1 和有限 AE 代表求和证明值身份，再对已经合法的弱 jet 使用开放域上的值唯一性，严格得到
   `φ.sobolevJet=∑i (monoDomain χ_i).sobolevJet`。
   这是完整 H¹ jet 的等式。后续才对它取实际一阶字段和坐标导数，得到所有导数的准确有限和；因此 Dη_i 的项在此完整身份中保留并相消，没有在乘积微分时遗漏它们。此步骤不假定各个 η_i 常数或导数为零。
5. **同一原梯度的全部二阶分布测试界。** 输入的每个局域 U_i∈H²(R_i) 都满足整个 H¹ 截断等于同一 u 的限制。取其一阶字段后，真实限制与坐标 CLM 交换给 `D_a U_i=(D_a u)|R_i`。对任意原坐标 a,b 和任意原 φ，将第 4 项导数身份代入配对，逐项使用第 2 项限制配对及 U_i 的实际弱链，得到负 Hessian 配对；其负号在绝对值估计中正确消去。Cauchy–Schwarz、真实分量范数≤完整二阶字段范数及第 3 项收缩给
   `|⟨D_a u,D_bφ⟩|≤(∑i ‖field₂U_i‖)‖φ‖`。
   整个坐标族和全部原测试均覆盖。未要求局域 H² 零迹或为其构造跨边界 H² 零延拓，也未额外输入重叠上的 Hessian 相等。
6. **真实 Riesz 与混合交换恢复全域同一状态。** 已直接读取所调用的 `exists_weakH2_of_gradient_test_bounds`、弱测试表示及混合交换实现：有界测试泛函以负导数配对定义，真实 Hahn–Banach 延拓/Riesz 给各 L² 二阶弱导数；两个原弱链和真实光滑测试导数交换使混合分量相等。随后按无序 `Sym (Fin d) 2` 装配完整二阶字段，原一阶字段保留，严格 `truncate¹ W=u`。得到的实际 bound 是
   `‖field₂W‖²≤card(Sym(Fin d,2))·(∑i‖field₂U_i‖)²`。
   该界与真实无序二阶纤维范数一致；局部范数和是有限且非负的，未把一个未证明有界的分布命名为 L² 函数。
7. **从局域资格到真正有限覆盖。** 有限覆盖 helper 在 `closure S` 上内部构造第 1 项 partition，并以 R_i=S∩V_i 应用全部测试论证。紧闭包 helper 则对每个真实 c∈closure S 选其正半径球及局域 U_c，使用实际紧性提取有限子覆盖，以该有限集合的 subtype 为真实有限指标；没有假定原覆盖已有限，也没有把依赖原 u 的局域半径改写成统一半径。一般拼接 helper 对任意 H¹ 状态有效，不要求 H¹₀ 或 PDE；最终应用才内部供应局部 H²。
8. **内点与边界覆盖同一闭包。** 对 c∈S，从原开放性选 ball(c,ε)⊆S，取 δ=ε/2；`closure(S∩ball(c,δ))⊆closedBall(c,δ)⊆S`，有限维有界闭包紧性内部给原内部 H² 定理的资格。调用的是原 u/f 的完整弱 Poisson 身份，输出同一限制状态。对正则解析子水平域 S={g<a}，c∈closure S 而 c∉S 时，开放域的准确 frontier 身份使 c 真正属于边界；边界数据 g(c)=a、Dg(c)≠0 接到已验收 T245。已直接读取其真实图侧、截断、T242/T241 调用，局部正则性来自原 H¹₀ 弱方程而不是本批新假设的 H² 状态。
9. **全域方程和最终实际内域。** 拼接得 U 后，`negativeLaplacian_isWeak U` 与 `truncate¹ U=u` 给同一 u 的弱右端；原全部测试的右端唯一性使 `negativeLaplacian U=f`，没有更换载荷或只给配对近似。最终指数和 theorem 从原有限半空间交的有界性取得实际内域紧闭包/有界性，从真实内点 z 及任意 frontier 点内部给准确水平 1/2 和非零导数，解析性由原有限指数和提供。故最后输入是原几何数据、已给定原 H¹₀ 状态、原 L² f 和原弱方程，未输入图、partition、局部 H²、Hessian 界或变换后 PDE。

所有结论保留原真实限制测度、完整状态和全部测试。最终 theorem 是对任意**已给定的弱解**证明正则性，不另声称对每个 f 构造解。有限集合可为空、S 可为空；一般拼接没有额外 d>0 假设。非零边界导数需要实际法向时才由原几何供应；没有在零维或空 frontier 情形伪造边界点。常数 `Σ‖field₂U_i‖` 可依赖所选覆盖和原状态，各局部图、半径还可依赖具体内域。它不构成随穷竭统一的 Hessian 估计；本批也未以闭图定理或有限分割偷取这种统一性。

## 全部声明逐项结论

名称统一带前缀 `Carleman.`。源码行指固定 `FiniteLocalH2Gluing.lean`；raw 行指固定审计文件完整类型的位置。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 14 / 43481 | `exists_finite_smooth_partition` | PASS；实际 subordinate partition、紧支、全局 C∞、[0,1] 及有限和 1。 |
| 32 / 43493 | `SpatialTest.monoDomain_inner` | PASS；原值配对的实际限制/测试零延拓身份。 |
| 46 / 43500 | `SpatialTest.monoDomain_derivative_inner` | PASS；任意真实方向测试导数的相同配对身份。 |
| 55 / 43508 | `SpatialTest.cutoffTransfer_toLp_norm_le` | PASS；真实局域乘积测试的 L² 收缩。 |
| 69 / 43515 | `SpatialTest.partition_jet` | PASS；完整 H¹ jet 求和身份，截断导数无遗漏。 |
| 88 / 43524 | `exists_H2_of_finite_local_partition` | PASS；全部分布测试界、真实 Riesz/混合组装、同一截断及显式平方界。 |
| 127 / 43544 | `exists_H2_of_finite_local_cover` | PASS；内部构造实际 partition，恢复全域同一 H²。 |
| 142 / 43558 | `exists_H2_of_compact_closure_local` | PASS；真紧闭包、正球覆盖及有限子覆盖，未加入统一半径。 |
| 163 / 43570 | `exists_local_interior_H2_ball` | PASS；原开放域内部球的资格及原方程内部 H²。 |
| 179 / 43583 | `exists_dirichlet_H2_of_regular_analytic_sublevel` | PASS；全部内点/边界局域化、原 H¹₀ 状态全域 H²、实际负 Laplacian=f。 |
| 202 / 43595 | `halfspaceSmoothInner_dirichlet_H2` | PASS；真实有界指数和内域内部供应全部几何与局部正则性资格。 |

## 固定依赖与本地证据

导入闭包 **249 个 Carleman 文件**，其中 **248 个旧文件**相对 base 逐 Git blob 不变，唯一新模块为 `FiniteLocalH2Gluing`。已直接读取本批、`SublevelGraphRegularity`、`InteriorPoissonRegularity`、`WeakH2BoundedTest`、`WeakDerivativeBoundedTest`、`BoundedTestRepresentation`、`WeakMixedDerivative`、`DirichletDistribution` 和 `WeakLaplacianLimit`，并核对既有真实限制/测试零延拓接口。T245 冻结报告全文读取并核对提交 `eadb9b67a43549dd5d75427b3e285869662fa83f`；checked_sha 为本报告 base，reviewed_at=`2026-10-20T08:54:55+00:00`，12/12 PASS。未用报告替代本次实际调用审查。

mathlib 的 `SmoothPartitionOfUnity` 定义、全拓扑支撑 subordinate 资格、存在定理的实际构造、[0,1] 与有限求和接口已直接读取。Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入及全部 11 项 `#check`/`#print axioms` 齐全。

- `/tmp/carleman-t246-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T09:01:59.956037+00:00`；`lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 的实际执行记录均 exit 0。
- `/tmp/carleman-t246-local-source-manifest.txt`：**1043 项、113208 bytes**，SHA256 `eb5fd852c34aa8c5b51d50567bf9e412b9cd32811e909148038a10996f32cf1d`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性和逐项摘要均与固定 Git blob 匹配。
- `/tmp/carleman-t246-target-build.log`：**3434 jobs** 成功，108 bytes，SHA256 `3ea50f5828f9e0172818b6cd024b64c104db9177af4a107e011327e6c24ce0d8`。`/tmp/carleman-t246-build.log`：**4285 jobs** 成功，80 bytes，SHA256 `f3fb5944d8dec4fc60845975d3ce99e2339f6969eaeea90f9824f054eb48c360`。`/tmp/carleman-t246-axioms.log` 为 0 bytes。
- `/tmp/carleman-t246-finite-h2-gluing-local-axioms.txt`：**3349391 bytes**，SHA256 `b97ce3d7c1e180b0dc45b5b88e770793a8331e8adf267ad2bd96ef6bc8125734`。11 项完整类型逐一核对；全部 **3978 个显式公理记录**仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，实际尾部确认 **9989 声明递归审计 PASS**，无 sorryAx 或额外数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，未重跑全库，未查询远端 CI/看板，也未把本地成功称作 CI。

无修复项。接受本批 **AUXILIARY 真实有限 H² 拼接及原光滑内域弱解的全域 H²**，保持 18/26。强边界逼近、凸域统一控制及穷竭到原多面体仍待。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、公理工具或其他报告，不 push。
