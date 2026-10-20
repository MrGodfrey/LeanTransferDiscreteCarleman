# T261 / C277 / P011 — Proposition 6.1 独立论文级验收

- checked_sha: `708eae70c82d9c0b1d60f6907f0202201d518a16`
- mathematical_base: `cbd25fdee3e670d39fce5a03cbf172c02a890544`
- reviewed_at: `2026-10-20T11:09:22+00:00`
- reviewer: independent local Agent `/root/accept_spatial_foundations`
- result: **PAPER PASS；完整原 Proposition 6.1 / P011；2/2 显式定理通过，无阻断缺陷。**
- axiom_check: **PASS**；evidence_source: **local**。
- coverage_decision: **C277/P011 可以登记 REVIEWED / PAPER，原文覆盖可由主执行者更新至 20/26。** 本报告不修改台账，不提升 P024 或其它后续结果。

## 原命题与审查依据

直接读取固定新模块 `Carleman/Control/FullP1Realization.lean` 全文及两项完整展开类型、公理输出，T261 analysis、MATH_SPEC、固定任务/claim 清单。对照原稿 `paper/main.tex:1469–1608` 的 P1 定义、Proposition 6.1 及三步证明，并回读 `286–330` 的原允许权和范数、`395–468` 的 N1–N5。

原命题要求：固定 d=2,3 的非空有界凸多面体、原一致质量全 P1 空间，以及原形状正则和顶点邻接分级条件下，统一选取正阈值和常数，使全部 N1–N5 成立；误差尺度为 Ch、Ch²、刚度缺陷为零，测试恰为 Π_h(σ²z)。它不以连续 Carleman 估计为本命题的结论。正文导言中后续传递还需要的连续 CE，不应成为本命题额外验收门槛。

本次结论的核心不是名称 `Nonempty NumericalData`，而是其固定证明实际返回的具体构造及同一构造已经证明的完整性质。`NumericalData` 为传递证明保存部分字段，没有重复保存所有原定义性质；本报告已展开该结构、`WeightedTest`、`WeightedApproximation`，并逐项核对省略字段所对应的实际对象与定理。最终使用者不再提供 H² 正则性、投影稳定性、插值或超逼近假设。

## 两项显式定理

行号依次为固定 `FullP1Realization.lean` 源码和固定 raw 中的类型起点。两项与固定 T261/C277 清单、根导入和审计登记完全一致。

| 源码 / raw 行 | 声明 | 独立结论 |
| --- | --- | --- |
| 14 / 44922 | `Carleman.finite_halfspace_convex` | PASS。将原严格半空间交真实改写为集合交，由各线性半空间的凸性得到凸性；不假定目标几何性质。此 helper 甚至无需有限指标。 |
| 21 / 44925 | `Carleman.finite_halfspace_p1_realization` | PASS。对非空有界有限严格半空间交内部提供开性、凸性、有限体积、紧闭包及真实 Dirichlet H² 域包含，再应用同一完整 P1 数值构造；保留全部网格、权、时刻和状态量词。 |

`S={x | ∀ i, b i<L_i x}` 是原满维非空有界凸多面体的有限半空间表示，允许斜面、冗余约束和角点，不要求光滑边界或矩形。`0<d≤3` 包含原 d=2,3；实际严格内点是原非空域资格，没有增加几何正则性。有限测度由有界性内部推出，且有限个开半空间的交确为开域。

新定理中的 `hD` 是
`finite_halfspace_dirichlet_domain_le_h2 hdpos L b hb hz`
的实际证明值，不是箭头前的假设。直接核对其调用：从同一 `boundedDirichletOriginalForm` 的完整 associated operator 图取原 H¹₀ 弱解和实际算子载荷；T259 的真实正则性给二阶 jet，其 H¹ 截断精确恢复原状态，由值身份得到原域包含。没有将 D(A) 重新定义成 H²，也没有换成具有预设光滑代表的子域。此前 T126 的最后显式解析前提现已清偿。

## 同一全 P1 空间、原范数及 N1

实际状态空间为
`X=M.conformingSpace (dirichletSubspace S)`。已读 `SimplicialPartition.mem_conformingSpace_iff`：成员恰为原 H¹₀ 的 L² 值类，且每个真实单纯形上 a.e. 为仿射多项式。它不是预先指定的节点插值像或较小有限维空间。真实有限单元分割给有限维性和 X 的 L² 完备性；H¹₀ 本身没有被误认为 L² 闭子空间。X 使用原 L² 内积，无质量集中或节点 Euclidean 内积替换。

`conformingReconstruction` 的 R 是 X→V 包含，RH 是原 L² 包含；J 是 X 的真实 L² 正交投影。mass_adjoint 由实际投影内积恒等式证明，`conformingReconstruction_injective` 给 R 单射，`conformingReconstruction_G` 给 JR=Id，`conformingReconstruction_QH` 给 RJ 的环境实现正是 Π_h。无权质量范数相等；加权状态范数按同一实际 σ 乘法定义，所以加权重构上下界也是等式，常数为 1。

同一 `boundedDirichletOriginalForm` 的 V 为真实 H¹₀，其 scalarForm 为原全部弱梯度的 L² 配对。`galerkinStiffness` 使用 X 的真实 Hilbert Riesz 映射表示该形式。已读 `galerkinStiffness_form`、`symmetric`、`nonneg`、`unique`、`defect_zero`：刚度满足原 `(A_hz,v)=a(Rz,Rv)`，自伴非负，缺陷 b=0，η_A=0。对任意权和全状态，原逆权双因子缺陷界左端确为零。

有限维自动连续性仅用于定义固定网格上的能量提升及刚度。其可能依赖网格的算子范数没有进入投影、近似或测试统一常数；数值估计使用实际形式等式和另行证明的统一空间界。

## 原载荷、控制与 N2/N5

`conformingLoad` 的载荷空间为完整 H=L²(S)，Γ=J=Π_h，lift=Id_H。其兼容式 J·lift=Γ 是实际等式。原右逆 I_h 取 R 的 L² 包含；`conforming_load_right_inverse` 给 Π_h(R_hz)=z，故 ΓI_h=Id。lift 与 I_h 的加权稳定性均为等式，常数 1，不是 `NumericalData` 中未检查的命名。

真实控制空间是 `Lp ℝ 2 ((volume.restrict S).restrict ω)`，在原 ω⊂S 情形就是 L²(ω)。`conformingRegionControl` 为 Π_h 复合区域限制的 Hilbert 伴随。对原开、因而可测的 ω，`conformingRegionControl_apply` 和 `conformingRegionControl_pairing` 给

```text
B_h u = Π_h(E₀u),       (B_hu,z)_X = ∫ω u z,
B_h* z = z|ω.
```

最后一个身份由实际伴随复合、双伴随及投影伴随公式证明；所有原 L²(ω) 控制均覆盖，没有替换成全域代理控制或有限维节点控制。

`restrictRegion_weighted_sq` 把实际受限权范数精确识别为 ω 上的同一权密度积分；`conforming_region_weighted_observation` 对任意 BoundedMultiplier、任意 X 状态和 ω₀⊆ω，利用真实可积非负密度的积分单调性给 N5，常数 1。原 ω₀、ω 的开性和紧包含满足新定理较弱的可测/包含要求。泛型控制定义允许更一般集合，但原可测区域的零延拓及积分配对结论保留其正确前提。

`NumericalData` 中状态/载荷/控制 seminorm 的字段记录基权 τ=0、正 profile 的时刻采样。这里没有因此缩小原 N1/N2/N5 的权族或时刻范围：重构和载荷等式由定义对每个真实权、每个实 t 成立；区域加权估计的实际定理同样接受任意 BoundedMultiplier，不依赖时间网格节点。三个范数确为原加权 L² 范数，任意正常数 r 的权缩放由真实乘法和 `‖r·v‖=r‖v‖` 给原齐次性。权的严格正值与 `seminorm_definite` 保证它们是原范数而非退化代理。

## N3：完整原算子域上的同一误差

实际 `full_p1_numericalData` 内部调用 `full_p1_weightedApproximation_interface`；后者取 D 为同一完整 `a.model.domain`，以内部 hD 和原 `domain_le` 为资格。已直接读取该接口和 `weak_h2_allowed_projection_approximation` 的证明。

真实弱 H² 节点插值给同一残差，四权投影稳定性及真实梯度逆估计给全 P1 的正交投影误差 E。E 在选择权、时刻、幂和符号前由原状态与网格确定。接口通过开域弱 jet 值注入性证明 `−E` 正是原 `v−Q_hv` 的 canonical H¹ jet；这同时识别全部弱梯度，不能只将标量值相同当作未证梯度身份。

`WeightedApproximation.energy` 使用完整原
`Nσ(v)²=q²‖σv‖²+‖σ∇v‖²`，不是单独梯度半范数；其 l2 字段使用同一个原误差。`parameterNorm` 是 0、1、2 阶实际字段的 q²、q、1 加权范数和。二阶字段项的 q 因子恰为 1，故真实 Hessian 误差界给

```text
Nσ(v−Π_hv) ≤ Capp h Rσ(v),
‖σ(v−Π_hv)‖ ≤ Capp h² Rσ(v).
```

该接口覆盖全部原域状态、整个 [0,T] 和两种空间权符号；底层空间结论实际上允许任意实 τ、t。其所需投影稳定性、逆估计、真实闭包连续代表、节点/边界表示及插值误差均已在固定依赖中证明，没有将 Step 2 的结论留作调用者前提。

## N4：同一实际 Π_h(σ²z) 及真实导数

直接读取 `full_p1_weightedTest_interface` 和实际 `full_p1_numericalData` 的选择代码。对每个符号 e，代码选择 η=±1，使 `ρ.scaled η=ρ.signed e`。`htest` 的输出是存在同一个 `T`，同时满足

```text
T.op t = (galerkinWeightedTest X (ρ.scaled η) w τ t).toLinearMap,
T.derivative t = (galerkinWeightedTestDerivative X (ρ.scaled η) w H τ t).toLinearMap.
```

NumericalData.test 正是对这一存在证明使用 `Classical.choose`。由同一 `choose_spec`，上述身份属于实际所选见证；没有在后面另换任意测试。外层未重复巨大 dependent identity 类型，是接口压缩；本次 PAPER 判定依赖这个具体构造及已证身份，不把裸 `Nonempty NumericalData` 当作足以推出原指定测试的抽象公理。

设 F(t)=σ(t)R_h。实际定义为 `galerkinWeightedTest=F*F`。`galerkinWeightedTest_apply` 通过真实投影配对及乘子对称性证明它恰等于 Π_h(σ²z)，`galerkinWeightedTest_energy` 给精确等式 `(z,Tz)=‖σz‖²`。结合权 seminorm definite 和 inclusion 单射，z≠0 时右端严格正；实际对称性给 self-adjoint。因此原 eq:test-norm 和严格正定性虽没有全部重复存入精简 `WeightedTest`，在所用具体对象上均成立。

**可微性的接口区分。** `WeightedTest.hasDeriv` 和现有 `galerkinWeightedTest_hasDeriv` 显式记录二次配对的 `HasDerivWithinAt`，不是一条名为“整个 T 的算子范数导数”的新声明。本次另核对实际构造：`SpatialProfile.hasDerivWithinAt_weightCLM` 已在真实 L² 连续算子范数中给 σ 的导数；与固定 inclusion 复合给 F′。实 Hilbert adjoint 是连续线性等距映射，算子复合是连续双线性映射，mathlib 的 `HasDerivWithinAt.clm_comp` 给
`(F*F)'=F′*F+F*F′`，正是这里定义的 `galerkinWeightedTestDerivative`。故同一实际 T 具有原算子族可微性；不是从一个无关的二次配对猜测导数。这里是已核对对象和基础微分法则的直接组合，没有缺少新的正则性、紧性或统一性定理，也没有声称本批新增了独立的整个 T 导数声明。

时间界使用真实乘子导数和内积 Cauchy–Schwarz，保留平方权的因子 2；统一可取
`Ctime=2β(τStar+ρ.bound)+1>0`，与 T、网格、qmax 和状态无关。q(0)=q(T) 给实际测试端点相等。原 C² q 类通过已读 `TimeWeightRegularity.ofContDiffOn` 供应所需的一阶正规性；没有把一阶正规性反过来冒充整个原 q 类，也没有增加原 q 的条件。

已直接读取 `allowed_full_projected_superapproximation`、`full_p1_galerkin_superapproximation` 及其测试装配。真实残差是
`Π_h(σ²z)−σ²z`，在 `(−η,−τ)` 所给真实逆权中估计；完整 H¹ 值唯一性将残差 jet 识别为原规范 jet。原任意完整 V_h 状态都适用，且尺度精确为 `Csuper h qmax Nσ(z)`。四权投影稳定性、实际逆界、完整节点残差与 hq≤1 吸收由具体依赖内部供应，没有假设目标 superapproximation。

`superapprox` 字段对权保持 V 的证明参数 hw 作全称量化。这里实际 V=H¹₀ 的允许权及逆权保持已由同一 Dirichlet 乘法/闭包证明给出，并纳入已接受的 T260；hw 不是额外未清偿限制。最终 N3 与 N4 共用同一 X、R、J、profile 和 q。

## 网格、允许权和统一量词

真实 `SimplicialPartition` 由非退化单纯形、closure S 内含、原 S 覆盖及不同单元内部不交构成。`FaceMatching` 是交集由共同顶点凸包刻画，`BoundaryFitted` 是边界交由边界顶点生成；它们是原 conforming、边界贴合网格条件，不是待证分析估计。任意形状正则单纯形可用其实际内球表达 `diam(K)≤κr_K`；全定理量化这些实际内球见证，固定 κ 在网格之前。

局部尺度 `ℓ_K>0`、`c·diam(K)≤ℓ_K≤B·diam(K)` 和所有有序共享顶点邻接对的 `ℓ_j≤γℓ_i` 保留原 grading。邻接对称性同时给另一方向。`p1GradingLimit d` 正是 `(sqrt(d+2)+1)/(sqrt(d+2)−1)`，γ 的严格阈值没有放宽。h 为真实单元直径最大值；没有准均匀、全局尺度比或固定网格索引限制。

固定域、维数、profile、κ/c/B/γ、β/τStar 和观测集合后，先选择 δ>0、δ≤1、Ctime>0、Csuper>0、Capp>0，再量化全部有限网格索引类型、所有分割/内球/局部尺度、所有 w/g/H。全部状态与时刻位于后续字段内。实际取 δ=min(δtest,δapprox)，只要求 hqmax≤δ，不附加 dt 条件、时空耦合、状态正则性或频率限制。原命题单个泛用正 C 可取这些固定常数与 1 的最大值，再单调放大 aE、a₀ 和各上界；这不改变任何统一量词。

两符号及全部 |τ|≤τStar 都在 approximation/test 字段中；对逆权同时反转 η、τ。其它三个接口的真实等式/不等式更强，适用于任意正实际权与任意实 t。profile 只要求闭包 C²，原负的 C∞ 闭包 profile 是其特例。空间常数不依赖周期或时间权；时间常数只依赖原固定 β、τStar、profile 界。原任意 T>0、原合法 TimeGrid 与原 q 类全部涵盖。

## 固定依赖与本地证据

新模块的 Carleman 递归导入闭包共 **629 个文件**，其中 **628 个旧源与 mathematical_base 逐 Git blob 不变**，唯一新增数学源为 `Control/FullP1Realization.lean`。另逐文件独立比对：

| 实际依赖根 | 已接受 proof | 完整闭包核验 |
| --- | --- | --- |
| `Control/FullP1NumericalData` | `8bfc0cb3d9a3d394805cfbb9720d903fc139bdfe`（T126/C142） | 511 模块，无新增、删除或修改；原辅助接口的实际证明完整保留。 |
| `Spatial/FiniteHalfspaceRegularity` | `0a4c425a254d6bc108651a078b6c0adbcc02b9f5`（T259/C275） | 313 模块，无新增、删除或修改；本批使用其实际域包含。 |

复用已验收且不变的底层证明，另直接阅读上述 N1–N5 关键定义、实际投影/误差/测试构造及正则性调用。已读取 T126 报告的完整数学核验与剩余 hD 说明；该剩余项现由具体定理内部清偿。T259 报告 commit `8693fe2b3f59764bf3544d6c81abba6a3d29bcd1` 与本固定树中的报告逐字节一致。T260 报告 `90003a32772cd54be6d442575e293c281516cecf` 全文已读，reviewed_at=`2026-10-20T10:59:42+00:00`，完整 P023 PAPER PASS；15066 bytes，SHA256 `0d62a478c7bbc547e8f892eaa168e76d2bdaeb0fe3998356a95ea700fb37ecc2`，同样已包含于本 proof 且逐字节一致。

实际读取 `/tmp/carleman-t261-local-evidence.json`：source=local、status=PASS，checked/source SHA 均精确为本报告 proof；`ci_url=null`，finished_at=`2026-10-20T11:02:02.703346+00:00`。`lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均实际记录 exit 0，固定任务另记录定向退出 0。核对实际日志及原始文件如下：

| 文件 | 核验结果 |
| --- | --- |
| `/tmp/carleman-t261-target-build.log` | 本模块成功，3855 jobs；106 bytes，SHA256 `60478d2f5ffd5c54320106d127570b8abca3e71fba85326993460a4910d04651`。 |
| `/tmp/carleman-t261-build.log` | 根目标成功，4300 jobs；80 bytes，SHA256 `1392f5f2e662f7de1d08fbeb310b75a6a0460a4c36c204bb40a771754a786f03`。 |
| `/tmp/carleman-t261-local-source-manifest.txt` | 1058 个唯一条目、114843 bytes，SHA256 `79ec7173827df25a3430da2c6c721484d1fcee450a37e2aac649bbc81fb9867a`。独立核对精确路径集合及每项固定 Git 原始 blob SHA256，全部一致。 |
| `/tmp/carleman-t261-full-p1-realization-local-axioms.txt` | 3462803 bytes，SHA256 `ec1372cf92dbebb01673ccd456d360e8564bf2e7ac657e2ed034c90f7d5d727e`；实际 10321 项全 Carleman 递归公理审计 PASS。 |
| `/tmp/carleman-t261-axioms.log` | 0 bytes，stderr 为空。 |

两项完整类型及依赖公理均实际存在；解析 raw 中 4151 条公理列表和 10 条无公理记录，所有依赖仅 `propext`、`Classical.choice`、`Quot.sound`。递归审计末段相对基线未改变，没有缩小 namespace 或跳过依赖，没有 `sorryAx` 或新增数学公理。根模块实际导入新模块；完整清单从固定 claim/task 提取并与源码两项定理一致，不依赖缺失的外部声明 JSON。

Lean 固定 4.35.0，compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 锁定及实际干净 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿未改变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。没有使用未来 T262 工作树或动态审计作为本次证据，没有查询远端 CI/看板或重复全库构建。

## 最终判定与边界

**T261/C277/P011 完整原 Proposition 6.1：PAPER PASS。** 原全 P1 一致质量空间、原 H 载荷与 L²(ω) 控制、全部 N1–N5、指定投影测试、全允许权族、Ch/Ch²/0 尺度和原统一量词均已核对。结构压缩未改变具体构造所具有的原性质；本报告没有把未暴露的字段误记为新形式化声明。

可由主执行者登记 P011 已接受并更新覆盖至 **20/26**。连续 CE/P024、后续一般域控制结果不由本批升级。未发现需要修复的数学缺陷；本报告仅固定版本有效，单文件提交后正文与 reviewed_at 冻结。
