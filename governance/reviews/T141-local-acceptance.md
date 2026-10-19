# T141 / C157 独立本机验收

- checked_sha / source_sha：`b818f314b275265490aa9b797779f7db0005ddb9`。
- base_commit：`e1774a58f1c57c8a3305173b5195beea5ffd53b7`。
- reviewed_at：`2026-10-19T08:55:48+00:00`。
- reviewer：独立本机 Agent `/root/accept_spatial_lemma`，未参与本批数学实现。
- result：**PASS**；axiom_check：**PASS**；34/34 项声明通过。
- scope：**AUXILIARY**。C157 可在本固定版本登记为 REVIEWED；完成原坐标盒 Dirichlet 全局 H² 正则、精确算子域和完整 H² 图范数右端估计。P023 / `prop:analytic-realizations` 不提升，原文覆盖保持 **16/26**。

本报告从固定 Git 对象读取全部九模块的定义、完整证明、原稿、T141 分析、MATH_SPEC、C157/T141 台账及关键依赖；逐项读取实际原始产物中的展开类型和公理。独立查询同 SHA 的正式 GitHub run/jobs/artifacts，独立下载原始文件并逐字节核对。执行者说明、既有依赖报告和 CI 通过均未代替本批语义审查。遵照本轮明确授权，只新增并单独提交本验收报告；当前 T142 实现、台账、根导入和动态 `.ci/axioms.txt` 不在本次审查或修改范围。

## 原文对应、原对象与结论边界

固定 `paper/main.tex:2659–2664` 的 Corollary A.2 / `prop:analytic-realizations` 要求固定有界凸多面体（d=2,3）或任意固定维数盒上的 Dirichlet Laplacian 满足 A1–A3。原证明以 Grisvard 的凸域正则性取得 `D(A)=H²∩H¹₀` 和椭圆估计，再用 Poincaré 与空间算子命题完成其余解析性质。本批采用实际奇反射加内部正则性的另一条证明路线，清偿其中**坐标盒的正则性部分**。它没有完成一般凸多面体、全部 A1–A3 包装或连续 Carleman 估计，因而不能据此将整个 P023 标为 PAPER。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，本批未改稿。

令 `S=openCoordinateBox a b`，每轴 `a i<b i`。输入是任意真实 `WeakSobolevJet d 1 (volume.restrict S) S`、它在原 `dirichletJetSpace S` 中的成员资格、任意真实 `Lp ℝ 2 (volume.restrict S)` 右端 f，以及原分布弱方程 `IsWeakNegativeLaplacian u f`。后者对 S 上全部原 `SpatialTest` 量化；H¹₀ 是这些真实紧支光滑测试在完整一阶图拓扑中的原闭包，未替换为逐点边界条件或较小的状态空间。

`exists_box_dirichlet_H2_bound` 输出同一原弱解的实际二阶 jet v，明确给出 `truncate v=u`、`negativeLaplacian v=f` 及完整二阶字段范数平方界。正维数下，`box_dirichlet_domain_eq_h2` 对由原梯度形式构造的实际算子证明精确子空间等式 `D(A)=sobolevSubspace d 2 … ⊓ dirichletSubspace S`；`exists_box_dirichlet_H2_estimate` 在所有 u/f 之前选定 K≥0，给出同一 v 的完整图范数 `‖v‖≤K‖f‖`。这里的图范数是三个真实 L² 导数字段的有限乘积范数，等价于通常的完整 H² 范数；它不是仅值的 L² 范数，也没有略去梯度或 Hessian。

## 全部 34 项声明

以下清单与 `/tmp/carleman-t141-box-h2-declarations.json`、固定 C157/T141 台账完全一致。位置均属于 checked_sha，文件前缀为 `Carleman/`。九模块全部被固定 `Carleman.lean` 导入；每项均有固定 `tools/CheckAxioms.lean` 中的 `#check @...` 与 `#print axioms ...`，并实际出现于独立下载的展开类型、公理产物中。

| # | 完整声明 | 固定源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `Carleman.upperReflectedBox` | `Geometry/UpperReflectedBox.lean:11` | PASS；仅将指定上端点更新为 2bᵣ−aᵣ，反射平面是 bᵣ。 |
| 2 | `Carleman.upperReflectedBox_boundary_exclusion` | `Geometry/UpperReflectedBox.lean:14` | PASS；原边界且不在上反射平面的点及反射点均不属于扩大开盒，含其它面和角点。 |
| 3 | `Carleman.upperReflectedBox_no_original_overlap` | `Geometry/UpperReflectedBox.lean:42` | PASS；原开盒内点的上侧反射严格越过原上端点。 |
| 4 | `Carleman.upperReflectedBox_contains_original` | `Geometry/UpperReflectedBox.lean:50` | PASS；正边长实际供应原盒包含。 |
| 5 | `Carleman.upperReflectedBox_contains_reflection` | `Geometry/UpperReflectedBox.lean:59` | PASS；真实反射原像包含，方向与测试支持所需一致。 |
| 6 | `Carleman.upperReflectedBox_test_boundary` | `Spatial/UpperBoxOddPoisson.lean:14` | PASS；任意扩大盒测试的奇差在原全部 frontier 逐点为零。 |
| 7 | `Carleman.upper_box_odd_poisson` | `Spatial/UpperBoxOddPoisson.lean:25` | PASS；指定奇延拓满足扩大盒上的全部原弱测试方程，内部供应边界测试资格。 |
| 8 | `Carleman.upper_box_odd_restrict` | `Spatial/UpperBoxOddPoisson.lean:39` | PASS；指定奇延拓限制回原盒，严格恢复整个原一阶 jet。 |
| 9 | `Carleman.upper_box_odd_dirichlet` | `Spatial/UpperBoxOddPoisson.lean:47` | PASS；实际测试闭包证明扩大盒 H¹₀ 成员，未用经典迹替代。 |
| 10 | `Carleman.subdomainLp_trans` | `Spatial/SubdomainComposition.lean:12` | PASS；真实 L² 商空间嵌套限制，由各代表 a.e. 身份和受限测度单调性证明。 |
| 11 | `Carleman.subdomainLp_self` | `Spatial/SubdomainComposition.lean:19` | PASS；真实自限制等于原 L² 类。 |
| 12 | `Carleman.subdomainLp_restrictRegion` | `Spatial/SubdomainComposition.lean:22` | PASS；全空间限制后再限制等于直接限制。 |
| 13 | `Carleman.WeakSobolevJet.restrictSubdomain_trans` | `Spatial/SubdomainComposition.lean:31` | PASS；任意阶全部字段的严格嵌套限制身份。 |
| 14 | `Carleman.WeakSobolevJet.restrictSubdomain_self` | `Spatial/SubdomainComposition.lean:38` | PASS；任意阶完整 jet 自限制身份。 |
| 15 | `Carleman.WeakSobolevJet.restrictSubdomain_restrictDomain` | `Spatial/SubdomainComposition.lean:44` | PASS；全空间 jet 的两级限制逐字段等于直接限制。 |
| 16 | `Carleman.IsPoissonExtension` | `Spatial/BoxPoissonExtension.lean:15` | PASS；谓词仅记录实际 H¹₀、PDE、完整 jet 恢复和右端/值/梯度三项界，没有公理字段。 |
| 17 | `Carleman.exists_odd_dirichlet_extension` | `Spatial/BoxPoissonExtension.lean:23` | PASS；从原弱解实际构造奇延拓，显式保留通用几何和测试边界条件，三项范数系数为 2。 |
| 18 | `Carleman.exists_lower_box_extension` | `Spatial/BoxPoissonExtension.lean:43` | PASS；原盒几何内部清偿通用下侧面全部条件。 |
| 19 | `Carleman.exists_upper_box_extension` | `Spatial/BoxPoissonExtension.lean:55` | PASS；原盒几何内部清偿通用上侧面全部条件。 |
| 20 | `Carleman.expandedBoxLower` | `Geometry/ExpandedCoordinateBox.lean:12` | PASS；已处理坐标端点为 2a−b，其余仍为 a，独立于 u/f。 |
| 21 | `Carleman.expandedBoxUpper` | `Geometry/ExpandedCoordinateBox.lean:15` | PASS；已处理坐标端点为 3b−2a，其余仍为 b。 |
| 22 | `Carleman.expandedBox_positive` | `Geometry/ExpandedCoordinateBox.lean:18` | PASS；任意有限处理集后的全部边长为正。 |
| 23 | `Carleman.expandedBox_contains` | `Geometry/ExpandedCoordinateBox.lean:25` | PASS；任意处理集的扩大开盒包含原开盒。 |
| 24 | `Carleman.expandedBoxLower_insert` | `Geometry/ExpandedCoordinateBox.lean:32` | PASS；未处理坐标的真实下反射端点与插入后端点精确相等。 |
| 25 | `Carleman.expandedBoxUpper_insert` | `Geometry/ExpandedCoordinateBox.lean:40` | PASS；在已下扩盒作上反射，精确产生 3b−2a，未误用原宽度。 |
| 26 | `Carleman.expandedBox_closure_inside` | `Geometry/ExpandedCoordinateBox.lean:50` | PASS；全部坐标处理后，原真实闭包严格包含于扩大开盒，含所有角点。 |
| 27 | `Carleman.IsPoissonExtension.refl` | `Spatial/PoissonExtensionComposition.lean:11` | PASS；原 H¹₀ 弱解给系数 1 的真实自延拓。 |
| 28 | `Carleman.IsPoissonExtension.trans` | `Spatial/PoissonExtensionComposition.lean:17` | PASS；严格限制复合保持同一 jet，D≥0 合法传递三项界并给系数 D·C。 |
| 29 | `Carleman.exists_finite_box_extension` | `Spatial/FiniteBoxPoissonExtension.lean:14` | PASS；真实有限集归纳逐坐标先下后上，完整 H¹₀/PDE/恢复均保持，系数恰 4^card(s)。 |
| 30 | `Carleman.derivativeComponent_norm_le_field` | `Spatial/BoxPoissonRegularity.lean:15` | PASS；任意阶真实 Euclidean 字段坐标 L² 范数≤完整字段范数。 |
| 31 | `Carleman.exists_box_dirichlet_H2_bound` | `Spatial/BoxPoissonRegularity.lean:22` | PASS；固定扩大盒内部 H² 给同一原 u 的二阶提升、实际 −Δv=f 及统一真实 Hessian 平方界。 |
| 32 | `Carleman.box_dirichlet_domain_le_h2` | `Spatial/BoxDirichletRegularity.lean:15` | PASS；从实际形式算子图提取原 H¹₀ 弱解，再用新正则性证明原算子域包含于完整 H²。 |
| 33 | `Carleman.box_dirichlet_domain_eq_h2` | `Spatial/BoxDirichletRegularity.lean:30` | PASS；新正向包含与既有全 H²∩H¹₀ Green 反向包含给精确原子空间等式。 |
| 34 | `Carleman.exists_box_dirichlet_H2_estimate` | `Spatial/BoxDirichletRegularity.lean:39` | PASS；由原弱方程和 Poincaré 内部消去值/梯度，统一 K 先于所有 u/f，控制同一提升的完整 H² 图范数。 |

## 关键数学核对

**上侧面、全边界和真实弱方程。** 上反射 `Rᵣx=2bᵣ−xᵣ` 的几何单独证明，未将下侧面结论错用于上面。原 frontier 点在反射平面上时 R 固定该点，奇测试 φ−φ∘R 为零；不在该平面时，利用原闭盒坐标及 x 不在原开盒证明 x、Rx 均不在扩大开盒，真实 `tsupport φ⊆T` 给两项为零。这个逐点论证包括其它各面、棱与角点；没有通过边界零测跳过角点。

已重读实际 `OddReflectionPoisson` 和 `OddReflectionDirichlet`：U 是合法全空间 H¹ 零延拓与其真实坐标反射之差，F 是同样的 L² 奇差。反射梯度的法向负号由实际弱链和完整梯度伴随处理；原方程通过原 H¹₀ 测试闭包作用于奇测试的限制，再由零延拓/限制配对和保测反射给 T 上全部原测试的 PDE。该奇测试未被伪称紧支于原 S；其全边界零资格由上述几何供应，再通过已验收的凸域光滑边界零函数 H¹₀ 引理取得原闭包资格。

扩大盒上的 H¹₀ 成员是从原测试 span 的强 H¹ 逼近出发：S⊆T 和 R⁻¹S⊆T 使每个奇测试真正紧支于 T；零延拓、反射与限制在完整 H¹ 图拓扑连续，闭包闭合给实际 U 的成员资格。没有将一般 H¹ 的零延拓当成 H¹，也没有将零延拓当成 H²。常数 2 分别来自实际右端、值、完整梯度的三角不等式及等距性，是合法安全上界；不声称最优的平方根常数。

**限制复合与 dependent transport。** `SubdomainComposition` 在 L² 上先以 `Lp.ext` 证明 a.e. 代表身份，再对所有导数字段做子类型外延，得到严格整个 jet 等式。实际 `restrictSubdomain` 的旧定义逐字段限制，并对全部原 `SpatialTest` 证明弱导数身份，因此新复合等式不是仅值投影的身份。有限迭代中 `transport` 先证明扩大域的真实集合相等，再 `subst` 传输带域索引的状态、载荷和证明；原始 u/f 始终固定。包含关系证明的 proof irrelevance 不改变任何 L² 值或弱导数字段，没有把不同域的状态未经证明混同。

**有限反射与角点成为内部点。** 每个新坐标 r 不在已处理集 s，因此当前该坐标仍是 (aᵣ,bᵣ)。先下反射到 (2aᵣ−bᵣ,bᵣ)，再围绕当前上端点 bᵣ 上反射到 (2aᵣ−bᵣ,3bᵣ−2aᵣ)。其它坐标保留已有扩大端点。两次 `IsPoissonExtension.trans` 给 `2·(2·4^card(s))=4^card(insert r s)`，包括 s=∅ 的系数 1 分支。对 univ 得实际 4^d 范数界，且原每个闭坐标区间均严格位于扩大开区间内，所以整个原闭盒（包括所有角点）紧包含于固定扩大开盒。证明无需分别假定面或角点正则性。

`IsPoissonExtension` 不把“存在延拓”当成输入；盒定理内部实际构造 v/g。该谓词记录完整一阶 jet 限制恢复，但未额外记录 g 限制等于 f 的字段。本次并未将缺少的字段暗中使用：最终 `negativeLaplacian v=f` 是将新 H² jet 的实际弱方程经 `truncate v=u` 改写后，与原 hf 对全部测试比较，通过 `unique_rhs` 的真实 L² 基本引理证明。因而仍是同一原右端，不能任意换成另一个载荷。

**原全部弱解的 H² 提升及常数次序。** `exists_interior_H2_bound` 只要求两个开域和内域闭包紧包含于外域；实际截断在输入 u/f 之前构造，M 也先于所有弱解选择。它由真实局部卷积 PDE、紧支测试 Hessian 能量、梯度强 L² 极限及全部弱测试恢复二阶字段，未预设原解 H²。这里用真实扩大盒和已经证明的延拓 U/F 清偿所有前提，再以严格限制复合恢复原 u 的整个一阶 jet。

实际二阶常数可取 `C=card(Sym(Fin d,2))·(M·4^d·(1+2d))²`。每个一阶坐标的 L² 范数≤完整 Euclidean 梯度字段范数，求和至多给 d 倍；三项延拓界一起给所用 `4^d(1+2d)(‖f‖+‖field₁u‖+‖value u‖)`。对非负量合法平方，并保留原内部定理的 `card(Sym(Fin d,2))`。常数在全部 u、hu、f、hf 之前；允许依赖固定盒和 d，不依赖解、右端、任意反射顺序或后来选择的 H² 提升。

**实际算子域与完整右端估计。** `boundedDirichletOriginalForm` 是原 H¹₀ 梯度形式的既有构造，不以 H² 域作定义。`dirichlet_operator_graph_iff` 将其任意真实域元素及实际算子值对应到原 H¹₀ 弱解；新正则性给相同 L² 值的 H² jet。反向 `h2_dirichlet_le_domain` 对任意 H²∩原 H¹₀ 使用全测试 Green 身份及原闭包，且实际算子值就是负的纯二阶坐标和。因此得到精确域等式，不是人为更换为 H² 的模型域。

对于纯 RHS 估计，固定盒有界性先给 R>0，选任一真实坐标 `i : Fin d` 并证明盒内 `|xᵢ|≤R`。原弱方程对 u 自测及 Poincaré 给 `‖field₁u‖≤2R‖f‖`、`‖value u‖≤(2R)²‖f‖`，包括零梯度/零右端分支。令 `B=1+2R+(2R)²`，合法开方给 Hessian 范数≤`sqrt(C)·B·‖f‖`，原完整 jet 范数≤三个字段范数之和，故 `K=(2R)²+2R+sqrt(C)·B` 有效。K 在所有原 u/f 之前，既不假设目标估计，也不重新选择另一个弱解。若需要严格正的常数可将 K 增大，实际声明准确只承诺 K≥0。

**假设和范围。** 最终域等式和纯 RHS 估计明确要求 d>0 及所有边长正；这是原非退化盒正维数情形，没有附加光滑代表、经典迹、H²、兼容性、外部反射 PDE 或先验二阶界。中间 Hessian 定理允许 d=0，有限集为空时没有选择不存在的坐标；正维数纯 RHS 证明才选择 `Fin d` 的方向。最终声明不声称退化空盒或任意形状盒间统一常数，不处理一般凸多面体。没有网格、时间权或状态截断假设。

## 依赖版本、公理和工具链

九新模块的 `Carleman` import 递归闭包为 **224** 模块；除九新模块外的 **215** 个旧模块与固定基线逐文件相同。另把关键依赖的完整 import 闭包与各自已验收版本逐文件比较，全部一致；读到的先前独立报告确认其既有范围。本批实际使用方式亦已从源码核对。

| 依赖 | 已验收 declaration_version | 本次比较根 / 模块数 | 结论 |
|---|---|---|---|
| C156，实际奇反射及范数 | `e1774a58f1c57c8a3305173b5195beea5ffd53b7` | `OddReflectionBounds` / 157 | 全部相同；结合基线比较覆盖实际盒延拓调用。 |
| C150，原内部 H² | `3d418d76a4959a094dcd26d2d157c213f297531d` | `InteriorPoissonRegularity` / 170 | 全部相同；闭包紧包含由本批内部供应。 |
| C147，弱方程和一阶估计 | `94f7ddd96b42ac046a4dc2cb14fffb5cd97f1402` | `DirichletWeakSolve` / 58 | 全部相同；未使用仍条件性的穷竭 H² 输入。 |
| C098，真实子域限制 | `59452751f05398e3446ed5305638a1e20dc89061` | `SubdomainContinuity` / 66 | 全部相同；完整原弱链保留。 |
| C057，真实算子图与 Green | `3d5aa9cec281974bef7da9d37ffa11a8f9f75670` | `DirichletDistribution` / 57 | 全部相同；反向包含和负 Laplacian 符号正确。 |

依赖验收参考：[T140](T140-local-acceptance.md)、[T134](T134-local-acceptance.md)、[T131](T131-local-acceptance.md)、[T082](T082-local-acceptance.md)、[T041](T041-local-acceptance.md)。其中 C156 进一步使用 C154 的真实光滑边界零函数 H¹₀ 结论；本批反对称测试的全部边界零前提已内部证明，而不是把该前提留给最终用户。

固定工具链为 Lean `4.35.0`、compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，本机实际版本与远端记录一致。mathlib 固定为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 checkout 同 SHA 且状态干净。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES 与此前已读版本哈希相同，本次重读适用验收/状态协议。

独立解析远端原始产物：**2,616** 条显式公理打印记录，其中 **2,607** 条的公理仅为 `propext`、`Classical.choice`、`Quot.sound` 的子集，另 **9** 条无公理；34 项本批声明全部存在。未出现其它公理、`sorryAx` 或未证明占位。固定九模块中没有 `sorry`、`admit` 或新增 `axiom`。原始末行实际为 `Axiom audit passed for all 7289 Carleman declarations.`，递归审计涵盖生成辅助声明，不仅是这 34 个公开名字。

## 构建与同 SHA 原始远端证据

已读固定 `/tmp/carleman-t141-dirichlet-regularity-target.log`：`BoxDirichletRegularity` 定向构建 **3,404 jobs** 成功。已读固定 `/tmp/carleman-t141-box-h2-full.log`：全库构建 **3,965 jobs** 成功，**7,289** 声明递归公理审计 PASS。本报告核对这些既有固定日志与正式远端证据，没有声称重跑另一次全库构建。

本人独立访问实际 GitHub [run 39225053273 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39225053273/attempts/1)，确认 main、head SHA 精确等于 checked_sha、run 为 `completed/success`。三个实际 jobs 均已最终成功：

| job | ID | 状态 | completed_at（UTC） |
|---|---|---|---|
| lean | `117969180893` | completed / success | `2026-10-19T08:49:42Z` |
| state-check | `117969181183` | completed / success | `2026-10-19T08:45:43Z` |
| dashboard / snapshot | `117970824846` | completed / success | `2026-10-19T08:49:54Z` |

实际 artifact API 返回的 run/head SHA 均相同，两个证据 artifact 未过期：

| artifact | ID | API 压缩大小 | 本人独立下载位置 |
|---|---|---|---|
| lean-ci-result | `12173342459` | 492 bytes | `/tmp/carleman-t141-box-h2-main-ci/independent/result.json` |
| lean-declaration-evidence | `12174175003` | 205,064 bytes | `/tmp/carleman-t141-box-h2-main-axioms/axioms.txt` |

下载使用同 run 的 `gh run download`。首个 result 目标路径已有文件，CLI 拒绝覆盖；本机 gh 不支持 `--clobber`，故最终下载到上表独立子目录，成功取得原始文件，并与父目录已有 `result.json` 比较一致。没有把主执行者提供的文件或成功说明当作独立下载。

独立 result 实际为 `PASS`，`checked_sha=source_head_sha=b818f314b275265490aa9b797779f7db0005ddb9`，目标为 `Carleman`，`finished_at=2026-10-19T08:48:39.817105+00:00`；文件 **537 bytes**，SHA256 `f0a85620b84d2caf0d74e719dd6d331b48095065e5fb30ba339025cba854ba74`。远端 raw 与固定 `/tmp/carleman-t141-box-h2-local-axioms.txt` 逐字节完全相同，均为 **2,216,514 bytes**，SHA256 均为 **`5837236580601c8df8c51a65b8d67eb278def318dfd18a7bbaecae4511a5d06e`**。API 压缩包 digest 分别为 `sha256:95891f4b8c01c5ce9f85f5138c85185b48d90b1c8111aca950d2459b522c4aba` 和 `sha256:c3a5fef251069050929209cfdb8b8a42becbb2f88af5549f2b45ac8594b7780c`；压缩包大小/digest 与解压后的 raw 大小/hash 是不同层次的记录。

## 签发结论

**T141 / C157 在固定 SHA 上 34/34 PASS，axiom_check PASS，无阻断性数学缺陷。** 原坐标盒上的全局 H² 正则、同一原弱解的完整提升、实际 Dirichlet 域等式及统一完整 H² 右端估计已清偿，可登记 REVIEWED / AUXILIARY。一般凸多面体正则、全部 P023 解析接口、FD 完整数值结论和连续 CE 不在本次签发范围，原文计数保持 16/26。

本报告按本轮授权单独提交；不包含实现、台账、根导入、原稿或后续工作树增量。签发时间和报告内容在通知主 Agent 后冻结，不再修改。
