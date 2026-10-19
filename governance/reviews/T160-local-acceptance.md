# T160 / C176 独立本机验收

- `checked_sha`: `d5a8ab859e4413c6eb950702df73990e356c3786`
- `base_commit`: `5923dbf398166a48ddf42f98585ff54a10545b0f`
- `reviewed_at`: `2026-10-19T11:56:26+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：任意正维正坐标盒的原 Dirichlet 算子图状态，由全空间紧支 C∞、原全部边界严格零值的函数及其实际负 Laplacian 作图拓扑逼近。**P024 / prop:continuousCE 不提升，原文覆盖保持17/26。**

本 Agent 独立读取固定 Git 对象四模块全部证明、10项完整展开类型、原 `paper/main.tex:2659–2676,2696–2704,2730`、T160 分析、MATH_SPEC、C176/T160 清单及关键依赖。AGENTS、PROJECT_OPERATIONS、state/README 与此前已读协议逐字节相同。正式 CI 由本 Agent 自行查询，原始 result/raw 自行下载并逐字节核验；执行者说明、历史验收和 CI 不替代实际数学核查。未来 HarmonicGraphContinuity、HarmonicStateDensity、DirichletSmoothTimeCore、BoxSmoothTimeDensity 草稿及动态 `.ci/axioms.txt` 排除。

## 原稿对应与范围

原2659–2664行的盒域实现采用 V=H¹₀(Ω)、a(v,w)=∫∇v·∇w，D(A)=H²(Ω)∩H¹₀(Ω)，A=−Δ。原连续 CE 的证明先取光滑周期状态，再在2730行以密度推广至完整弱周期轨道。本批完成这一过程的**空间算子图密度**，并未输出周期时间逼近或完整弱 CE。

最终定理量词是 ∀d>0、∀a,b:Fin d→ℝ、∀i,a_i<b_i，令 B 为同一原盒真实 Dirichlet 形式的模型，再 ∀z∈B.operatorGraph，∃U_n∈SpatialTest univ 和 Z_n∈B.operatorGraph。全部 U_n 在整个 frontier Ω 上逐点为零，Z_n 的值、算子投影分别等于 U_n 的原域 L² 类和实际负 Laplacian L² 类，且 Z_n→z 于实际图拓扑。没有长宽比、侧长下界、光滑原状态、原状态连续代表或额外算子域前提。序列可依赖盒与 z；不声称同一线性近似算子对所有状态统一工作或提供定量收敛率。

输出是 **SpatialTest univ** 加原 frontier 零值，不是 C_c∞(Ω)。这一区别保证没有额外要求法向导数为零或函数在边界邻域消失；所需近似类覆盖原 H²∩H¹₀ 的正常边界行为。一般凸域上的光滑函数入域辅助定理不等于一般多面体图密度，最终完整密度仍限原正坐标盒。

## 全部 10 项公开声明

名称省略 `Carleman.`，源位置相对于 Carleman。源行来自固定提交，完整类型行来自与固定本机副本逐字节相同的独立下载 raw；与交付 manifest、固定 C176 和 T160 顺序完全一致。

| # | 声明 | 固定源位置 / 完整类型行 | 独立结论 |
|---|---|---|---|
| 1 | `coordinateDerivative_eqOn_of_eqOn` | `Spatial/BoxCompactSmoothDensity.lean:13` / 31569 | PASS；开集内函数相等给每点邻域相等，真实 iteratedFDeriv 的局部唯一性保持任意阶坐标收缩。 |
| 2 | `exists_box_dirichlet_compact_h2_approximation` | `Spatial/BoxCompactSmoothDensity.lean:20` / 31575 | PASS；对全部原弱 H² 且一阶截断在 H¹₀ 的状态，构造同一真正 SpatialTest 序列，全边界零，值及全部一、二阶分量强收敛。 |
| 3 | `lp_tendsto_of_representative_L2_error` | `Spatial/SmoothLaplacianL2Limit.lean:14` / 31607 | PASS；任意测度下，实际 Lp 类的 a.e. 代表误差范数趋零给真实 Lp 拓扑收敛。 |
| 4 | `coordinateDerivative_two_diagonal` | `Spatial/SmoothLaplacianL2Limit.lean:31` / 31613 | PASS；真实二阶张量对同一标准基方向的收缩等于连续线性微分的两次实际方向导数。 |
| 5 | `SpatialTest.laplacianOnLp` | `Spatial/SmoothLaplacianL2Limit.lean:47` / 31620 | PASS；定义为实际光滑二阶导数的原域 Lp 有限和，不是任意载荷。 |
| 6 | `SpatialTest.laplacianOnLp_ae` | `Spatial/SmoothLaplacianL2Limit.lean:52` / 31624 | PASS；有限个 Lp 代表身份合并后精确等于实际 classical spatialLaplacian。 |
| 7 | `SpatialTest.laplacianOnLp_tendsto` | `Spatial/SmoothLaplacianL2Limit.lean:66` / 31628 | PASS；选全部 Hessian 收敛中的对角分量，有限 Lp 求和再取负，极限恰为原 negativeLaplacian。 |
| 8 | `SpatialTest.laplacianOnLp_eq_subdomain` | `Spatial/SmoothDirichletGraph.lean:13` / 31639 | PASS；真实受限测度下的 Laplacian 类等于全空间 Laplacian 类的实际限制。 |
| 9 | `SpatialTest.exists_dirichlet_domain_of_boundary` | `Spatial/SmoothDirichletGraph.lean:20` / 31642 | PASS；正维有界非空凸开域内，实际全边界零的光滑紧支函数内部取得原 H¹₀ 资格及弱 Poisson 身份，从而进入真实算子域，算子值严格为−Δ。 |
| 10 | `exists_box_smooth_operator_graph_approximation` | `Spatial/BoxSmoothGraphDensity.lean:15` / 31652 | PASS；任意原图元素内部取得同一状态的弱 H² jet，构造 U_n/Z_n，并证明两个原 L² 图投影共同收敛。 |

## 同一全边界零序列与真实导数

已重读已验收 `exists_box_dirichlet_smooth_h2_approximation` 的实际组合：原弱 H² 状态的一阶截断与真实 negativeLaplacian 进入已证盒弱 Poisson 延拓；在扩大盒内取得 H² jet，限制回原盒后由弱 jet 的值单射证明就是原 u。局部全偶核的实际平滑、全部弱一二阶分量收敛以及整个原边界的最终零值共同使用同一 F_n，最后只丢弃一个统一有限前缀。当前入口没有另要求原 u 光滑或域外 H² 零延拓。

本批取原盒紧闭包 K=closure Ω，在全空间内由实际光滑截断存在定理构造 η∈SpatialTest univ，η=1于 K；η 仅选一次。U_n=ηF_n 的结构由真实 mulSmooth 给 C∞ 和紧支，值在整个开盒精确等于 F_n。对每个开盒点，开性使这种相等在邻域成立，`EventuallyEq.iteratedFDeriv` 保持真实迭代 Fréchet 微分，再经同一个 coordinateTensorEval 得所有坐标导数相等。不存在遗漏的截断导数余项。

受限测度 a.e. 点确在原开盒内，因此值、全部一阶与全部有序二阶分量的原 L² 误差与 F_n 完全相同。二阶目标为 derivativeComponent(v₁::v₀::nil)(field₂ u)，与原实际弱 Hessian 分量一致；不是输入一组任意梯度/Hessian 数组。frontier 上 U_n=ηF_n=0，由原逐点边界零值立即得到，包含边、角等全部边界点，无 a.e. 边界例外或只在面内部成立的缩减。该 H² 辅助入口也容许 d=0；最终原算子入口明确 d>0，与原论文空间维数一致。

## 原 L² 类、实际 Laplacian 与负号

`lp_tendsto_of_representative_L2_error` 先将实际 ‖u_n−v‖ 等于其代表差的 Bochner L² 范数，再使用 Lp.coeFn_sub 和所给 a.e. 身份。它不把 a.e. 身份升级为处处相等；F_n 的可测及有限范数性质由它与真实 Lp 类 a.e. 相同保证，不能用无穷 eLpNorm 的 toReal 默认值伪造收敛。

`laplacianOnLp` 对每个标准基 e_i 先取真正 derivativeTest，再取其 derivativeLp，最后在 **volume.restrict S** 上求和。已核对 derivativeTest/derivativeLp 的真实 Fréchet 导数代表和紧支 L² 资格。`coordinateDerivative_two_diagonal` 使用 iteratedFDeriv_two_apply 与真实 CLM 求值微分恒等式；在常基向量处额外导数项确为零，无遗漏项或 Sym 重数因子。

每个对角项的实际 Lp 收敛由第3项取得；有限和保持收敛，再整体取负。原 negativeLaplacian 的定义正是 −Σ_i derivativeComponent(i::i::nil)(field₂ u)，因此输出同时保留原阶数、对角求和与负号。一般第7项对任意集合 S 的受限测度成立，不暗加区域边界正则性；最终实例使用开盒。该步骤只从已证全部分量收敛选取对角项，没有将原H²假设换成外部给定 Laplacian 收敛。

## 从边界零值进入原形式算子域

实际 `boundedDirichletOriginalForm` 的 V 为原 dirichletSubspace，形式为全弱梯度的 L² 内积，未加入零阶质量项。已重读 `dirichlet_operator_graph_iff`：它将实际形式关联算子图等同于原 H¹₀ jet 与对全部 SpatialTest S 的弱负 Laplacian 方程，并用真实定义闭包扩展到全部能量测试，不预设原函数已在算子域。

对全局光滑紧支 φ、原 frontier 零值，`smooth_boundary_test_mem_dirichletJetSpace` 内部通过真实零边界指示函数、Lipschitz jet 及 H¹₀ 定义闭包取得域内 H¹₀ 资格。此处正维、有界、非空、凸、开都是该一般辅助结论的明确几何条件，最终盒实例从 a_i<b_i 内部供应，没有额外对原状态的限制。

随后给**已光滑的 φ 本身**构造全空间实际 H² jet，使用弱 negativeLaplacian 身份并限制到 S。已核对弱 Poisson 限制证明只迁移原紧支测试与真实载荷，未假定跨边界 Green 恒等式。`laplacianOnLp_eq_subdomain` 由两个实际 a.e. Laplacian 代表及 subdomainLp 代表身份确认，限制映射的线性性保持负号。最终原图等价输出 z∈D(A)、z=φ|_S、Az=−Δφ|_S；域资格和算子身份均是结论，不是输入。

## 全原图元素与真正图拓扑

已核对 operatorGraph 定义为 {(x,Ax):x∈D(A)} 在 H×H 中的实际线性图；graphH、graphA 是两个实际连续投影，graphDomain 从图成员取得原域元素，graphOfDomain 正是对应配对。其子类型拓扑就是空间算子图拓扑，等价于通常的图范数收敛，并未替换为只有 H 值的拓扑。

任意 z∈B.operatorGraph 先由真实盒正则性 `box_dirichlet_domain_le_h2` 得 u，且 value u=graphH z。原形式的 domain_le 给同一值属于原 H¹₀，`mem_dirichletJetSpace_iff` 将这一资格传给 u 的一阶截断。原 H² 域元素与 graphDomain z 通过同一 Lp 值作 Subtype.ext 相等，进而得到 **negativeLaplacian u=graphA z**。这一步防止把另一载荷或另一状态的 H² 逼近拼接进来。

对同一 U_n，由已证明的边界入域定理选择 z_n，再置 Z_n=graphOfDomain z_n。值收敛是 U_n 的原域 Lp 类趋于 graphH z；算子收敛是−laplacianOnLp U_n 趋于 graphA z。最后在 H×H 中取乘积极限，并用 tendsto_subtype_rng 返回真实图子类型极限。两个投影使用同一 n、同一 U_n、同一 z_n，没有分离子列或仅宣称集合稠密。没有对任意原 z 新增 H²、光滑性、边界连续性或选取某个预先光滑核子空间的限制。

## 固定依赖、公理及构建

四模块公开声明数2+5+2+1=10，全部由固定 Carleman.lean 导入并在固定 CheckAxioms 中打印完整类型及公理；无漏列的新公开或私有辅助声明。新源码无 sorry、admit、新数学 axiom 或 native_decide。

实际 Carleman import 闭包共 **276** 模块，其中 **272** 个旧模块与基线逐字节相同。关键接受版本的整个闭包分别核对：BoxDirichletSmoothDensity 的253模块与 C175 基线相同；BoxDirichletRegularity 的224模块与 C157 `b818f314b275265490aa9b797779f7db0005ddb9` 相同；DirichletDistribution 的57模块与 C057 `3d5aa9cec281974bef7da9d37ffa11a8f9f75670` 相同；SmoothBoundaryDirichlet 的118模块与 C154 `d1dca8884990c684f923a4938e40a6cc88e1645f` 相同；InteriorSmoothCutoff 的26模块与 C150 `3d418d76a4959a094dcd26d2d157c213f297531d` 相同；RegularTimeCore 的53模块与已验收 Section3 版本 `a315bdc449c58a705a982f0d009f1dde24d6af66` 相同。关键实际证明均已重读，不以这些旧报告替代语义检查。版本追溯见 [T159](T159-local-acceptance.md)、[T141](T141-local-acceptance.md)、[T041](T041-local-acceptance.md)、[T138](T138-local-acceptance.md)、[T134](T134-local-acceptance.md)、[T019](T019-local-acceptance.md)。未使用后续时空密度或完整 CE，依赖不存在目标循环。

Lean pin为4.35.0；mathlib pin与本机实际HEAD均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，依赖工作树干净。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。实际读取 `/tmp/carleman-t160-box-graph-density-target3.log` 的3464 jobs成功，`/tmp/carleman-t160-box-graph-density-build.log` 的4058 jobs成功；`-axioms.log` 是空 stderr，未将它当作PASS证据。

实际审计主体按 privateToUserName 遍历所有 Carleman 环境常量，递归 collectAxioms，仅容许 propext、Classical.choice、Quot.sound。固定 raw 末行实报 **7713** 项递归PASS；另扫描2936条非空公理打印及9条无公理打印，无其他公理，未将打印数混同全量递归数。10项本批声明均有实际完整类型及上述三项正常基础公理。CI、构建脚本、工具链和 mathlib 配置与此前已核版本相同。

## 独立正式 CI 与原始工件

本 Agent 实际查询 [main CI run 39247555446 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39247555446/attempts/1)：event=push、head_branch=main、head_sha=`d5a8ab859e4413c6eb950702df73990e356c3786`，顶层 completed/success，updated_at=`2026-10-19T11:55:15Z`。最终三项 job 均 completed/success：

| job | 实际 ID | 最终结果 |
|---|---:|---|
| state-check | 118043086406 | success |
| lean | 118043086726 | success |
| dashboard / snapshot | 118044906243 | success |

本 Agent 从同 run 自行 gh run download 两份原始工件，两下载进程 exit 0；实际 artifact 元数据均绑定同 SHA：

| 工件 | 实际 artifact ID | 归档 bytes | 归档 SHA256 |
|---|---:|---:|---|
| lean-ci-result | 12183947870 | 493 | `09e14e1375409e5a60e9651ae4926bda07a2852dd256326dd99546e8a401e175` |
| lean-declaration-evidence | 12183922812 | 224616 | `582ec8567832e52d282aa5f10f01d3e7cf25d09417eab0976e0b1b1b18957cd3` |

实际读取 `/tmp/carleman-t160-box-graph-density-main-ci/result.json`：status=PASS，checked_sha 与 source_head_sha 均等于本报告固定 SHA，ci_url 为同 run/attempt，finished_at=`2026-10-19T11:53:52.921677+00:00`，targets=[Carleman]；Linux Lean4.35.0 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 与上述 pin 一致。

实际下载 `/tmp/carleman-t160-box-graph-density-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t160-box-graph-density-local-axioms.txt` **逐字节相同**，均 **2416329 bytes**，原始 SHA256 **`c94678abd8b1aafea6f4d9a21cd3c4bb5ffc571a083007306ef45f40153d6c3f`**。原始文件 hash 与 ZIP 归档 hash 分开记录；远端 raw 含全部10项完整类型及7713项递归公理 PASS。

## 签发结论

**T160 / C176 可在该固定版本登记 REVIEWED，scope 保持 AUXILIARY。** 10项声明的语义、公理和实际同版本证据均 PASS，未发现需修复缺陷。范围严格限原盒空间算子图密度；完整周期时空密度及弱 CE、一般多面体仍未完成，P024不提升，原文覆盖保持17/26。签发后冻结正文及 reviewed_at，仅单独提交本报告，不改数学、台账、root/audit 或原稿，不推送。
