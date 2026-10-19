# T178 / C194 独立本机验收：真实控制支撑、闭核及区域弱极限

- checked_sha / source_sha: `673bf04f87c065482b06bac35a2a97c971592dc2`
- mathematical_base: `d1134c0ccc8f343aef6223f304fe52f86a7aff1d`
- reviewed_at: `2026-10-19T14:38:03+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result / axiom_check: **PASS / PASS**；全部 **18/18** 显式声明通过，其中两个闭子空间定义、16 个定理。
- scope: **AUXILIARY**；C194 可登记 REVIEWED，原文覆盖保持 **17/26**。不提升完整控制收敛、连续 PDE 或终态零值命题。

## 固定版本和原文范围

直接读取固定 Git 对象中四模块的全部源码、18 项完整展开类型及证明，并核对 T178 分析、MATH_SPEC、C194/T178 台账和关键依赖。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE、工具链及 CI 协议与已读取的 T175 版本逐字节一致，继续执行独立语义验收流程。固定台账仍为 SPECIFIED/RUNNING，本报告提供该精确证明版本的独立验收，不把执行者自检或 CI 当成数学审查。

对照 `paper/main.tex:2290–2377` 的控制收敛段落：原 FD 对偶单元及 E_h、K_h=E_hB_h、半开时间单元上的 U_h,dt；ω₀⊂⊂ω_sharp⊂⊂ω 的活动节点限制；有界控制弱子列与任意弱聚点是区域控制零延拓的步骤。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。四模块没有声称已经证明原 `prop:control-convergence` 的连续方程、初终值或一致性。

签发前完整读取并核实已冻结的 [T177 正式报告](T177-local-acceptance.md)：checked SHA 正是本批基线，report commit=`923f74e8dc1e4b64967bdc10ba8248aa71dd96e9`，reviewed_at=`2026-10-19T14:32:42+00:00`，16/16 PASS；报告工作区字节与该提交完全相同。重新读取实际 TimeCellReconstruction、ReconstructedControlCompactness 和 HilbertWeakSubsequence，未仅引用报告结论。空间重构另依赖已冻结 [T175 报告](T175-local-acceptance.md)，报告提交 `8a921065b09fe7082c4ef5d1163e9925f3f98709`。后续 IsometricReconstructionProjection、FiniteCellApproximation 草稿及动态 `.ci` 不在范围。

## 全部 18 项声明逐项核对

顺序与固定 manifest、C194/T178 一致。源码位置相对于 `Carleman/`；raw 行指固定原始产物中实际完整类型的起始行。

| 序号 | 完整声明 | 固定源码 / raw 行 | 判定及实际内容 |
| --- | --- | --- | --- |
| 1 | `Carleman.cartesianDualCell_dist_le` | `Spatial/CartesianCellControlSupport.lean:15` / 34201 | PASS；真实单元点到实际内部节点的 Euclidean 距离≤d h。 |
| 2 | `Carleman.cartesianDualCell_subset_region` | 同文件:26 / 34209 | PASS；原紧包含条件内部产生网格统一 h0，整个活动单元包含于 ω。 |
| 3 | `Carleman.cartesianCellControl_zero_outside` | 同文件:42 / 34223 | PASS；同一实际 K_h 的指示和在 ω 外 a.e. 为零。 |
| 4 | `Carleman.cartesianCellControl_support_small_mesh` | 同文件:63 / 34233 | PASS；统一 h0 先于全部网格和控制。 |
| 5 | `Carleman.Physical.supportedRegionSpace` | `Control/SupportedRegionSpace.lean:12` / 34248 | PASS；真实补集限制 CLM 的核定义。 |
| 6 | `Carleman.Physical.supportedRegionSpace_closed` | 同文件:14 / 34251 | PASS；该真实核在原 L² 范数拓扑中闭。 |
| 7 | `Carleman.Physical.mem_supportedRegionSpace_iff` | 同文件:17 / 34254 | PASS；可测 ω 下核成员等价于原 a.e. 零支撑。 |
| 8 | `Carleman.Physical.zeroExtend_restrict_of_supported` | 同文件:31 / 34259 | PASS；实际区域限制再零延拓精确恢复原 L² 类。 |
| 9 | `Carleman.bochnerKernelSpace` | `Control/BochnerKernelSpace.lean:14` / 34263 | PASS；真实逐时 compLpL 算子的核。 |
| 10 | `Carleman.bochnerKernelSpace_closed` | 同文件:18 / 34273 | PASS；实际 Bochner 范数拓扑闭核。 |
| 11 | `Carleman.mem_bochnerKernelSpace_iff` | 同文件:22 / 34278 | PASS；核成员等价于 a.e. 逐时 L(u(t))=0。 |
| 12 | `Carleman.timeCellReconstruction_mem_bochnerKernel` | 同文件:34 / 34283 | PASS；真实时间指示重构保持每一步的核条件。 |
| 13 | `Carleman.exists_bochnerKernel_weak_subsequence` | 同文件:46 / 34290 | PASS；有界核内序列的完整弱子列、核内极限及同一成本界。 |
| 14 | `Carleman.bochnerKernel_of_weak_tendsto` | 同文件:57 / 34305 | PASS；任意给定完整弱极限仍在真实核中。 |
| 15 | `Carleman.cartesianTimeControl_supported` | `Control/SupportedTimeControl.lean:16` / 34313 | PASS；实际 FD 时间控制的 a.e. 空间支撑。 |
| 16 | `Carleman.cartesianTimeControl_supported_small_mesh` | 同文件:36 / 34323 | PASS；同一 h0 对所有 TimeGrid 与完整控制序列有效。 |
| 17 | `Carleman.supportedBochner_zeroExtension` | 同文件:50 / 34339 | PASS；真实区域 Bochner 控制恢复及精确范数等式。 |
| 18 | `Carleman.exists_regional_control_weak_subsequence` | 同文件:72 / 34346 | PASS；原有界有支撑序列的完整弱极限是该区域控制的真实零延拓。 |

## 活动单元的真实几何与统一阈值

第 1 项调用实际 `closedCoordinateBox_diameter_bound`，把 x 和原节点同时放入该对偶单元的闭盒。各坐标区间的真实长度是 δ_j≤h，δ_j>0，得到 **dist(x,x_a)≤d h**。底层闭盒界是先证明开盒 Euclidean 距离界，再以实际距离连续性延伸到闭包；不是由一个抽象“网格距离”替代原距离。

第 2 项直接使用 `IsCompact (closure ωsharp)`、`IsOpen ω` 和 `closure ωsharp⊆ω`。mathlib 的实际紧集厚化定理给 ε>0 及 `cthickening ε (closure ωsharp)⊆ω`，然后取 **h0=ε/(d+1)**。从 0<h≤h0 得 h(d+1)≤ε，结合前述 d h 界和节点属于 closure ωsharp，推出整个 D_a⊆ω。h0 先于 o、δ、N、h、节点、时间网格及控制；不依赖节点数、原周期 T、dt 或控制值。维数固定的 d+1 避免 d=0 除零，零维情形也成立。

原稿中紧包含活动区正好提供这些几何条件；证明不需要额外的 ω 边界正则性、边界零测或可选距离下界。ωsharp 不必额外声明非空或开放，故结果包含原文情况而且更广。输入 `∀j,δ_j≤h` 是真实步长上界，适用于原 h=max_j h_j；没有改成尚待证明的单元支撑假设。通用第 3 项保留 hcell，最终第 4、16 项已经在内部供给 hcell。

实际控制空间使用活动节点子类型 `CartesianPhysicalControl ... ωsharp`，B_h 是这些节点上的原物理零延拓，K_h 是同一 E_hB_h。展开 T175 的真实指示和时：活动节点的整个单元在 ω 内，故 ω 外指示项为零；非活动节点的 B_h 系数本身为零。这样得到真实原域限制测度下 a.e. 零值，而不是只检查控制节点中心。边界条带仍保留原零值；未填满原域，也未对任意 L² 代表声称逐点零。

## 支撑闭核与两层 a.e. 资格

`supportedRegionSpace ω` 精确等于 `(restrictRegionCLM ωᶜ).ker`。重新读取该 CLM 的构造：先把原 u 的 MemLp 沿限制测度缩小，再以同一函数取真实 Lp 类；线性由实际 a.e. 加法/数乘身份证明，连续性界为 1。核的闭性因而来自实际有界线性算子，未把目标支撑集合的闭性当输入。

第 7 项在 MeasurableSet ω 下使用 `ae_restrict_iff'`、真实限制代表公式和 `Lp.eq_zero_iff_ae_eq_zero`，双向得到 `u∈K ↔ ∀ᵐx, x∉ω→u(x)=0`。第 8 项再以实际零延拓的指示代表逐情况比较：ω 内为限制原 u，ω 外使用已证零值，得到 Lp 类的精确相等。整个过程只取可测性；空区域、零测度区域和非零测度边界均允许，没有把区域边界丢弃。

Bochner 核定义为 `(L.compLpL 2 μ).ker`。本次读取固定 mathlib `LpSpace/Basic.lean` 的定义与证明：compLp 是实际 Lipschitz 复合取得的 Lp 类，compLpL 用 ‖L‖ 的真实界装配成 CLM，并提供 a.e. `compLpL u(t)=L(u(t))`。因此第 11 项的逐时核条件与 Bochner Lp 类的核身份确实等价。

空间支撑和时间支撑明确是两层 a.e. 命题：对 μ-a.e. t，原空间 L² 类在 ν-a.e. 的 ω 外为零。没有为 Bochner L² 指定每个时刻的点值，也没有交换不可数个零测例外。最终恢复的是实际 `Lp (Lp ℝ 2 (ν.restrict ω)) 2 μ` 区域控制；本批没有另证明与乘积空间 L²(μ×ν|ω) 的显式等距等价，原文的 L² 时空表述在这里以真实 Bochner 空间实现。

## 实际时间重构与完整弱极限

第 12 项展开真实 `timeCellReconstruction` 的 a.e. 有限指示和，利用 L 的真实线性把 L 作用移入有限和，再以每一步 L(u_i)=0 消去。不是只在离散时间节点声明支撑。T177 的时间单元为实际 `(i dt,(i+1)dt]`，包含最终 T，重构属于 `Lp H 2 (volume.restrict (Ioc 0 T))`。有限时间 0 的端点差异仅为零测；没有周期 next 操作替换物理终点。

第 15 项取 L 为原空间补集限制 CLM，逐步由空间支撑转成核资格，再应用时间核定理；第 16 项沿用第 2 项的同一 h0。量词为先选 h0，然后所有空间网格、所有 TimeGrid、所有完整控制序列，未附加时间小步长条件。原时间控制的成本恒等式来自已验收 T177，本批支撑结果也不需要控制有界或满足离散 PDE。

第 13 项对真实完备 Hilbert H、一般 Hilbert G 和任意 μ，显式要求完整 Bochner L² 可分、u_n 每项 a.e. 入核及 **‖u_n‖≤C**。调用实际闭子空间弱抽取：闭核使子空间完备，Riesz 等距和弱对偶闭球序列紧性产生严格递增 φ 与同一核内 v；用子空间正交投影把测试扩展到**全部原 Bochner 空间**。输出保持原 C，不含网格或投影常数。C≥0 由任一 n 的范数界自动保证，C=0 合法。

可分性在通用任意测度定理中是显式 typeclass 前提，未被藏入一个目标结论。原 Euclidean Lebesgue 空间及实时间区间的限制测度具有可数生成 Borel 结构和 SFinite；固定 mathlib 的 `Lp.SecondCountableTopology` 在有限 p=2 下逐层供应所需 Bochner 可分性。抽取结果不声称对任意不可分 Lp 直接适用，也不自行产生原 HUM 控制或统一成本界。

第 14 项更强地处理**任意已经给定的完整弱收敛序列**，不依赖第 13 项选中的子列，不需要可分性或另加成本界。对任意目标空间测试 z，经真实 `(L.compLpL).adjoint z` 把弱收敛传到映像；所有映像恒零，极限唯一性给所有 `inner(Lv,z)=0`，内积唯一性得到 Lv=0。H、G 完备是实际 Hilbert 伴随的合法条件，最终空间限制实例满足它们。没有把范数闭性直接误当作无需证明的弱闭性。

## 区域恢复、成本和结论边界

第 17 项实际选择 `v=(restrictRegionCLM ω).compLp u`。对 μ-a.e. t，利用真实 `restrictRegion_adjoint` 把伴随识别为 `zeroExtendLp`，再调用第 8 项，证明其逐时零延拓构成的 Bochner Lp 类**严格等于原 u**。范数证明用零延拓实际空间等距，逐时取得范数相等后通过 eLpNorm 的 a.e. 范数同一性积分；不是只得到收缩或一个任意同范数向量。无边界光滑、有限域测度或代表正则性前提。

第 18 项首先在补集限制的 Bochner 核内抽取 v0，再以上述实际限制构造 v。结论量化每个完整环境 Bochner 测试 z，原 u_(φn) 弱收敛到**这个 v 的真实零延拓**，且 ‖v‖=‖v0‖≤C。结合第 14、17 项，任意完整弱聚点也可如此恢复，不限于存在性定理产生的某个特殊极限。

本批最后的通用抽取定理仍明确以已给的统一成本、各项支撑和公共 Bochner 空间为输入。空间细化序列的域/周期识别、截去有限个不满足 h≤h0 的前项、受限活动区控制的存在性及原成本供应，需要在完整控制收敛组合中接入；本批没有一个宣称已经完成这些全部组合的具体 wrapper。尤其未证明状态紧性、数据/势强一致性、连续弱方程、初值或终态 y(T)=0。上述边界与 AUXILIARY 规格一致，无新增光滑数据限制或未声明的目标估计前提。

## 固定依赖、公理和构建

递归读取四模块的实际 Carleman 导入共 **335** 个模块，其中 **331** 个既有模块与 mathematical_base 逐字节不变。关键接受版本另行比较完整闭包，均无变化：

| 依赖入口 | 固定接受版本 | 闭包模块数 |
| --- | --- | --- |
| ReconstructedControlCompactness / T177 | `d1134c0ccc8f343aef6223f304fe52f86a7aff1d` | 25 |
| CartesianCellReconstruction / T175 | `7c2ceacf62d42b168879106b8c6d6fc246c45794` | 326 |
| ObservedRegionLp / T030 | `31d5e165a595849bc1c882523838aad69576b594` | 53 |
| HilbertWeakSubsequence / T129 | `bee8a93d0856f84c9280d10a19f50da7da2a362f` | 1 |

固定 `Carleman.lean` 导入四模块，18 项都实际执行 `#check @...` 与 `#print axioms ...`。新源码无 sorry、admit、axiom 或 native_decide。18 项各仅依赖 `propext, Classical.choice, Quot.sound`。独立解析完整 raw 的 **3176** 条显式记录（**3172** 个不同名字，含 9 条无公理记录），白名单外依赖为零；真实末行对所有 Carleman 常量的递归 collectAxioms 审计确认 **8284 项 PASS**。

实际读取最终 `/tmp/carleman-t178-cell-support-target3.log`：**3518 jobs**；`/tmp/carleman-t178-supported-spaces-target.log`：**3100 jobs**；`/tmp/carleman-t178-supported-time-target4.log`：**3534 jobs**；固定 `-build.log`：根目标 **4122 jobs**，均成功。早期失败草稿日志未被算作最终成功证据。`-axioms.log` 是零字节 stderr，审计结论以完整 raw 为准。

Lean pin v4.35.0，正式 CI compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 和本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿、工具链、manifest、lean/dashboard workflow 和 `tools/lean_ci.sh` 与 T175 已验版本逐字节相同。实际新用的紧集厚化、compLp/compLpL 和 Lp 可分性均从此固定 mathlib 版本核对。

## 独立同 SHA CI 与原始工件

本 Agent 自行访问 GitHub run/jobs/artifacts API，并独立执行两次 `gh run download`，均 exit 0；没有用 root 的副本代替独立下载。曾见 lean 运行及 dashboard 排队，待实际三项最终成功后才签发。

- run: [39270090962 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39270090962/attempts/1)，event=push、branch=main、head_sha 精确等于本报告 SHA；最终 completed/success，updated_at=`2026-10-19T14:37:51Z`。
- state-check job **118119792902**：completed/success，完成于 `2026-10-19T14:34:05Z`。
- lean job **118119793466**：completed/success，完成于 `2026-10-19T14:37:39Z`。
- dashboard / snapshot job **118121753557**：completed/success，完成于 `2026-10-19T14:37:50Z`。
- `lean-ci-result` artifact **12194283134**，ZIP **492 bytes**；API digest `sha256:1d3b910e76b476e0eb3f8f59c336466c8b2d1b92e6392e8e6285b331793b0a1a`。
- `lean-declaration-evidence` artifact **12195087069**，ZIP **243137 bytes**；API digest `sha256:cf0f575e075f1652d75e2606c40a9535df681bad7d6f4e2fa2d939d7d4c02e5d`。

两工件 workflow_run 均绑定同一精确 SHA、main 和 run。独立 result `/tmp/carleman-t178-supported-controls-main-ci/result.json` 为 **537 bytes**，SHA256 `89c65931755ab9288d9d1bc25b6fa5ae610112205825795f69038a6bb2df2cda`；实际 status=PASS、checked_sha=source_head_sha=`673bf04f87c065482b06bac35a2a97c971592dc2`、targets=[Carleman]、finished_at=`2026-10-19T14:36:29.125809+00:00`，ci_url/Lean/mathlib 与上述实际记录一致。

独立 raw `/tmp/carleman-t178-supported-controls-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t178-supported-controls-local-axioms.txt` **逐字节完全一致**，均为 **2630488 bytes**，SHA256 **`dca985cdb86ef3ca473350c9e0f9c5f07591201fb546bc6ee9a2e1ae2cab33c4`**。ZIP digest 与解包 raw digest 分别记录；完整类型、公理和最后 8284 项成功记录均实际核对。

## 最终结论

**18/18 PASS，未发现阻断缺陷。** 原紧包含活动区给整个对偶单元的真实支撑和统一阈值；实际空间及时间控制在 ω 外 a.e. 为零。支撑是原限制 CLM/逐时 compLpL 的真实闭核，任意完整弱极限保留该核；真实区域限制与零延拓恢复 Bochner 控制并保持范数，在显式统一成本与支撑输入下给严格递增的完整弱子列。C194 可登记 **AUXILIARY/REVIEWED**，覆盖保持 **17/26**。本报告仅单文件提交，不 push，不改实现、原稿或台账；通知后正文及 reviewed_at 冻结。
