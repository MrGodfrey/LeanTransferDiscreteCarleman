# T177 / C193 独立本机验收：真实时间控制重构、配对与弱子列

- checked_sha / source_sha: `d1134c0ccc8f343aef6223f304fe52f86a7aff1d`
- mathematical_base: `ef4e3f83320e3a2d4cc7a074a1df996c13bd9d52`
- reviewed_at: `2026-10-19T14:32:42+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_foundations`
- result / axiom_check: **PASS / PASS**；全部 **16/16** 显式声明通过。
- scope: **AUXILIARY**；C193 可登记 REVIEWED，原文覆盖保持 **17/26**。本批完成实际 Bochner 时间重构、原物理配对及有界控制的弱子列基础，不据此宣布整条控制收敛、终端零值或极限 PDE。

## 固定版本、原文与既有验收

从固定 Git 对象读取三个新模块的全部证明、固定 raw 中 16 项完整展开类型、T177 分析、MATH_SPEC 和 C145/C192/C193 台账，并核对关键旧依赖。原文实际读取 `paper/main.tex` 2290–2377 行：FD 的单元常数 E_h、FE 的实际包含、控制 K_h、eq:conv-pairings、后向 Euler 时间重构与控制收敛准备。另沿用已核对的原物理方程及控制时间范数。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 与已读 T174 版本相同；本次重新读取前三份规则。排除后来工作树中的支撑/Bochner 核空间等模块、未提交根导入与动态 `.ci/axioms.txt`。本报告不改变数学实现、原稿和唯一台账。

签发前已完整读取 [T176 冻结报告](T176-local-acceptance.md)，报告提交 **`47fcf88f7bc34bebea05f6ae285efc85aeaeef2b`**，reviewed_at=`2026-10-19T14:24:10+00:00`，25/25 PASS；其 checked SHA 正是本批 mathematical_base。固定 T177 台账中的旧待验收状态不被误读成已审查，该固定正式报告补齐依赖验收门槛。另直接复核 TimeCellAverage、TimeGrid、HilbertWeakSubsequence、CartesianCellReconstruction、ObservedRegionLp 及相关实际接口，而非仅接受报告结论。

## 全部声明逐项核对

顺序与固定 manifest 一致。源码位置相对于 `Carleman/Control/`；raw 行为固定完整声明类型的起始行。

| 序号 | 完整声明 | 固定源码 | raw 行 | 判定 |
| --- | --- | --- | --- | --- |
| 1 | `Carleman.TimeGrid.physicalTimeCell_disjoint` | `TimeCellReconstruction.lean:15` | 34093 | 真实半开时间单元两两不交，包含相邻端点处理；PASS。 |
| 2 | `Carleman.TimeGrid.physicalTimeCell_restrict_volume` | `TimeCellReconstruction.lean:31` | 34096 | 限制到 (0,T] 后实际单元 Lebesgue 质量恰为 dt；PASS。 |
| 3 | `Carleman.timeCellReconstruction` | `TimeCellReconstruction.lean:42` | 34099 | 实际 indicatorConstLp 有限和，值域为原 Bochner L²；定义忠实性 PASS。 |
| 4 | `Carleman.timeCellReconstruction_ae` | `TimeCellReconstruction.lean:47` | 34104 | 原 Lp 类与逐单元指示函数和 a.e. 一致；PASS。 |
| 5 | `Carleman.timeCellReconstruction_inner` | `TimeCellReconstruction.lean:60` | 34109 | 真实积分内积精确等于 dt Σ 内积；PASS。 |
| 6 | `Carleman.timeCellReconstruction_norm` | `TimeCellReconstruction.lean:76` | 34113 | 原控制范数 sqrt(dt Σ‖u_i‖²) 精确保持；PASS。 |
| 7 | `Carleman.timeCellReconstruction_on_cell` | `TimeCellReconstruction.lean:84` | 34117 | 每个真实单元限制测度下 a.e. 等于原该步控制；PASS。 |
| 8 | `Carleman.reconstructedControl` | `ReconstructedControlCompactness.lean:16` | 34121 | g.period=T 后进入同一实际 L²(0,T;H)，重构为 K u_i；定义忠实性 PASS。 |
| 9 | `Carleman.reconstructedControl_norm` | `ReconstructedControlCompactness.lean:20` | 34133 | 显式保范数 K 下保持同一原物理控制成本；PASS。 |
| 10 | `Carleman.reconstructedControl_on_cell` | `ReconstructedControlCompactness.lean:29` | 34139 | 固定公共时域后的真实逐单元 a.e. 身份；PASS。 |
| 11 | `Carleman.reconstructed_controls_weak_subsequence` | `ReconstructedControlCompactness.lean:35` | 34145 | 原实际控制序列、严格递增子列、全部 Bochner L² 测试与极限成本；PASS。 |
| 12 | `Carleman.Physical.conformingTimeControl_norm` | `RealizedTimeControl.lean:18` | 34160 | FE 区域零延拓的实际时间控制范数恒等式；PASS。 |
| 13 | `Carleman.Physical.conformingTimeControl_on_cell` | `RealizedTimeControl.lean:24` | 34168 | 原 L²(ω) 控制在每个时间单元真实零延拓；PASS。 |
| 14 | `Carleman.Physical.conformingTimeControl_pairing` | `RealizedTimeControl.lean:30` | 34177 | 同一原 FE B* 的真实时间积分配对；PASS。 |
| 15 | `Carleman.cartesianTimeControl_norm` | `RealizedTimeControl.lean:45` | 34186 | 原 FD E_h B_h 时间重构保留实际对角质量成本；PASS。 |
| 16 | `Carleman.cartesianTimeControl_pairing` | `RealizedTimeControl.lean:51` | 34192 | 原 E_h 状态、E_h B_h 控制和物理 B_h* 的精确配对；PASS。 |

## 真实时间单元、可积性和尺度

TimeGrid 的 steps 为正整数、dt>0，period=steps*dt；`physicalTimeCell i=Ioc(i*dt,(i+1)*dt)`。相邻单元的公共端点属于左侧单元而不属于右侧单元，故真正不交；最后一个单元右端为 T，未使用周期序列 next 将终点替换成 0。N=1 同样成立。各单元包含于 (0,T]，限制测度不会改变其体积，真实质量为 dt。时间 0 的遗漏是零 Lebesgue 测度端点。这里核对的是定义和已证不交/体积/单元身份，不把未单独声明的全单元并集等式另算一项成果。

定义使用 mathlib 的 `indicatorConstLp 2`，有限单元测度在内部供应 MemLp；有限和因此确为 Bochner L² 元素。没有把任意点函数强行看成 Lp 类。第 4、7、10、13 项的点态表述均明确是相应限制测度下 a.e. 身份，不为 Lp 等价类赋予不合法的指定时刻值。

第 5 项实际展开双重有限和，应用 `L2.inner_indicatorConstLp_indicatorConstLp`：第 i、j 项的积分为 μ(cell_i∩cell_j) 乘原 H 内积。对角交集质量 dt，非对角为空，得到精确 `dt*Σ inner(u_i,v_i)`。第 6 项令 v=u，再用非负平方根得到 **sqrt(dt Σ‖u_i‖²)**；没有 T、节点数或额外归一化因子。第 7 项将全时域 a.e. 身份沿 `physicalTimeCell_restrict_le` 正确限制到单元，再以真实不交性消去其他求和项。

## 公共 Bochner 空间与完整弱子列

第 8 项以实际等式 hT:g.period=T 传输同一时间重构，故不同 g_j 的输出都在字面相同的 `Lp H 2 (volume.restrict (Ioc 0 T))` 中。它不是分别落在不同空间后只比较数字范数；各 K_j 可以有不同原控制空间 V_j，但都进入同一 H。

第 11 项的完整输入是：H 为实完备可分 Hilbert 空间；各 V_j 为实内积空间；每个 g_j.period=T；真实 CLM K_j 满足 **∀v, ‖K_j v‖=‖v‖**；输入为所有原 u_j；并显式给出统一 **controlNorm(dt_j,u_j)≤C**。没有隐藏已收敛子列、指定极限或 PDE 解假设。输出是实际上述重构的严格递增子列 φ、同空间 v、‖v‖≤C，以及对 **每个 z∈该完整 Bochner L²** 的内积收敛。

证明先用精确范数等式取得真正有界的 Hilbert 序列，再调用已验收 `exists_hilbert_weak_subsequence`。该依赖实际通过 Riesz 等距同构到对偶、弱星闭球序列紧性、逆 Riesz 构造 v，并由对偶逐测试收敛恢复所有内积；不是假设弱紧性结论或只检查可数精选测试。实 Hilbert 的全部连续线性测试亦由 Riesz 表示覆盖。

本次直接核对 mathlib 的有限 p 可分 Lp 实例与弱对偶闭球序列紧性：实轴 Borel 可数生成、时间限制测度 SFinite，配 H 可分和明确 Fact(2≠∞) 得该 Bochner 空间可分；H 完备给完整 L² Hilbert 空间。没有要求 V_j 有限维或完备。C≥0 不另假设，由原有界序列在任一 j 的范数界自动保证；C=0 允许。T>0 也由任一 g_j.period=T 保证。

该基础定理不要求 dt_j→0，这对有界序列弱紧性是合法的更广结论；它没有因此完成原控制收敛中需要的离散方程一致性。成本常数 C 是明确输入，本批不会自行产生原 HUM 控制或其统一估计。重构及配对常数恰为 1，弱子列保留同一 C；没有网格相关有限维自动连续性常数进入成本。

## FE 与 FD 的实际空间控制对象

FE 的 H=Lp ℝ 2 ν、U=Lp ℝ 2 (ν.restrict ω)，实际 K 使用 `(restrictRegionCLM ω).adjoint`。重新读取 ObservedRegionLp 的真实积分配对证明后，MeasurableSet ω 给该伴随恰为 `zeroExtendLp hω`，并且范数精确保持。因此 K 是原区域零延拓，**不是** Π_X 零延拓这一状态控制算子 B；原 FE 控制空间仍可无限维。

FE 配对对完整 `X : Submodule ℝ (Lp ℝ 2 ν)`（仅要求 CompleteSpace X）及所有 z_i∈X 成立：原状态采用实际包含 E_h；时间积分为 `dt Σ⟨u_i,(conformingRegionControl X ω)*z_i⟩`。证明使用同一 Hilbert 伴随的精确代数身份。该配对定理自身不需要 hω；MeasurableSet ω 只在把 K 明确识别为真实零延拓以及保范数时使用。原可测/开观察区域当然满足要求。

FD 的 `cartesianCellIsometry` 是既有真实有限双单元指示函数重构 E_h，其对角物理质量由实际单元体积 ∏δ_r 给出。`cartesianCellControl=E_h ∘ cartesianPhysicalControlExtension`，即同一原 **E_h B_h**。故第 15 项保范数来自实际空间等距；第 16 项以 E_h z_i 为状态测试，精确输出原物理 B_h* 配对。没有把这里的 E_h 偷换成刚度分析所用的分片线性 R_h。

原全部节点状态和区域节点控制均量化，允许空内部索引和 d=0 的相应退化有限模型；未要求节点数据已来自连续函数。不同空间网格的实际域若识别为固定 Ω，可应用通用公共空间定理；本批没有另给一个已完成所有固定域与细化条件的具体 FE/FD 控制收敛 wrapper。尤其 FD 的被选节点单元未在这里证明整个包含于 ω，也未在这里证明弱极限支撑于 ω；这些都是后续工作，而非本批隐含结论。

## 固定依赖、公理和构建

递归解析三个新模块的 Carleman 导入共 **333** 个模块，其中 **330** 个既有模块与 mathematical_base 逐字节一致。关键已验收入口的完整闭包另行比较，全部无变化：

| 入口 / 已接受阶段 | 固定接受版本 | 闭包模块数 |
| --- | --- | --- |
| TimeCellAverage / T176 | `ef4e3f83320e3a2d4cc7a074a1df996c13bd9d52` | 18 |
| CartesianCellReconstruction / T175 | `7c2ceacf62d42b168879106b8c6d6fc246c45794` | 326 |
| HilbertWeakSubsequence / T129 | `bee8a93d0856f84c9280d10a19f50da7da2a362f` | 1 |
| ConformingRegionControl / T030 | `31d5e165a595849bc1c882523838aad69576b594` | 54 |

固定根目标导入全部三个模块，16 项名字均实际执行完整 `#check @...` 和 `#print axioms ...`。新源码无 sorry/admit/新 axiom/native_decide。独立解析固定 raw 中 **3158** 条公理记录（3154 个不同名字、9 条无公理记录），白名单外依赖为零；正常依赖只有 `propext, Classical.choice, Quot.sound`。完整递归审计实际末行确认 **8254 项 Carleman 声明全部通过**，不是仅把16项局部输出当作全库审计。

实际读取 `/tmp/carleman-t177-time-reconstruction-target2.log` 的 **3009 jobs**、`/tmp/carleman-t177-realized-time-target2.log` 的 **3532 jobs**，以及固定前缀 `-build.log` 根构建 **4118 jobs** 全部成功。`-axioms.log` 是零字节 stderr，结论取自完整 raw 的真实审计末行。

Lean pin 为 v4.35.0，正式 CI compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 和本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、CI workflow 与 lean_ci.sh 和已审 T174 相同。实际新用的 mathlib L² 指示函数内积、Lp 可分性和 WeakDual 序列紧性均从该固定版本读取。

## 独立同 SHA CI 与原始工件

本 Agent 自行查询实际 GitHub API，并分别执行两次 `gh run download`，两命令均 exit 0；没有以 root 下载副本代替独立取证。

- run: [39268926496 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39268926496/attempts/1)，event=push、branch=main、head_sha 精确等于本报告 SHA。最终 completed/success，updated_at=`2026-10-19T14:29:34Z`。
- 三项 jobs：lean **118115772115**、state-check **118115772525**、dashboard / snapshot **118117382264**，均实际查询为 completed/success。曾观察 lean 运行中，待最终三项成功后才签发。
- `lean-ci-result` artifact **12194531278**，ZIP **491 bytes**，API digest=`sha256:4a4b268b7c525237cb8253f1a2481cdd7106e4483c3ebaea39f43d2ec4a4e70d`。
- `lean-declaration-evidence` artifact **12194286705**，ZIP **241977 bytes**，API digest=`sha256:022667e3a2f9ef854d4c0c3675cbcef5e7db73c7692f574f86cc4c8ffea973ea`。
- 两工件 workflow_run 均绑定同一精确 SHA、main 和 run；ZIP digest 与解包 raw digest 分别核对记录。

独立 result `/tmp/carleman-t177-time-control-reconstruction-main-ci/result.json` 为 **537 bytes**，SHA256=`5e7b9a0d37b61fbad9afc7c98ec6296494ee20072037466f481963fae5b89168`。实际 status=PASS，checked_sha=source_head_sha=`d1134c0ccc8f343aef6223f304fe52f86a7aff1d`，targets=[Carleman]，finished_at=`2026-10-19T14:28:18.488394+00:00`，ci_url、Lean 和 mathlib 精确对应上述证据。

独立 raw `/tmp/carleman-t177-time-control-reconstruction-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t177-time-control-reconstruction-local-axioms.txt` **逐字节完全一致**，均为 **2618585 bytes**、SHA256 **`8ba262e78f84145848ca33b497f1d8ccb63f25d2c83f784cd4f3d3fb95d729e6`**；全部类型、公理和最终 8254 项成功记录均实际读取。

## 最终结论

**16/16 PASS，未发现阻断缺陷。** 原后向 Euler 时间单元、真实 Bochner L²、原控制成本和物理配对均忠实；FE 用区域零延拓，FD 用实际 E_h B_h；在显式等距 K 和统一成本界下，得到实际重构序列对全部 L² 测试的弱子列及同一极限成本。C193 可登记 **AUXILIARY/REVIEWED**，原文保持 **17/26**。原区域支撑、离散方程的极限识别、终端零值及完整控制收敛仍未由本批证明。本报告仅单文件提交，不 push；通知后正文与 reviewed_at 冻结。
