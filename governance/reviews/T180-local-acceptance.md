# T180 / C196 独立本机验收：原差分单元平均初值的任意 L² 强一致性

- checked_sha / source_sha: `1d85add4836977c5a6b3bd55448110e9bad21a50`
- mathematical_base: `c93eb000a3fe6624a0923b70781b2caa173cce4b`
- reviewed_at: `2026-10-19T14:55:17+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_foundations`
- result / axiom_check: **PASS / PASS**；全部 **9/9** 显式声明通过，无阻断缺陷。
- scope: **AUXILIARY**；C196 可登记 REVIEWED，原文覆盖保持 **17/26**。本批证明原 FD 任意 L² 初值的真实单元平均强一致性，不提升 P1、势一致性或完整控制/PDE 极限。

## 固定对象、原文与依赖验收

直接读取固定 Git 对象中三个新模块的全部证明、固定 raw 中九项完整展开类型、T180 分析、MATH_SPEC 及 C191/C195/C196 台账。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES 和 PAPER_COVERAGE 与已读 T177 相同，继续适用。后续 SpatialTestLpDensity 等工作树增量、动态根导入和动态 `.ci/axioms.txt` 全部排除。

原文对照 `paper/main.tex:2294–2318` 的任意 y0∈L²、原对偶单元、eq:conv-data-fd 的真实平均和 E_h；并读取 `2897–2925`，特别是 `eq:conv-data-consistency` 的 ‖E_h y0,h−y0‖→0 及相邻的初值范数界。另核对 2344 行起完整控制收敛结论以限定本批范围。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，没有改变论文目标。

签发前已完整读取 [T179 冻结报告](T179-local-acceptance.md)，报告提交 **`6a2d0267d61d5d8e316a4d341dd48a60b62447f7`**，checked SHA 正是本批 mathematical_base，reviewed_at=`2026-10-19T14:50:09+00:00`，11/11 PASS。固定 T180 台账中 C195 仍为 BUILT/PENDING，以这份明确版本的正式报告补齐依赖验收门槛。另重新读取 T179 三模块的全部数学证明和 T175 原重构、质量、伴随、真实单元几何，不以已有报告代替实际依赖检查。

## 九项声明逐项验收

顺序与固定 manifest 一致。源码位置相对 `Carleman/Spatial/`；raw 行为固定完整类型的起始行。

| 序号 | 完整声明 | 固定源码 | raw 行 | 判定 |
| --- | --- | --- | --- | --- |
| 1 | `Carleman.cartesianBoxCellIsometry` | `FixedBoxCellReconstruction.lean:14` | 34457 | 同一固定原盒 L² 中的真实对偶单元指示重构；定义忠实性 PASS。 |
| 2 | `Carleman.cartesianBoxCellIsometry_adjoint_average` | `FixedBoxCellReconstruction.lean:21` | 34465 | 实际 Hilbert 伴随逐坐标等于原体积归一化积分；PASS。 |
| 3 | `Carleman.cartesianBoxCellIsometry_average_norm` | `FixedBoxCellReconstruction.lean:30` | 34472 | 任意原 L² 数据的原离散物理范数不增；PASS。 |
| 4 | `Carleman.cartesianBoxCell_average_error` | `FixedBoxCellReconstruction.lean:38` | 34477 | 固定原域中的真实平均误差，保留完整未覆盖区域项；PASS。 |
| 5 | `Carleman.cartesianBox_uncovered_volume_tendsto` | `FixedBoxCellReconstruction.lean:52` | 34489 | 精确边界条带体积差随全部坐标步长趋零；PASS。 |
| 6 | `Carleman.isometric_reconstruction_residual_bound` | `DenseReconstructionConvergence.lean:15` | 34501 | 真实 Id−EE* 残差对所有 H 数据范数≤1；PASS。 |
| 7 | `Carleman.isometric_reconstruction_tendsto_of_denseRange` | `DenseReconstructionConvergence.lean:19` | 34507 | 允许离散空间随 n 变化的实际稠密性推广；PASS。 |
| 8 | `Carleman.cartesianBoxCell_continuous_residual_tendsto` | `CartesianCellStrongConvergence.lean:17` | 34519 | 实际闭包一致连续性与条带项给连续辅助类强逼近；PASS。 |
| 9 | `Carleman.cartesianBoxCell_average_strong_convergence` | `CartesianCellStrongConvergence.lean:78` | 34538 | 所有原 L² 数据、同一实际单元平均与重构的强收敛；PASS。 |

## 同一固定原盒与真正原平均

固定 lo、hi 后，所有网格满足正步长 δ_n,j 和精确几何关系 **lo_j+N_n,j δ_n,j=hi_j**。`cartesianBoxCellIsometry` 并非选择任意等距映射，而是直接调用 `finiteCellIsometry`，单元参数正是原 `cartesianDualCell lo δ N`，质量为 **∏j δ_j**，目标测度始终是 `volume.restrict (openCoordinateBox lo hi)`。因此离散空间虽变化，所有重构落入同一原 H；不在不同盒上分别计算范数后误称强收敛。

实际 E 的底层函数是单元指示函数有限和，a.e. 在 D_i 上为 z_i，在未覆盖区为零；与原稿 E_h 相同。`funext hbox` 和 `subst hi` 仅把精确相等的盒端点代入相同构造，证明参数的差异由证明无关性处理，没有缩放、重新选取平均或换用 R_h。相邻开单元公共面未纳入单元并，但真实补集测度在全程保留。

原状态 `CartesianPhysicalState` 使用全部内部节点索引 ∏j Fin(N_j−1)，内积为 **(∏jδ_j) Σ z_i w_i**，不是函数 sup 范数。有限维性只用于建立该原有限 Hilbert 空间的完备性；定量收缩和极限没有取其网格相关范数等价常数。

第 2 项的 E* 是真实 Hilbert 伴随。重新核对 FiniteCellReconstruction：对全部离散测试向量的真实积分配对确定 E*u，质量正性合法消去质量，逐坐标得到 **(∏δ_j)⁻¹∫D_i u**。D_i⊆Ω 使两次限制测度准确化为原 Lebesgue 单元积分；原 L² u 在有限单元上可积，不需要附加 L¹ 或点值假设。该平均不依赖 Lp 代表，因为单元限制测度由原域限制测度控制。第 3 项是这个同一平均算子的范数界 **‖E*u‖≤‖u‖**，直接给原文初值物理成本不增。

## 精确条带体积与退化网格

第 5 项以 N_n,j≥1 和固定盒等式把 T179 的实际补集体积改写为

`ν((⋃i D_n,i)ᶜ) = ∏j(hi_j−lo_j) − ∏j(hi_j−lo_j−δ_n,j)`，

其中 ν=volume|Ω，故补集测度只计算原盒内未覆盖区，没有减入无界外域。T179 的单元并体积来自真实有限可测不交并和内部节点基数，Nat.cast_sub 所需的 N≥1 在本批明确保留；不是把自然数截断减法直接当作实数减法。有限个坐标的 δ_n,j→0 后，真实有限乘积极限给差值→0。没有把条带直接当作零测集，也未假设 E 满射。

N≥1 正是有效固定盒分割的整数条件；正维时结合 hbox、δ>0 推出每边 hi>lo。允许 N_j=1，此时某坐标没有内部节点，E=0 且未覆盖区域可为整个盒，精确误差及体积公式仍成立。最终细化极限不会要求每一个粗网格先有内部节点。d=0 时所有坐标条件为空，空乘积为1、实际零维盒与单元均为单点，未覆盖体积为1−1=0；没有除以 d 或非法选取一个坐标。

第 1–4 项甚至不要求 N≥1；若正维某 N_j=0，原等式允许空盒和空离散空间，这些等距/平均/误差陈述仍有意义。最终原非空盒细化结论则使用明确 N≥1，不把空域特例当作非空域证明。

## 连续辅助类：闭包模与实际误差

第 8 项仅以全空间有界连续函数 f 为辅助数据，实际 u=`BoundedContinuousFunction.toLp 2 ν ℝ f`。该有限限制测度资格由原盒有界性在内部供应。不是假定最终原 L² 数据已有连续代表。

真实开盒闭包在有限维 Euclidean 空间紧，mathlib Heine–Cantor 只在该闭包上给 f 的一致连续模。代码没有假设 f 在全空间一致连续。任意单元点及其真实中心节点均属于原盒，从而属于同一闭包。`cartesianDualCell_dist_le` 由真实 Euclidean 闭盒直径界给 **dist(x,x_i)≤d h_n**；δ_n,j≤h_n、h_n≥0 和 h_n→0 清偿全部局部振幅条件。没有把坐标 sup 范数直接当 Euclidean 距离。

取 V=ν(univ)≥0，η=sqrt(ε²/(2(V+1)))>0。闭包模使单元振幅≤η，实际条带极限使 **‖f‖²ν(未覆盖区)<ε²/2**。第 4 项来自真实最佳逼近和 L² 指示积分估计，给 **‖u−EE*u‖²≤η²V+‖f‖²ν(未覆盖区)**；η 的准确恒等式给第一项≤ε²/2，因此误差范数<ε。V+1 保留零体积情况，无除以可能为零的域体积。

局部节点值 f(x_i) 仅用于构造比较候选；真正左端仍是同一个 u 的单元平均重构，而非节点采样重构。已重新读取 T179 中候选残差的 a.e. 身份、平方可积性、integral_mono_ae 与最佳逼近步骤，常数没有额外单元数、最小质量倒数或长宽比。连续辅助证明的模和最终所需 n 可依赖 f、ε、固定盒；本批没有宣称对全部 L² 单位球统一趋零的错误算子范数收敛。

## 变化离散空间上的真实稠密性推广

第 6–7 项允许任意实完备 Hilbert H 和各自不同的实完备 Hilbert X_n，以及实际线性等距 E_n:X_n→H。第 6 项把已证最佳逼近的离散候选取0，推出残差 **R_n=Id−E_nE_n*** 满足 ‖R_nu‖≤‖u‖；没有误把 EE* 等同 H 上恒等。

第 7 项将 R_n 真正定义为 H→L[ℝ]H，并用其线性分解 R_nu=R_n(u−f(v))+R_nf(v)。给定 ε>0，真实 DenseRange f 先选 ‖u−f(v)‖<ε/2，再在这个固定 v 上应用已知强逼近，得到另一项<ε/2。所有估计均在同一 H 中，X_n 不同不影响论证。常数1独立于 n，最后以范数差趋零等价转换成 **Tendsto(E_nE_n*u)(𝓝u)**。

第 9 项没有把 DenseRange 或连续类收敛作为调用者条件：前者由固定 mathlib `BoundedContinuousFunction.toLp_denseRange` 实际供应，后者由本批第 8 项供应。已核对该 mathlib 定理的完整前提及证明入口：有限 p、1≤p、Normal/Borel 空间、相应第二可数性与 WeaklyRegular 有限测度。此处 p=2，空间为有限维 Euclidean、值域ℝ；有限限制测度来自实际盒有界性，而有限 Borel 测度在可度量空间的 WeaklyRegular 实例在固定 mathlib 中成立。没有新增正则测度公理或“连续数据稠密”假设。

最终对**每个任意原 u∈L²(Ω)** 得 E_n(E_n*u)→u，u 无点值、光滑、H¹、零迹或本质有界条件。几何输入为任意固定平移盒、正各向步长、N≥1、固定盒等式、一个趋零的非负公共步长上界 h；这包含原 h=max_jδ_j，且没有网格嵌套、各向步长比例、准一致性或时间耦合。适用于所有有限 d，故覆盖原 d=2、3。没有 T 参数及需重新选择的时间相关常数。

## 固定依赖、公理和构建

递归解析三个新入口的实际 Carleman 导入闭包为 **333** 个模块，除三新模块外的 **330** 个与 mathematical_base 逐字节一致。关键接受版本另行比较完整闭包，均无变化：

| 入口 / 已接受阶段 | 固定接受版本 | 闭包模块数 |
| --- | --- | --- |
| CartesianCellApproximation / T179 | `c93eb000a3fe6624a0923b70781b2caa173cce4b` | 330 |
| IsometricReconstructionProjection / T179 | `c93eb000a3fe6624a0923b70781b2caa173cce4b` | 1 |
| CartesianCellReconstruction / T175 | `7c2ceacf62d42b168879106b8c6d6fc246c45794` | 326 |

固定根目标导入三模块，九个名字均实际执行完整 `#check @...` 和 `#print axioms ...`。新源码无 sorry、admit、新 axiom 或 native_decide。九项均只有正常 `propext, Classical.choice, Quot.sound` 依赖。独立解析完整 raw 的 **3196** 条公理记录（**3192** 个不同名字、**9** 条无公理记录），按逗号分词并规范化换行空白后，白名单外依赖为零。真实递归审计末行确认 **8309 项 Carleman 声明全部通过**。

实际读取 `/tmp/carleman-t180-strong-target4.log`，最终原强收敛模块 **3525 jobs** 成功；固定 `/tmp/carleman-t180-cell-strong-convergence-build.log` 根目标 **4128 jobs** 成功。`-axioms.log` 为零字节 stderr，审计结论来自实际 raw 末行，而非空日志推断。

Lean pin 为 v4.35.0，正式 CI compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 与本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、正式 CI workflow 与 lean_ci.sh 相对已审 T177 未变。实际新用的有界连续函数 Lp 稠密性、有限测度弱正则实例、紧集 Heine–Cantor 均读取该固定 mathlib 版本。

## 独立取得的同 SHA CI 与工件

本 Agent 独立查询实际 GitHub run/jobs/artifacts API，并分别自行执行两次 `gh run download`，均 exit 0；没有使用主执行者的 root 下载副本替代独立取证。

- run: [39272614064 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39272614064/attempts/1)，event=push、branch=main、head_sha 精确等于本报告 SHA；最终 **completed/success**，updated_at=`2026-10-19T14:54:54Z`。
- lean **118128593275**、state-check **118128593955**、dashboard / snapshot **118130680431**：三项最终均实际查询为 **completed/success**。曾观察 lean 的缓存收尾仍运行，并未以已发布工件代替最终三作业成功。
- `lean-ci-result` artifact **12196640400**，ZIP **493 bytes**，API digest=`sha256:52d95a11ee7d32553f9831749f70d07a19bc11fefb5e11215f0595c045c03e2b`。
- `lean-declaration-evidence` artifact **12194694931**，ZIP **244681 bytes**，API digest=`sha256:d92fee79c55012a4886a56e9d7521178405890ff31317c930f2c474b0f0a4ea9`。
- 两工件的 workflow_run 均绑定同一精确 SHA、main 和 run；压缩工件 digest 与解包 raw hash 分开记录。

独立 `/tmp/carleman-t180-cell-strong-convergence-main-ci/result.json` 为 **537 bytes**，SHA256=`a339ab5b18e80be93f4640e44e79cac29a2372ec775a5bee9b9ed8b7a437d224`；实际 status=PASS、checked_sha=source_head_sha=`1d85add4836977c5a6b3bd55448110e9bad21a50`、targets=[Carleman]、finished_at=`2026-10-19T14:53:38.085849+00:00`，ci_url/Lean/mathlib 均匹配。

独立 `/tmp/carleman-t180-cell-strong-convergence-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t180-cell-strong-convergence-local-axioms.txt` **逐字节完全一致**，均为 **2645145 bytes**，SHA256 **`4cadd3dd0926265e8f51602850a1b4a725e3324d534f0226022409019a2acb76`**。完整类型、公理记录及最终 8309 项成功实际核对。

## 最终结论

**9/9 PASS，无需修复。** 同一固定原盒上的真实 E_h、其原物理伴随平均、范数不增、实际边界条带趋零与稠密性推广共同证明原 FD 任意 L² 初值的强一致性。C196 可登记 **AUXILIARY/REVIEWED**，原文维持 **17/26**；P1 投影一致性、势强一致性、R_h−E_h 估计及连续 PDE/终端控制极限不由本批完成。仅本报告单文件提交，不 push、不改数学或台账；通知后正文及 reviewed_at 冻结。
