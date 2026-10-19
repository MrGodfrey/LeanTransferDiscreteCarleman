# T179 / C195 独立本机验收：真实单元平均误差与边界条带

- checked_sha / source_sha: `c93eb000a3fe6624a0923b70781b2caa173cce4b`
- mathematical_base: `673bf04f87c065482b06bac35a2a97c971592dc2`
- reviewed_at: `2026-10-19T14:50:09+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_section3`
- result / axiom_check: **PASS / PASS**；全部 **11/11** 显式声明通过，未发现阻断缺陷。
- scope: **AUXILIARY**；C195 可登记 REVIEWED，原文覆盖保持 **17/26**。不提升任意 L² 数据强一致性、势一致性或完整控制收敛。

## 固定对象、原文与声明范围

直接读取固定 Git 对象的三模块全部源码、11 项完整展开类型和证明，核对 AGENTS、PROJECT_OPERATIONS、state/README、MATH_SPEC 的 T179 条目、[阶段分析](../analysis/T179-cell-approximation.md) 及固定 C195/T179 清单。声明顺序与两个固定台账条目和 manifest 一致。独立读取既有依赖的实际实现，不把执行者报告或 CI 代替数学验收。后续 CartesianCellStrongConvergence、DenseReconstructionConvergence、FixedBoxCellReconstruction 及动态 root/audit 增量全部排除。

对照 `paper/main.tex:2294–2318`：任意原 y0∈L²、真实内部对偶单元 D_i、物理质量 ω_i=|D_i|、单元平均初值及在未覆盖条带为零的 E_h。另读 `paper/main.tex:2893–2925`，特别是 `eq:conv-data-consistency` 的任意 L² 初值强收敛目标。本批提供该目标的定量基础，尚未把固定原域、细化序列、条带体积趋零和密度组合成原极限定理。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与基线不变。

## 全部声明逐项验收

源码相对 `Carleman/`；raw 行是本次固定完整类型产物中的起始行。

| 序号 | 完整声明 | 固定源码 / raw 行 | 判定及实际内容 |
| --- | --- | --- | --- |
| 1 | `Carleman.reconstruction_adjoint_left_inverse` | `Spatial/IsometricReconstructionProjection.lean:12` / 34363 | PASS；真实 Hilbert 伴随满足 E*E=id。 |
| 2 | `Carleman.reconstruction_residual_orthogonal` | 同文件:16 / 34368 | PASS；u−EE*u 与所有 Ev 正交。 |
| 3 | `Carleman.reconstruction_error_pythagoras` | 同文件:22 / 34373 | PASS；精确误差平方分解，离散余项为 ‖E*u−v‖²。 |
| 4 | `Carleman.reconstruction_best_approximation` | 同文件:30 / 34380 | PASS；EE*u 对所有离散候选 v 的最佳逼近。 |
| 5 | `Carleman.finiteCells_union_volume` | `Spatial/FiniteCellApproximation.lean:18` / 34385 | PASS；有限可测不交等质量单元的精确并体积。 |
| 6 | `Carleman.finiteCellLinear_error_bound` | 同文件:23 / 34392 | PASS；真实 L² 指示重构误差，保留补集项。 |
| 7 | `Carleman.finiteCell_average_error_bound` | 同文件:78 / 34403 | PASS；最佳逼近将同一误差界传给实际单元平均。 |
| 8 | `Carleman.cartesianDualCells_union_volume` | `Spatial/CartesianCellApproximation.lean:16` / 34419 | PASS；原有限内部节点单元并的准确体积。 |
| 9 | `Carleman.cartesianDualCells_uncovered_volume` | 同文件:26 / 34426 | PASS；原盒内未覆盖区域的精确体积差。 |
| 10 | `Carleman.cartesianCell_average_continuous_error` | 同文件:47 / 34434 | PASS；真实有界连续函数的 L² 类及平均误差。 |
| 11 | `Carleman.cartesianCell_average_lipschitz_error` | 同文件:72 / 34445 | PASS；实际 Euclidean 距离供给 ε=C d h。 |

## 真实投影和原物理平均

前四项对任意实完备 Hilbert X、H 和任意线性等距嵌入 E 成立，未要求 E 满射或有限维。重新读取固定 mathlib 的 `LinearIsometry.adjoint_comp_self`，它从真实等距性推出伴随复合为恒等。第 2 项通过真实伴随内积等式与 E*E=id 消去残差；第 3 项先分解 u−Ev=(u−EE*u)+E(E*u−v)，再用实际 norm_add_sq_real、正交性和等距性；第 4 项以非负平方得到范数最小性。没有把目标正交性、投影身份或误差界作为输入，也没有把 EE* 错认作整个 H 的恒等算子。

重新读取 `FiniteCellReconstruction`、`CartesianCellReconstruction` 和 `PhysicalFiniteSpace`：有限状态的原内积确为 mass·Σ f_i g_i，范数由这个正内积构造，完备性由实际有限维空间内部给出。E 是真实 L² 指示函数有限和，单元不交和 ν(K_i)=mass 精确给等距性。其伴随逐坐标是 **mass⁻¹∫K_i u**，由全离散测试的配对等式识别；不是任选一个同范数离散向量或节点采样。Cartesian 中 mass=∏δ_j，D_i⊆Ω 使限制测度积分严格等于原 Lebesgue 单元积分。这与原 `eq:conv-data-fd` 的 y0,h 完全一致，且 E* 对任意 L² 输入已经有定义及范数收缩。

## a.e. 误差、可积性和未覆盖区域

第 6 项在有限测度 ν、任意有限指标集、可测两两不交单元上，显式以 ε≥0、B≥0、逐单元 ν-a.e. 的 |u−f_i|≤ε 和 ν-a.e. 的 |u|≤B 为输入。这里 u 是真实 L² 类，f 是完整物理离散向量。该项不需要单元等体积；第 7 项为使用等距性才加入等体积条件。

证明先用 `Lp.coeFn_sub`、`finiteCellLinear_ae` 和有限 `ae_all_iff` 取得同一个 a.e. 代表集合。A=⋃K_i 内因真实不交性，指示和恰为唯一单元的 f_i；A 外整个指示和为零。因此实际残差平方被 **ε²1_A+B²1_Aᶜ** 控制。L² 成员资格供给残差平方可积，ν 有限供给两个常数指示函数可积，随后用实际 integral_mono_ae。L² 范数平方通过 L2.inner_def 严格识别为该积分，而不是以一个抽象“误差能量”替换。

积分先得到 ε²ν(A)+B²ν(Aᶜ)，最后仅把非负第一项放大为 ε²ν(univ)。边界条带项方向正确且没有丢弃；没有假设单元覆盖 Ω、边界零值或条带零测。第 7 项对相同 u 和候选 f 用已证最佳逼近取平方，所得被估计量是 **u−EE*u**。空指标集合法，此时 E=0、A=∅，相应全域 B² 项仍保留。没有加入单元个数因子、最小单元质量倒数或范数等价常数。

## Cartesian 精确体积和维数退化情况

实际内部指标为 ∏j Fin(N_j−1)，节点坐标是 o_j+(a_j+1)δ_j，单元是各坐标开区间中心±δ_j/2。T175 的实际几何给每个单元包含于原开盒、严格不交和限制体积∏δ_j。第 8 项将真实有限并积分与指标基数 ∏j(N_j−1) 相乘，精确得到 **∏j((N_j−1:ℕ):ℝ)δ_j**，没有漏掉内部节点的 −1。

第 9 项在 N_j>0 时用有限限制测度的真实补集公式 ν(Aᶜ)=ν(univ)−ν(A)，并由开盒体积得到 **∏j(N_jδ_j)−∏j(N_jδ_j−δ_j)**。Nat.cast_sub 使用的 1≤N_j 在该项明确给出，不把自然数截断减法误当实数减法。这里 ν 是 volume|Ω，Aᶜ 虽取全空间补集，其测度正是 Ω 内未覆盖部分；不把无界外域体积减进来。

第 8、10、11 项不要求 N_j>0：若 d>0 且某 N_j=0，原盒为空且内部指标为空；若某 N_j=1，内部指标仍空而盒可非空，条带项正确保留。第 9 项允许 N_j=1。d=0 时空坐标乘积为 1，实际零维域和内部指标均为单点，单元覆盖该域，体积差为 1−1=0，距离和 Lipschitz 局部误差为零。证明没有除以 d，也没有用不存在的节点选择来掩盖空指标。

## 连续数据范围与全部量词

第 10 项的 f 是**全空间有界连续函数**，不是任意 L² 类或仅域内连续函数。实际 `BoundedContinuousFunction.toLp 2 ν ℝ f` 给原 L² 类，其 a.e. 代表等于 f；候选离散向量取真实点值 f(x_i)，局部振幅 ε 是显式输入，B 取真实全空间 sup 范数 ‖f‖。证明只对候选使用节点取值，最终左端仍为该 u 的真实单元平均重构误差。

第 11 项另有实际全局 LipschitzWith C、C∈ℝ≥0、h≥0 和每个 δ_j≤h。重新读取 T178 的 `cartesianDualCell_dist_le`：把点 x 与中心节点都放入实际闭对偶盒，调用真实 Euclidean 闭盒直径界得到 dist(x,x_i)≤d h，进而供给 ε=C d h。因此系数准确为 **(C d h)²**，未把坐标 sup 距离直接当 Euclidean 距离，也未声称更尖锐的常数。h=0 在正维正步长下没有满足全部假设的网格，零维仍合法。

所有 o、正步长 δ、N、候选数据及局部参数在实际声明中完整量化；没有网格相关隐藏常数或长宽比要求，也没有输入时间周期、离散 PDE、权函数、H¹₀ 资格。通用最佳逼近覆盖任意 L² u，但带 ε/B 的定量估计显式要求相应 a.e. 控制，最后两个实例只覆盖上述连续/Lipschitz 辅助类。这不是把原任意 L² y0 收紧成光滑初值：本阶段尚未声称原任意 L² 强收敛完成。固定原域的细化极限、密度及统一算子界组合仍须后续证明，势/状态/控制极限同样未由本报告升级。

## 固定依赖、公理和本机证据

递归检查三个入口的实际 Carleman 导入闭包 **330** 个模块；除三个新增模块外的 **327** 个与 mathematical_base 逐字节一致。关键接受版本进一步比较完整闭包：CartesianCellReconstruction 的 **326** 个模块与 T175 proof `7c2ceacf62d42b168879106b8c6d6fc246c45794` 不变；CartesianCellControlSupport 的 **327** 个模块与 T178 proof `673bf04f87c065482b06bac35a2a97c971592dc2` 不变。已读取的 [T175 报告](T175-local-acceptance.md) 和本次完整读取的 [T178 报告](T178-local-acceptance.md) 分别冻结于 `8a921065b09fe7082c4ef5d1163e9925f3f98709`、`b7f7971014e3839e49177496c3be31cd21784cf4`；当前报告字节与各冻结提交相同。

三个新模块都由固定 Carleman.lean 导入；11 项在固定 tools/CheckAxioms.lean 中各实际执行 #check @ 和 #print axioms。新源码无 sorry、admit、axiom、native_decide。11 项递归公理均仅 `propext, Classical.choice, Quot.sound`。独立解析完整 raw 的 **3187** 条显式记录、**3183** 个不同名字、其中 **9** 条无公理记录，白名单外依赖为零。实际 auditor 对全部 Carleman 常量调用 collectAxioms，raw 末行为 **8296 declarations PASS**；没有把空 stderr 当审计成功。

实际读取 `/tmp/carleman-t179-cartesian-approx-target2.log` 的 **3521 jobs** 成功和 `/tmp/carleman-t179-cell-approximation-build.log` 的 **4125 jobs** 根构建成功。Lean 固定 v4.35.0，正式 CI compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 和本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、lake manifest、原稿、lean workflow、tools/lean_ci.sh 与基线不变。实际新用的 Hilbert 伴随恒等式、有限并/补集实测度公式及有界连续函数 toLp/代表身份均从此固定 mathlib 读取。

## 自行取得的同 SHA CI 和原始工件

本 Agent 独立访问实际 run/jobs/artifacts API，并分别自行 gh run download 两工件，均 exit 0；未使用执行者的 root 副本替代下载。最终三项完成后才签发。

- run: [39271611095 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39271611095/attempts/1)，event=push、branch=main，head_sha 精确为 checked_sha；最终 **completed/success**，updated_at=`2026-10-19T14:49:10Z`。
- lean job **118125084247**、state-check job **118125084867**、dashboard / snapshot job **118127679982**：全部实际 **completed/success**。
- `lean-ci-result` artifact **12195952414**，ZIP **492 bytes**，API digest `sha256:4feb50b34a8d7905eb21bd8bab25c2cec507f963e1ec982a18347767704affd5`。
- `lean-declaration-evidence` artifact **12195797486**，ZIP **244023 bytes**，API digest `sha256:369a5d9bbf3d988e2347f611f7188b1ae31b7ea0a8e88050e190c6a83d5c9e8b`。

两 artifact 的 workflow_run 都绑定该 run、main 和精确 proof SHA。独立 `/tmp/carleman-t179-cell-approximation-main-ci/result.json` 为 **537 bytes**，SHA256=`a5f80b361a80a25df4b4002f1ff9f2eb18c5cc9a97cfbf2deb3104267ff53f7b`；实际 status=PASS、checked_sha=source_head_sha=`c93eb000a3fe6624a0923b70781b2caa173cce4b`、targets=[Carleman]、finished_at=`2026-10-19T14:47:20.375337+00:00`，ci_url/Lean/mathlib 均与上述记录一致。

独立 `/tmp/carleman-t179-cell-approximation-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t179-cell-approximation-local-axioms.txt` **逐字节相同**，均为 **2637861 bytes**，SHA256 **`0375631c2b6ef2d92888696381d6659f20d704b719b45ef4dc2e9da85c05c4cc`**。远端 raw 中 11 项完整类型、各公理名单和末行 8296 项成功均已重新核对。ZIP digest 与解包 raw hash 分别记录，不互相混用。

## 最终判定

**11/11 PASS，无需修复。** 本批从真实 Hilbert 等距重构得到原平均的最佳逼近，以真正 a.e. 积分证明保留边界条带的误差界，并精确计算原 Cartesian 体积。C195 可登记 **AUXILIARY/REVIEWED**；原任意 L² 初值强收敛及完整控制极限尚未完成，覆盖保持 **17/26**。仅本报告单文件提交，不 push，不修改数学、原稿或台账；通知后正文和 reviewed_at 冻结。
