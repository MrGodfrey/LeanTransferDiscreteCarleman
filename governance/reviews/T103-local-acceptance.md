# T103 / C119 独立本机验收

- 结论：**PASS（AUXILIARY）**。三模块 8 项显式声明逐项通过数学语义、实际类型、依赖及固定版本 CI 验收。允许将 C119 记为已独立验收的辅助结果；原论文覆盖保持 **14/26**，不据此提升完整 FD / P012 或 `eq:testsuper`。
- `checked_sha`: `23d19fb4276d47fb788d7040ae156f3e67e46ec8`
- `base_sha`: `c749c4620eb0cba6f74a8a6ae58f6ce114645897`
- 验收者：独立 Agent `/root/accept_section3`。
- 签发时间：`2026-10-19T03:19:21+00:00`（UTC；完成原始证据核验后签发）。
- 只读取固定提交及其固定产物；工作区 T104 未跟踪文件和后来生成的 `.ci/axioms.txt` 未纳入本次结论。仅新增本报告，未修改实现、原稿、台账、根导入或提交。

## 原文范围及实际对象

直接核对固定 `paper/main.tex` Section 6：1470 起的真实分片仿射 `V_h ⊂ H¹₀` 定义，1634 起的任意固定维数 Cartesian 网格、互相可比正步长、实际 Kuhn 剖分、内部帽函数重构及零边界数据，以及 Appendix B Step 3（2879 起）的节点平方权测试和 `R_h T_{σ,h} z = I_h(σ² R_h z)` 桥接。原文网格取 `o=0`、`δ_r=L_r/N_r`、`h=max δ_r`，可比条件给固定 `κ` 使 `h/κ ≤ δ_r ≤ h`；本批允许任意平移，覆盖这个实例，没有增加额外网格或状态限制。

本批解决 Step 3 所需的实际统一形状条件和节点代表一致性。它既没有把抽象形状参数当作真实内球，也没有在任意 L² 等价类上定义点值。节点唯一性只对由真实有限节点插值产生的 L² 类陈述；它恢复的是每个闭单元的实际仿射多项式及其顶点数据。

所有三文件已从固定 Git 对象完整阅读；8 个完整展开类型从实际公理产物逐一核对。下表中的名称均在 `Carleman` 命名空间下。

## 8 项声明逐项验收

| 模块 / 声明（源码行） | 实际类型与证明核查 | 结论 |
|---|---|---|
| `Geometry/AffineSimplexInball.lean:13` — `simplex_exists_inball` | 任意 `Affine.Simplex ℝ (SpatialCoordinates d) d`，输出实际 `a`、`r>0` 和 `Metric.ball a r ⊆ simplicialCell T.points`。满维仿射独立性给非空内部，再由内部开性选球；没有预设内球或形状正则性。 | PASS |
| 同文件 `:19` — `affineSimplex_contains_ball` | 输入实际包含球、连续线性同构 `A`、平移 `b`、`Γ>0` 和真实逆算子范数 `‖A⁻¹‖≤Γ`，推出像单纯形包含以 `Aa+b` 为中心、半径 `r/Γ` 的球。对目标点明确取 `A⁻¹(y-b)`，通过实际距离估计及 `A A⁻¹=id` 证明包含；半径缩放方向正确。 | PASS |
| `Geometry/CartesianKuhnShape.lean:15` — `cartesianKuhn_cellDiameter_le` | 所有实际有限单元 `i`、正步长及 `δ_j≤h`，真实 `Metric.diam(cell i)≤(d+1)h`。依赖真实 Kuhn 单元在其坐标盒内及已证任意两点距离界，不以单元标签或形式尺度定义直径。 | PASS |
| 同文件 `:24` — `cartesianKuhn_maxDiameter_le` | 对相同全部网格，实际有限 `maxDiameter≤(d+1)h`。使用非负真实单元直径的 `NNReal` 有限上确界逐项控制；没有单元个数因子，空索引时上确界为零。 | PASS |
| 同文件 `:36` — `cartesianKuhn_uniform_inballs` | 固定 `d`、`κ>0` 后先选 `C>0`，再量化全部 `o,δ,hδ,N,h` 和 `h/κ≤δ_j≤h`。固定参考 Kuhn 单纯形先选 `a₀,r₀>0`；所有物理单元用真实排列后对角伸缩和平移得到中心，共同半径 `r=r₀h/κ`。逆范数界 `κ/h` 内部供应，`C=(d+1)κ/r₀` 给 `diam(K)≤Cr`。常数无位置、网格大小、单元标签或状态依赖。 | PASS |
| `Spatial/NodalMultiplierUniqueness.lean:18` — `SimplicialPartition.nodalLp_vertex_eq` | 对实际有限满维剖分、开凸有限测度域和 `FaceMatching`，两个真实 `nodalLp` 类相等推出所有单元所有顶点的输入数据相等。借 `cell_measure_le_domain` 把域内 a.e. 身份限制到闭单元，得到局部仿射函数 a.e. 相等；连续性、Lebesgue 开集正测度和 `K⊆closure(interior K)` 提升到整个闭单元，再使用真实插值顶点身份。包括共享面和物理边界顶点。 | PASS |
| 同文件 `:36` — `SimplicialPartition.nodalLp_multiplier_congr` | 相同 `nodalLp` 类的任意节点代表 `f,g`，经任意物理点函数 `ω` 逐节点相乘后，得到同一实际 `nodalLp` 类。先用上一条取得真实顶点数据相等，再用已证 `nodalLp_congr`。无需给有限节点操作额外加 `ω` 可测、有界或正性；结论没有错误声称任意 `ω` 的逐点乘积本身等于其节点插值。 | PASS |
| 同文件 `:47` — `cartesianKuhnReconstructionLp_mem_conforming` | 对任意完整内部向量 `f : CartesianInteriorIndex N → ℝ`，原帽函数重构 `R_h f` 属于同一实际剖分的 `conformingSpace (dirichletSubspace Ω)`。重写为已证实际节点 L² 类，利用实际面匹配、边界拟合、内部数据在域外为零，内部供应全部边界顶点零值，调用真实 H¹₀ 节点资格。没有对 `f` 添加资格假设。 | PASS |

上述类型在固定 `axioms.txt` 中分别自第 24321、24324、24334、24340、24343、24357、24365、24372 行开始，均实际打印类型及递归公理依赖。

## 重点数学检查及依赖

### 真实几何与统一量词

`affineSimplex_cell` 识别的正是闭凸包的实际仿射像。Kuhn 单元的映射为实际坐标排列后正对角伸缩，中心平移为实际网格点。独立检查 `CartesianKuhnSimplex`、`KuhnInverseMap` 与 `KuhnAllowedWeightComparison`：排列保持欧氏范数；各正步长的倒数受 `κ/h` 控制；实际闭单元在对应物理坐标盒内。因此本批没有把逆范数界或直径界作为未清偿的目标前提。

参考中心及半径在所有网格之前选定，依赖固定维数；`C` 的存在量词位于全部数值数据之前。所有边界单元与内部单元走同一构造。证明的是一个实际正半径包含球，不需要声称选到最大内接球；这已给出所需的统一直径/内球比。半径共同为 `r₀h/κ`，精确代入 `Cr=(d+1)h`。

原文使用 `d≥1`、`N_r≥2`；本批并未收紧，声明允许 `d=0` 和较小 `N`。零维空间的满维零单纯形仍有非空内部，正半径球为其唯一点，直径为零；空有限分割的最大直径为零，量词及正分母处理成立。本批只声称直径上界和实际内球，未单独宣称原文“最大直径与 h 双向可比”的所有方向。

### L² 类、节点值和完整状态

检查 `SimplicialPartition`、`SimplicialIntegrals`、`SimplexNodalLp`、`SimplicialNodalOperator` 的实际定义及被调用证明。单元是满维闭单纯形；在开凸域中，域闭包与域的体积差为零，从而闭单元限制测度不超过域限制测度。此步骤使“域内 L² 相等”可以合法用于包括边界的闭单元。随后只对连续仿射代表使用 `Measure.eqOn_of_ae_eq`，没有将任意 a.e. 代表在顶点的值当作不变对象。

核对 `NodalDirichletMembership` 与 `CartesianKuhnReconstructionJet`：`dirichletSubspace` 是真实测试函数 H¹ 图闭包，节点函数的资格来自此前的内缩和光滑逼近，不是自定义较小零边界状态族。`conformingSpace` 正是实际分片仿射 L² 范围与该 H¹₀ 子空间的交。当前新结论是所有原内部数据重构的成员资格；完整 conforming 状态的节点表示由既有 `FullConformingNodal` 结果提供。两者配合本批唯一性，允许后续把任选的节点代表与实际原数据对齐。本批自身不把成员资格误写成新的满射/双射定理，也不把代表无关性当作已证超逼近估计。

### 固定依赖与无循环

递归展开三新模块的 `Carleman.*` 导入闭包共有 **248** 个文件；其中 **245** 个既有文件与基线逐字相同。关键旧依赖按上文实际阅读、沿证明调用核查；新模块按“参考内球 → 实际网格形状”和“节点 L² 唯一性 → 节点乘法一致性”推进，没有反向依赖后续超逼近或 FD 完整结论。

三模块均在固定 `Carleman.lean` 根目标导入。新增源码无 `sorry`、`admit`、`axiom`、`native_decide`。固定 `tools/CheckAxioms.lean` 的全环境递归审计实现与基线一致，遍历包括私有名还原后的所有 Carleman 声明并调用递归公理收集。三份治理文件、原论文、工具链与 mathlib 锁定版本亦与基线一致。原论文 SHA256：`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## CI 与原始证据

验收者自行查询 GitHub 同 SHA 的 main/push 运行并自行下载两个原始 artifact，未以主执行者转述代替核验。

- Run **39193233175**，attempt **1**，`head_sha=23d19fb4276d47fb788d7040ae156f3e67e46ec8`，最终 `completed/success`，运行页面：[Lean CI](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39193233175/attempts/1)。API `updated_at=2026-10-19T03:11:59Z`。
- `state-check` job **117870354369**：`completed/success`。
- `lean` job **117870354595**：`completed/success`；实际 proof build、结果记录、声明证据上传均成功。
- `dashboard / snapshot` job **117871243385**：`completed/success`。
- `lean-ci-result` artifact **12161196059**；下载到 `/tmp/carleman-kuhn-test-geometry-main-ci/result.json`。
- `lean-declaration-evidence` artifact **12160787786**；下载到 `/tmp/carleman-kuhn-test-geometry-main-axioms/axioms.txt`。
- 实际 `result.json`：`status=PASS`；`checked_sha` 和 `source_head_sha` 均为完整固定 SHA；`targets=["Carleman"]`；`finished_at=2026-10-19T03:10:45.254340+00:00`。
- Lean **4.35.0**，Linux 构建提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib **56a005855ea17e0b0958f73ec801ae140b0a1679**，均与固定锁定配置一致。

远端原始 `axioms.txt` 与 `/tmp/carleman-kuhn-test-geometry-local-axioms.txt` 已独立逐字节比较，完全相同：**1,880,351 bytes**；SHA256 **`6c45919c3ef1e6d299fc98344f93715dda699a91861e574d81ba5c2db40acb89`**。8 项清单全部具备完整类型与依赖。全文件检查到 2112 个带公理的打印记录（2108 个不同名称）以及 8 个无公理记录；所有出现的依赖均限于 `propext`、`Classical.choice`、`Quot.sound`。此打印记录数不是全环境声明总数；最终递归审计明确通过 **6293** 个 Carleman 声明。

独立读取固定日志：`/tmp/carleman-kuhn-test-geometry-target.log` 显示定向 **3438 jobs** 成功；`/tmp/carleman-kuhn-test-geometry-full.log` 显示全库 **3812 jobs** 成功及上述 **6293** 项审计通过。本报告变更仅为文字验收，无需重新生成不同工作区版本的证明产物。

## 最终判定及保留范围

**8/8 PASS，C119 可记为独立验收通过的 AUXILIARY。** 没有发现需要修复的数学、类型、量词、依赖或版本绑定问题。

本批提供原真实 Kuhn 网格的统一内球与直径上界、实际节点 L² 类唯一性、节点乘法代表一致性和全部原内部数据重构的 conforming 成员资格。允许权的具体估计、完整 `eq:testsuper`、时间测试性质、观察接口及完整 FD 数值假设不能从本批辅助结论直接宣布完成。原文覆盖保持 **14/26**。
