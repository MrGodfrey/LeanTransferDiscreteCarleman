# T096 / C112 独立本机验收

- `checked_sha`: `ab5f74bf708c3bb969ecca40fcee8b26edd16d96`
- `base_commit`: `116908340801d3f1cd9f7e940304807f70bdb1ba`
- `reviewed_at`: `2026-10-19T02:21:42+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**；原全部 H²∩H¹₀ 状态的实际 Q_h 无权局部值与完整弱梯度 h² 误差。完整允许权 B.2/P026 和 FD/P012 仍待，原文保持 **13/26**。

本验收直接读取固定提交四个新模块的全部源码与证明、13 项实际完整展开类型、原 `paper/main.tex:2783–2870`、规格 `governance/analysis/T096-kuhn-local-error.md` 及关键旧依赖。执行者说明与构建结果没有代替数学核对；后续工作树中的加权与组装模块不在本次范围内。已自行查询同 SHA 的 main CI，并自行下载、读取、逐字节比较同 run 的两份原始产物。

## 全部 13 项声明

名称均省略公共前缀 `Carleman.`；位置相对于固定提交的 `Carleman/`。名单与交付 JSON、固定 C112 和 T096 台账逐项一致。

| # | 声明 | 固定位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `WeakSobolevJet.restrictSubdomain_eq_of_value_ae` | `Spatial/WeakJetLocality.lean:13` | PASS；任意阶真实弱 jet 在开子域的值 a.e. 相等决定整个限制 jet，使用完整弱测试唯一性。 |
| 2 | `SimplicialPartition.field_congr_on_cell` | `Spatial/WeakJetLocality.lean:22` | PASS；先限制到真实单元内部，再用实际单纯形边界零测，将值相等提升为闭单元上所有弱字段的 a.e. 相等。 |
| 3 | `bochnerL2Norm_mono_measure` | `Spatial/WeakJetLocality.lean:40` | PASS；显式 MemLp 有限性保证 eLpNorm 的 toReal 单调性合法。 |
| 4 | `bochnerL2Norm_lp_sub` | `Spatial/WeakJetLocality.lean:45` | PASS；真实 Lp 差的代表身份及测度单调性供应局部三角不等式，未将代表逐点相等作为前提。 |
| 5 | `cartesianClippedPatch_cell_measure` | `Spatial/CartesianKuhnErrorLocality.lean:14` | PASS；实际闭单元限制测度小于裁剪开块限制测度，正确保留物理边界零测例外。 |
| 6 | `cartesianKuhnProjectionJet_ae` | `Spatial/CartesianKuhnErrorLocality.lean:25` | PASS；原 Q_h jet 的实际值代表 a.e. 等于同一 R_hJ_h 函数。 |
| 7 | `cartesianKuhnProjectionJet_sub` | `Spatial/CartesianKuhnErrorLocality.lean:32` | PASS；原 Q_h 值的实际减法线性性经值注入性提升为整个真实 H¹ jet 的减法线性性。 |
| 8 | `cartesianKuhnErrorJet` | `Spatial/CartesianKuhnErrorLocality.lean:47` | PASS；误差定义为原 H¹ jet 减去同一 Q_h jet，值和梯度均为真实 L² 弱字段。 |
| 9 | `cartesianKuhnErrorJet_sub` | `Spatial/CartesianKuhnErrorLocality.lean:52` | PASS；真实误差 jet 的减法身份，不假设形式梯度或任意选择见证的线性性。 |
| 10 | `cartesianKuhnErrorJet_value_local_invariant` | `Spatial/CartesianKuhnErrorLocality.lean:59` | PASS；局部被 Q_h 再现的真实 H¹ jet 可从输入中减去而不改变闭单元误差值。 |
| 11 | `cartesianKuhnErrorJet_field_local_invariant` | `Spatial/CartesianKuhnErrorLocality.lean:82` | PASS；第 2 项将上一值身份提升至全部 `k : Fin 2` 弱字段；最终使用真实第一阶场。 |
| 12 | `cartesianKuhnErrorJet_local_stability` | `Spatial/CartesianKuhnErrorStability.lean:11` | PASS；全部原 H¹ 输入的单元缩放误差由实际裁剪块缩放 H¹ 范数控制，统一常数为原 Q_h 梯度稳定常数加 2。 |
| 13 | `cartesianKuhn_h2_local_error` | `Spatial/CartesianKuhnLocalError.lean:12` | PASS；原全 H²∩H¹₀ 状态，包括物理边界单元，得到同一实际 Q_h 的值及完整弱梯度 h² 局部误差；C 先于网格、h、单元和状态。 |

## 原文对应与范围

原 B.2 证明先选取 B.1 的物理边界相容仿射 p_K，利用原帽矩和边界节点零值得到 Q_hp_K=p_K，再将单元误差改写为 `(u−p_K)−Q_h(u−p_K)`。局部 L² 稳定性、有限元逆估计和 B.1 给无权局部 h² 界，之后才通过允许权局部比较和有限重叠求和得到完整加权全域 B.2。

本批完成上述无权局部误差步骤，且将值和梯度都实现为原真实弱 Sobolev jet 的字段。它没有把一般 H² 函数的节点值、额外光滑代表、目标误差估计、局部零迹或某个预先选好的局部梯度作为输入。

采用的邻域是已验收的实际加宽裁剪块 B_K⁺，并非原稿所写最小轴向 B_K。设中心 Cartesian 单元整数原点为 z，则其逐轴端点为 `max(o_j,o_j+(z_j−2)δ_j)` 和 `min(o_j+N_jδ_j,o_j+(z_j+3)δ_j)`。新结论右端确为该较大块上的原 Hessian L² 范数，不能将其改称最小块上的更强局部估计。已有宽度 δ_j 至 5δ_j、活动帽非零支撑容纳和统一重叠性质支持这一已记录的等价证明路线。当前仍未输出允许权或全域 B.2，保持 AUXILIARY 与 13/26 合理。

## 局部弱导数唯一性、测试族和闭单元

已直接读取 `SobolevJet`、`SobolevRealization`、`WeakDerivativeUnique`、`SubdomainRestriction` 和 `SimplicialLocalGradient`。原 jet 的每一阶为全部对称多重指标的实际 L² 欧氏字段，各阶之间逐坐标满足原完整 `SpatialTest` 分布弱导数身份。第一阶包含每个坐标一次，第二阶按原 D² 多重指标约定包含全部二阶分量，混合排列不重复计数。它不是自由指定的导数数据。

值注入性的旧证明从真实 L² 类的零值出发，逐阶利用完整紧支光滑测试的基本引理和弱导数唯一性证明每个字段为零。限制到子域时，每个子域 SpatialTest 都通过同一全空间光滑函数、紧支撑和支撑包含关系成为原域测试；函数及其真实导数在子域外为零，因此原弱积分身份确实传到子域。每个字段的限制由 MemLp 的测度单调性构造，并有明确 a.e. 代表身份。

第 1 项只要求 T⊆S 且 T 开。真正受限 L² 值与给定局部值 a.e. 相等后，Lp.ext 和开域上的值注入性给整个限制 jet 严格相等；不要求全局 S 开，也不额外要求 v 的梯度与 u 一致。

第 2 项在原 S 开且凸的前提下使用 `interior K⊆S`，把两个 jet 限制到开单元内部。闭 K 上的值 a.e. 身份经测度单调性限制到内部，然后第 1 项给整个 jet 相等。最后实际满维单纯形的 frontier 为 Lebesgue 零测集，使内部与闭单元的限制测度相同；由此恢复所有阶字段在闭 K 上的 a.e. 身份。没有将公共面或物理面上经典导数的逐点相等作为假设，也没有把闭 K 错误地包含到开物理域中。

第 5 项同样先删除真实单元零测边界，再以开单元内部包含原域、K∩Ω 包含于 B_K⁺ 得到 `volume.restrict K≤volume.restrict B_K⁺`。物理边界确实可能不在 B_K⁺ 中，这不妨碍该测度不等式。零维辅助接口由实际单纯形拓扑与测度定理处理，没有错误采用“所有空间单点零测”的假设；最终 h² 定理的实际维数为 d+1，覆盖原全部正维数。

## 同一 Q_h、真实误差及仿射不变性

直接核对了 `CartesianKuhnWeakInverse`、`CartesianKuhnLocalAffine`、`CartesianKuhnPatchProjection` 的实际定义与调用。Q_h 仍严格是原全部内部节点上的归一化帽矩 J_h 与实际有限帽和重构 R_h 的组合。`cartesianKuhnProjectionJet` 是已证明属于原 H¹₀ 的实际 R_hJ_h 重构 jet，其值等于同一重构 L² 类。输入 J_h 的空间是原全部 L²，所有帽配对已有真实可积性；此处没有换成正交投影或较小状态空间。

第 7 项首先在真实 L² 代表层使用已有 Q_h 减法身份及 `Lp.coeFn_sub`，再用开域上真实值注入性得到整个 jet 的减法身份。因此，即使原重构 jet 由存在性选择获得，其梯度也不能任意变化；新证明清偿了所需线性性。

误差 e 定义为 `u−projectionJet(value u)`，从而 value(e) a.e. 就是实际 u−Q_hu，field 1(e) 是其完整真实弱梯度。局部不变性辅助接口确实带有“p 的值在 K 上被 Q_h 再现”的前提，但最终定理内部供应该前提。它先证明 p 的误差值为零，再利用实际减法代表得到 e(u)=e(u−p) 的局部值身份；全部弱字段身份由上述开单元局部唯一性推出，不是额外假定。

最终定理从 T094 的同一 p 与局部残差 r 出发。通过真实仿射系数的满射，构造全原有界域上的 `affineBoxJet P`；其值严格等于此前再现结论使用的 `boundedAffineLp p`。已读取该 jet 的定义：它由真实仿射值、真实坐标导数和完整弱身份装配。p 作为真实仿射函数可以取节点值；一般 u 从始至终没有被取节点值。P 不需要属于全域 H¹₀，也没有将局部仿射函数按零延拓伪造成全域 H¹ 函数。

将原 H² jet 截断成 U 时，值和第一阶字段原样保留。全域残差 U−P 在 B_K⁺ 的值 a.e. 等于 T094 产生的实际局部 r 的值。第 1 项由此得到严格的 `restrictSubdomain(U−P)=r`，故不只值范数，完整第一阶字段的局部范数也准确等于 r 的对应 L² 范数。证明随后将单元误差不变性、误差稳定性和 r 的 B.1 误差界合法连接起来。

## L² 有限性、物理边界和统一常数

所有涉及 bochnerL2Norm 的量都是实际有限 L² 量。第 3 项以 MemLp 排除无穷 eLpNorm 的 toReal 总化问题；第 4 项从 Lp.memLp 和真实测度不等式供应局部差的可积性。后续原 jet 值、全梯度、Hessian 以及 Q_h jet 字段都属于原域 L²；B_K⁺⊆Ω 以及 K 的测度小于 B_K⁺ 供应全部局部资格。a.e. 代表替换均在相应限制测度下完成。

设 T095 的局部 Q_h 梯度稳定常数为 G>0。第 12 项对任意原 H¹ jet 使用实际常数 1 的局部 Q_h 值稳定性和真实测度单调性，得到值误差≤2 倍输入局部值范数、梯度误差≤输入局部梯度范数加 `(G/h)` 倍输入局部值范数。h>0 保证 `h·(G/h)=G` 精确抵消，故可选 A=G+2。该结论仅需 κ>0 和 δ_j≥h/κ，不附加 Dirichlet、H²、步长上界或目标误差前提。

第 13 项先固定 d 和 κ≥1，选取 A 及 T094 的 B>0，再选 C=A·B；其后才量化全部 o、δ、正步长证明、N、实际单元 i、h>0、`h/κ≤δ_j≤h` 以及全部弱 H² 状态。唯一边界要求是 `value u∈dirichletSubspace Ω`，即原紧支光滑测试在真实 H¹ 图拓扑闭包的标量实现。常数没有网格总尺寸、单元数、位置、h、状态、局部仿射系数或选取见证的依赖。

T094 所调用的实际局部 B.1 使用参数 5κ，宽度 δ_j 至 5δ_j 内部给出其全部尺度前提；其常数依然只依赖维数和原 κ。原全局 H¹₀ 经真实限制和连续面迹的闭核给局部物理面零迹，T094 内部获得 p 在所选整个物理闭面上的零值，并覆盖中心单元全部边界顶点、角点及多重面交线。当前最终接口没有留下零迹或边界节点假设。

最终结论的右端为 `C*h^2*bochnerL2Norm(volume.restrict B_K⁺)(field 2 u)`，确是同一原 Hessian 的真实局部范数，没有改成局部拟造 Hessian、归一化体积范数或全域更大范数。零状态和零 Hessian 不被排除，也不发生除以它们范数的步骤。κ=1 允许；h=0 按原正网格尺度明确排除。原 N_j≥2 的网格全部覆盖；若正维中有 N_j=0，则没有单元 i，类型自然处理空索引。辅助命题允许的更小有限网格没有削弱原量化范围。

## 已验收依赖与版本

已读取 [T094 独立验收报告](T094-local-acceptance.md) 和 [T095 独立验收报告](T095-local-acceptance.md)，并直接核查本次实际使用的上述类型与证明。依赖门槛均已通过，且固定代码未漂移：

- T094 / C110 的 `CartesianKuhnLocalAffine` 导入闭包 255 模块，与其已验收 SHA `fc89f7ab4516bb6dd97a43a2e5224e722b0b7a56` 逐字节相同。
- T095 / C111 的 `CartesianKuhnWeakInverse` 导入闭包 207 模块，与本次 base、其已验收 SHA `116908340801d3f1cd9f7e940304807f70bdb1ba` 逐字节相同。
- T093 / C109 的 `CartesianKuhnPatchProjection` 导入闭包 186 模块，与已验收 SHA `ba9aa5d2a3caf655bba037695fe733a3f292d952` 逐字节相同。
- `DirichletLocalAffine` 的 183 模块闭包与已审查的 T082 固定 SHA `59452751f05398e3446ed5305638a1e20dc89061` 逐字节相同；本批没有改动 B.1、真实面迹、弱 jet 或原 H¹₀ 定义。

四个新模块总 Carleman 导入闭包为 276 模块，272 个旧模块相对 base 全部不变，root 明确导入四个新模块。已读 AGENTS、治理和 state 协议没有变化；原论文、Lean/mathlib pin 及两个 CI workflows 相对 base 未改。原文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean pin 为 4.35.0，本机 mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。

## 实际构建、公理与同 SHA 远端证据

实际读取 `/tmp/carleman-kuhn-local-error-target.log`：定向构建 **3467 jobs** 成功；`/tmp/carleman-kuhn-local-error-full.log`：全库 **3792 jobs** 成功，并实际打印全库 **6177** 声明递归审计通过。新四模块没有 sorry、admit、新数学公理或 unsafe 证明。`tools/CheckAxioms.lean` 相对 base 只新增本批 13 项 #check 与 #print axioms；原全环境 `privateToUserName` / `collectAxioms` 递归审计保持不变，白名单仅为 `propext`、`Classical.choice`、`Quot.sound`。

本验收逐项读取固定本机产物的 13 项完整类型，每项均恰有一条对应类型与显式公理记录；所有 13 项均仅含三项正常基础公理。全文件实际有 2036 条带公理记录和 6 条无公理记录，合计 2042 条打印、2038 个不同声明名；扫描未发现白名单外公理。末行实际为 `Axiom audit passed for all 6177 Carleman declarations.`。显式打印数与递归环境审计数是不同统计，没有混为一谈。

已独立通过 GitHub connector 查询 [main CI run 39189061598 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39189061598/attempts/1)：event 为 push，branch 为 main，head 精确为 `ab5f74bf708c3bb969ecca40fcee8b26edd16d96`。run 最终 `completed/success`，updated_at 为 `2026-10-19T02:18:25Z`；三个实际 jobs 及各自步骤均成功：

| Job | ID | 最终状态与完成时间 |
|---|---|---|
| `state-check` | `117857613007` | `completed/success`，2026-10-19T02:15:06Z |
| `lean` | `117857613349` | `completed/success`，2026-10-19T02:18:16Z |
| `dashboard / snapshot` | `117858435362` | `completed/success`，2026-10-19T02:18:24Z |

远端 artifact 元数据中，`lean-ci-result`（ID `12158678525`）和 `lean-declaration-evidence`（ID `12159316155`）均未过期，均绑定同 run、main 和本次固定 SHA。最初受网络沙盒限制的下载重试后，本验收 Agent 已自行通过 `gh run download 39189061598` 成功下载两份原始 artifact。

独立读取 `/tmp/carleman-kuhn-local-error-main-ci/result.json`：status 为 PASS，checked_sha 与 source_head_sha 均精确为固定 SHA，ci_url 对应上述 run/attempt，targets 为 Carleman，finished_at 为 `2026-10-19T02:17:18.515092+00:00`。实际 Linux Lean 4.35.0 commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib commit 为上述固定 pin。

下载的 `/tmp/carleman-kuhn-local-error-main-axioms/axioms.txt` 与 `/tmp/carleman-kuhn-local-error-local-axioms.txt` 已独立逐字节比较，**完全相同**：**1,830,192 bytes**，SHA256 **`149d0b6f73ecf799bc14c1a5bf3676cf8c925d0c710212735eb1f4e6ad87c004`**。因此远端 13 项实际类型、公理依赖及全库 6177 声明递归审计均与逐项审核的固定本机证据完全一致。没有使用后续工作树 `.ci/axioms.txt` 或其他 SHA 的产物。

## 验收决定

**C112：PASS，可记录为 REVIEWED，scope 保持 AUXILIARY。** 未发现本批声称范围内的实际弱导数唯一性、闭单元测度、Q_h 身份、仿射不变性、完整原状态、边界处理、常数量词或局部 h² 误差方面需要修复的缺陷。同 SHA main 三项最终 CI 和自行下载的原始证据已全部独立核实。

这次通过只清偿无权局部误差步骤。允许权比较、全域加权组装、完整 B.2/P026、FD/P012 与其余原文义务不因本报告提升，原文仍 **13/26**。本 Agent 仅写此报告，未修改数学实现、台账、root、原稿，也未 commit/push。
