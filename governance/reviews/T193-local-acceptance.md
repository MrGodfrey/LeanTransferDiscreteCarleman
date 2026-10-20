# T193 / C209 — 原差分取样测试一致性独立验收

- checked_sha: `3ac3635f878b0c1521032b396a2630acdcc4da46`
- base_commit: `560e3aa8d23c22943b51dd7744da8174944b27ef`
- reviewed_at: `2026-10-20T01:56:57+00:00`
- reviewer: `/root/accept_spatial_lemma`，独立本机数学验收
- result: **PASS，18/18 声明；AUXILIARY，原文覆盖保持 17/26**
- evidence_source: **local**。依据本轮用户通过主 Agent 明确传达的流程调整，远端 CI 是后台环境复现，不再是本批签发前提；下文区分本地验证与已经看到的远端状态。

直接读取固定 Git 对象中的三模块全部源码、固定 raw 中全部展开类型、公理记录、T193 分析、MATH_SPEC、原稿及相关协议；并检查关键依赖的实际证明。未把执行者说明或构建成功当作数学验收。原稿 `paper/main.tex` SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与原版本一致。

## 逐项声明

下表名称均位于 `Carleman` 命名空间；行号属于 checked_sha。三项 def、十五项 theorem 与 `/tmp/carleman-t193-fd-tests-declarations.json` 精确一致，均有对应完整 `#check @...` 和公理记录。

| 模块与源码行 | 声明 | 实际核查与结论 |
|---|---|---|
| CartesianTestInterpolation:16 | `cartesianNodalSample` | 真正全部内部索引上的函数取值，经物理有限空间等价映射构造；PASS |
| 同上:20 | `cartesianNodalSample_apply` | 每个原内部节点的精确取值身份；PASS |
| 同上:24 | `cartesianInteriorData_test_vertex` | 每个真实 Kuhn 顶点上，内部取样或边界零延拓都等于原测试值；PASS |
| 同上:37 | `cartesianKuhnReconstructionLp_test_eq_nodal` | 实际 R_h 的 L² 类等于该网格的原节点插值类；PASS |
| 同上:46 | `cartesianBoxKuhnPartition` | 仅由真实盒端点等式运输同一个有限网格；PASS |
| 同上:51 | `cartesianBoxKuhnPartition_faceMatching` | 原公共面匹配内部供应；PASS |
| 同上:58 | `cartesianBoxKuhnPartition_boundaryFitted` | 原边界适配内部供应；PASS |
| 同上:65 | `cartesianBoxDirichletState_test_eq_nodal` | 原 R_h 状态与节点 H¹₀ 状态完全相等，含弱梯度；PASS |
| 同上:83 | `cartesianBoxKuhnPartition_maxDiameter_le` | 实际有限最大直径 ≤(d+1)h；PASS |
| 同上:91 | `cartesianBoxKuhn_uniform_inballs` | C 仅依赖 d、κ，先于域/网格/h，提供真实正内球与直径比；PASS |
| CartesianTestStrongConvergence:13 | `cartesian_test_H1_strong_convergence` | 从原步长比及 h→0 得实际 R_h I_hψ 的完整 H¹₀ 强极限；PASS |
| 同上:36 | `cartesian_test_cell_L2_strong_convergence` | 原 E_h−R_h 误差加上已得梯度强收敛，推出实际 E_h I_hψ 的 L² 强极限；PASS |
| CartesianTensorTestConsistency:13 | `cartesianBoxDirichletLinearMap` | 原 chosen R_h 状态本身线性，未另选状态；PASS |
| 同上:45 | `cartesianBoxDirichletLinearMap_apply` | 上述线性映射与原 R_h 状态的精确身份；PASS |
| 同上:49 | `cartesianNodalSample_finite` | 完整有限张量的实际取样等于取样有限和；PASS |
| 同上:60 | `cartesian_finite_time_test_H1_consistency` | 原前层取样及完整物理差商经 R_h 的真实 Bochner H¹₀ 强极限；PASS |
| 同上:91 | `cartesian_finite_time_test_cell_L2_consistency` | 同一前层取样及差商经 E_h 的真实 Bochner L² 强极限；PASS |
| 同上:122 | `cartesian_finite_test_endpoint_consistency` | 原 E_h I_h 的固定时刻 L² 极限，适用于 τ=0、T；PASS |

## 原文忠实性与关键证明

原 FD 定义（`paper/main.tex:1630` 起）采用全部内节点 `1,…,N_j−1`、零边界值、同方向 Kuhn 重构、物理质量 `∏δ_j`，并假设各方向步长互相可比。本批 `CartesianInteriorIndex N = ∀j, Fin (N j−1)` 连同实际点坐标准确覆盖这些节点。`h/κ≤δ_j≤h` 使用整个序列固定的 κ，正是原可比条件的定量形式；取原 h=max δ_j 即可满足上界。没有加入嵌套、分级极限、空间与时间步长耦合。

顶点身份的内部分支由整数坐标的严格上下界实际构造原内节点索引；外部分支调用零延拓和 `SpatialTest.support`，在每个相应顶点得到严格零值。因而没有忽略首末层、边界条带或仅在 a.e. 意义下擅自求节点值。取值对象是原紧支光滑测试的实际函数，不是任意 L² 等价类。

R_h 的 L² 身份通过真实 nodalLp 得到；随后 `conformingEmbed_injective` 经 `SobolevHilbert.value_injective`、完整弱导数唯一性，识别同值的两个 H¹₀ 状态。开盒和 `volume.restrict` 内部清偿开域及 a.e. 支撑条件，未要求额外光滑代表或假设梯度相等。该身份也用于 R_h 线性证明，线性映射的 `toFun` 就是原状态，不会更换 chosen jet。

真实参考单纯形内球经坐标置换、正对角伸缩给统一形状常数；参考半径只依赖维数，C 可取 `(d+1)κ/r₀`。同一固定盒的 dependent transport 不改变网格、测度或状态。`maxDiameter≤(d+1)h` 给直径趋零，T192 的实际节点值及全部弱梯度估计因此适用于原 R_h。使用的是完整 H¹ 图范数，不是仅值域范数。定义和证明也允许空有限索引/零维情形，没有借用未声明的非空单元或正体积前提；原 d≥1、N_j≥2 当然包含在其范围内。

E_h 一致性使用已经证明的真实误差 `‖E_hz−R_hz‖₂≤C_d h‖∇R_hz‖₂`。复查其点态证明：a.e. 最近格点是当前 Kuhn 单元顶点；内部及边界条带都由原零延拓处理，再用当前仿射多项式的真实导数控制。T193 中梯度映射连续，使梯度范数收敛到有限极限，故 h 乘该范数趋零；没有额外统一梯度预算或预设 E_h 一致性。

原 `eq:conv-test-consistency` 及其相邻三条测试结论位于原稿 `2926–2956`。最终声明取固定盒、固定 T；η、f 在整个 Icc[0,T] 连续，且 `HasDerivWithinAt η (f t) (Icc 0 T) t`，故覆盖原 C∞ 时间测试且不要求区间外延拓。实际时间单元是 `(t_i,t_{i+1}]`，取样为 t_i，完整差商是 `dt⁻¹ • (I_hφ(t_{i+1})−I_hφ(t_i))`；原整个有限和经过线性身份进入 T191，不是仅断言各形式因子的差商。T191 的区间内 FTC、真实单元平均、Lp 代表及连续双线性 `timeTensor` 保证其极限就是实际时间导数张量。空间强极限在本批最终定理内部供应，未留下 T191 的抽象空间收敛前提。h→0 与 dt→0 独立。T 固定，未声称这些测试常数对任意 T 统一。

固定端点结论对任意固定 τ 成立，因此覆盖 0、T；它是光滑测试的端点一致性，不是离散解或极限弱解的状态迹定理。R_h 的前层强极限和 E_h 差商/端点极限符合原要求；E_h 前层目前只证明 L²，**原产品 L∞ 测试误差、最终势乘积、极限 PDE 和状态端点仍未清偿**。没有将本批提升为完整 P021。

## 依赖和公理

递归检查三个模块的项目 import 闭包共 369 个文件，其中 366 个既有文件与数学基线逐字节一致。关键闭包分别与已接受版本核对：T192 `P1TestStrongConvergence` 146 个文件；T191 `TensorTimeTests` 69 个；T188 `CartesianDirichletReconstruction` 352 个；T187 `FixedBoxKuhnConsistency` 344 个；T186 `CartesianCellKuhnConsistency` 339 个；C022 `WeakDerivativeUnique` 18 个，均无变动。关键证明已实际读取，未仅引用旧报告。T192 冻结报告提交 `739f92b05f7169e03dc1c917630d89ba40e7511d` 已完整读取并与工作树逐字节核对。

三个模块均由固定 `Carleman.lean` 导入，18 项均由固定 `tools/CheckAxioms.lean` 检查完整类型及依赖公理。固定 raw 中本批每项仅依赖 `propext`、`Classical.choice`、`Quot.sound`；全部显式公理记录无越出该集合者，无 `sorryAx`。实际递归检查通过 `privateToUserName` 覆盖整个 Carleman 命名空间，包括依赖中的 private 辅助及自动生成声明，末行确认 **8656 项 PASS**。

## 固定本地证据与远端记录

独立读取并校验以下本地文件；正式日志显示实际构建成功，不采用早期 probe 日志。固定受检源码清单的 944 个条目逐一与 checked_sha 的 Git 字节核对，全部匹配，覆盖 tracked Lean 源及三个工具链/构建配置文件。因此本地证据与本次数学版本相对应；同时的治理修改及未来实现没有进入审查。

| 证据 | 实际结果 / SHA256 |
|---|---|
| `/tmp/carleman-t193-target1.log` | 3569 jobs 成功；269 bytes；`3df6c46cdd2f471b29aaa62d33e2df26fa45e4cc18cb7719b67d3bd47c3c4991` |
| `/tmp/carleman-t193-build.log` | 全库 4179 jobs 成功；80 bytes；`2c3aa54d9374711601d410bf49241506a70d3c5ce7b7d59fb5de355b326eced5` |
| `/tmp/carleman-t193-axioms.log` | stderr 0 bytes |
| `/tmp/carleman-t193-fd-tests-local-axioms.txt` | 2807170 bytes；8656 项；`70fc5b59c3872591d07d063eec37df738f79c9461cebfbbc2542dbf859b8ea23` |
| `/tmp/carleman-t193-local-source-manifest.txt` | 944 条，102265 bytes；`a2ea189a3ec98b1605f26fda7a7b8e85b72ba6da14c48759cec6d1044a509195` |

远端已独立发现 exact-SHA 的 [run 39355636405](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39355636405)。本审查取得的快照中 `state-check` 118409639841 已于 `2026-10-20T01:50:33Z` success，`lean` 118409639673 当时仍 in_progress，尚无 dashboard job 和工件。未核验远端最终状态，也未下载远端 raw；本报告不宣称远端三项成功。按用户更新的规则，本次正式数学 PASS 依据上述固定本地验证和独立语义审查签发，无需等待后台 CI。

结论：本批原 FD 测试取样、真实 R_h/E_h 的所述强一致性全部通过，未发现阻断缺陷或新增目标估计前提。保持 AUXILIARY、17/26，剩余原文义务如上。仅提交本报告；签发后正文与 reviewed_at 冻结。
