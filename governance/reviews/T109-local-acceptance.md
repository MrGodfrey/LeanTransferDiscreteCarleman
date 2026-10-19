# T109 / C125 独立本机验收

- `checked_sha`: `b1611e7c3fe37e6b3ed31556e932f61b657e2be1`
- `base_sha`: `cd4c4c9e459a1757a027c36fd05fa3dbfd83fc92`
- `reviewed_at`: `2026-10-19T04:04:47+00:00`（UTC；同 SHA 最终三项 CI 与原始产物核验完成时间）
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**。19/19 项显式声明通过；C125 可记为独立验收通过。原文覆盖保持 **14/26**，完整 FD / P012 不升级。
- 验收者：独立 Agent `/root/accept_section3`。本报告定稿后不再变更签发时间。

本次直接读取固定 Git 对象的三个新模块全部源码、19 项实际展开类型、关键依赖、原 `paper/main.tex` 和 `governance/analysis/T109-fd-physical-numerics.md`。没有以执行者说明或 CI 成功替代数学核查。自行查询同 SHA main CI、自行下载同次两份原始 artifact、实际读取结果并逐字节比较。本次只新增本报告；未改数学实现、台账或提交。工作树 `CartesianApproximationInterface` / T110、`CartesianNumericalData` / T111 未纳入验收。

## 原论文映射

核对原 Section 2 的数值数据和权同质性、N1–N4（`eq:massinterface`、`eq:reconstruction-norms`、`eq:stiffnessinterface`、`eq:loadinterface`、`eq:stateload`、`eq:test-norm`），以及 Section 6 的 FD 定义（1634 起，`eq:physicalFD`、原物理质量和状态/载荷/控制范数、`eq:fdstiffness`）。

本批把同一原差分算子作为真实物理 Hilbert 空间上的连续线性映射，证明其精确刚度、自伴和非负；把原节点权范数作为实际 seminorm 并证明在非零节点权下正定；将既有真实重构、同一载荷提升和同一平方权测试的估计写入这些实际物理范数。原全部状态和原物理质量保留。本批不声称已经完成 N3 或所有数值数据的最终统一组装。

## 19 项声明逐项验收

名称省略共同前缀 `Carleman.`，位置相对于固定提交 `Carleman/`。

| # | 声明及位置 | 独立核查结论 |
|---|---|---|
| 1 | `cartesianInteriorData_add` — `Spatial/CartesianPhysicalStiffness.lean:12` | PASS；实际节点数据在全物理空间的零延拓有限和保持加法，对任意 x 逐点成立，包含边界和域外。 |
| 2 | `cartesianInteriorData_smul` — `:22` | PASS；同一实际数据函数保持任意实数数乘，不依赖状态正性或额外支撑条件。 |
| 3 | `cartesianPhysicalLaplacian` — `:28` | PASS；在完整物理状态空间上逐值实现原差分式，用前两项证明真实线性，再由有限维性取得连续性。 |
| 4 | `cartesianPhysicalLaplacian_values` — `:61` | PASS；实际连续算子的节点值严格等于此前原 `cartesianFiniteDifferenceLaplacian`，没有改变差分模板或质量。 |
| 5 | `cartesianPhysicalLaplacian_stiffness` — `:66` | PASS；对任意独立 f、g，在原正维条件下，实际物理内积 `⟪A_h f,g⟫` 等于同一 `cartesianReconstruction.R` 的真实 Dirichlet `scalarForm`，没有质量零阶项或缺陷项。 |
| 6 | `cartesianPhysicalLaplacian_symmetric` — `:78` | PASS；把独立 f、g 的真实物理配对改写为同一坐标边差商乘积和，通过乘法交换律证明对称。 |
| 7 | `cartesianPhysicalLaplacian_adjoint` — `:91` | PASS；使用真实 `ContinuousLinearMap.adjoint` 及内积非退化性，由上一项推出 `A_h†=A_h`，不是仅给形式配对。 |
| 8 | `cartesianPhysicalLaplacian_nonneg` — `:101` | PASS；自身配对等于正物理质量乘全部坐标边差商平方和，逐项非负。 |
| 9 | `cartesianStateSeminorm` — `Spatial/CartesianPhysicalNorms.lean:14` | PASS；实际物理状态范数与真实节点权乘法线性映射复合，得到原节点加权 seminorm。 |
| 10 | `cartesianControlSeminorm` — `:19` | PASS；在实际 ω 内节点控制空间上作相同构造，沿用同一原物理质量。 |
| 11 | `cartesianStateSeminorm_apply` — `:25` | PASS；值严格等于实际状态权乘子作用后的物理 Hilbert 范数。 |
| 12 | `cartesianControlSeminorm_apply` — `:29` | PASS；值严格等于实际控制权乘子作用后的物理 Hilbert 范数。 |
| 13 | `cartesianStateSeminorm_definite` — `:34` | PASS；只要求每个实际状态节点权非零，范数为零等价于完整状态为零；通过乘子逐节点等式及真实节点线性等价证明。 |
| 14 | `cartesianControlSeminorm_definite` — `:49` | PASS；相同结论用于所有控制节点；没有要求控制节点集合非空或控制区域有正测度。 |
| 15 | `cartesianStateSeminorm_weight_scale` — `:65` | PASS；任意 `r≥0` 下，把权替换为 rσ 精确使范数乘 r；先证明实际乘子值等于 r 倍原值，再使用范数齐次性。 |
| 16 | `cartesianControlSeminorm_weight_scale` — `:78` | PASS；同一权同质性对完整控制空间成立，包括 r=0，覆盖原文 r>0。 |
| 17 | `cartesianPhysicalTest_positive` — `:92` | PASS；实际原平方允许权测试对全部非零状态严格正。允许权严格正性内部给出节点非零条件，精确节点能量正定性排除配对为零。 |
| 18 | `cartesianReconstruction_norm_sq_bounds` — `Spatial/CartesianPhysicalStability.lean:12` | PASS；同一真实 `RH` 满足 `(d+2)⁻¹‖f‖² ≤ ‖RH f‖² ≤ ‖f‖²`，物理范数与此前真实 L² 质量估计精确识别，常数仅依赖维数。 |
| 19 | `allowed_weight_cartesian_physical_stability` — `:19` | PASS；固定域及轮廓后先选同一个正 C，再量化全部网格、权参数和完整状态。该 C 同时控制加权重构双向平方范数、同一实际 load lift 的平方范数和同一真实测试配对与加权重构的双向界。 |

固定 `axioms.txt` 中上述完整类型依次从第 24961、24966、24970、24976、24980、24986、24991、24996、24999、25005、25012、25016、25021、25026、25031、25037、25044、25049、25054 行开始，均有实际递归公理记录。

## 原差分算子与精确刚度

直接核对 `CartesianFiniteDifference` 的定义：对每个真实内部节点 a，算子是

`Σ_r (2 f_a − F(a+e_r) − F(a−e_r)) / δ_r²`，

其中 F 是实际整数节点的零延拓数据，前驱和后继不是周期索引。`cartesianInteriorData_add/smul` 对全物理点成立，因此边界分支同样保持线性。`cartesianPhysicalLaplacian` 通过物理节点线性等价封装这一算子，没有另行定义一个只满足所需性质的抽象 A。

核对既有 `cartesianFiniteDifferenceLaplacian_pairing_edges`：原有限和按轴离散分部积分，两端 Dirichlet 零值消除边界项；全盒索引缩减到内部索引只去掉真实零项。得到的精确物理质量 `∏δ_r` 乘边差商配对，与实际 Kuhn 重构梯度的组装相同。本批直接调用该身份，对任意独立 f、g 得到对称性；取 g=f 得非负平方和。真实 Hilbert 自伴随后由 `adjoint_inner_left` 及 `ext_inner_right` 推出，使用的是此前直接从物理质量内积构造的 Hilbert 结构。

检查 `CartesianReconstructionLinear`、`CartesianMassAdjoint`、`CartesianReconstructionInterface` 与 `DirichletForm`：同一 `R` 是原帽函数重构的实际 L² 类，值域限制在已证明的真实 H¹₀ 子空间；`RH` 是其真实 L² 嵌入。`boundedDirichletOriginalForm.scalarForm` 来自真实全梯度 L² 内积，没有添加 `⟪u,v⟫` 质量项。形式身份只需要原 `d>0`、开且有界的物理盒；未添加 H² 椭圆正则性或更强算子域假设。本批证明形式刚度相等，不把这一点误称为完整连续椭圆正则性。

算子对称、非负和其余有限空间结论还允许 d=0 或空节点索引；此时相应空和正确。刚度形式声明显式使用 `0<d`，恰与原论文 `d≥1` 一致。原 `N_r≥2` 的所有网格和任意完整节点数据均覆盖。

## 物理范数、载荷与测试对象一致性

这里的范数沿用 `PhysicalFiniteSpace`：由 `mass Σ f_i g_i` 的正内积直接构造，`mass=∏δ_r`，实际平方范数严格为 `mass Σ f_i²`。新 seminorm 只是实际权乘子与该范数的复合，故其平方恰为原 `mass Σ σ(x_i)² f_i²`；控制空间相同但求和指标为 ω 内节点子类型。没有调用有限维范数等价来替代这些恒等式。

任意权可以产生 seminorm；第 13、14 项准确保留其正定所需的节点非零前提。原允许权 `q(t)^τ exp(ηρ(x)q(t))` 严格正，故该前提对原族内部可清偿，不缩小原状态空间。权同质性使用 r≥0，包括原要求的全部 r>0；r=0 不用于宣称正定性。

直接检查 `cartesianLoadInterface` 的实际类型：**F 就是同一 `CartesianPhysicalState` 类型 X**，Γ=id，lift 为同一 `cartesianKuhnLoadLiftLp`，兼容性由真实 `J(lift f)=f` 证明；已有右逆定理取 I=id。T109 的载荷界右侧使用的 p 与状态加权范数是同一个函数。因此原载荷加权范数确实按原文取为状态加权范数，`p(Iz)=p(z)`，状态到载荷界常数为 **1**；不存在由另一未知载荷范数推断同一性的缺口。当前文件提供这些组件，尚未将其包装为完整数值数据总接口。

`cartesianPhysicalTest` 是同一物理空间上逐节点乘以允许权平方的真实连续线性算子；参数顺序是 `ρ,w,τ,η,t`。新严格正性和最终稳定性均按这一顺序调用，与 `σ=((ρ.scaled η).multiplier w τ t).onSubdomain` 的节点值完全一致。其配对精确等于同一节点加权能量。非零状态严格正由能量为零 iff 状态为零推出，不是把非负性当作严格正性；空状态空间的非零前提相应为空命题。

有限维性只用于 A 的连续算子资格，未把可能依赖网格的算子范数或范数等价常数放进任何统一估计。

## 稳定性、常数和量词

无权结果把此前真实积分质量界严格改写为当前物理范数，保留精确常数 `1/(d+2)` 与 1。没有节点基数、长宽比或位置损失。

最终全允许权定理的五个结论是同一状态 f 上：

1. `p(f)² ≤ C ‖σ RH f‖²`；
2. `‖σ RH f‖² ≤ C p(f)²`；
3. `‖σ lift f‖² ≤ C p(f)²`；
4. `⟪f,Tσ f⟫ ≤ C ‖σ RH f‖²`；
5. `‖σ RH f‖² ≤ C ⟪f,Tσ f⟫`。

前后三者通过精确节点能量、`RH`、lift 和测试配对身份改写已有 `allowed_weight_cartesianKuhn_stability`，没有新增比较假设。独立检查其实际证明和 `CartesianKuhnWeightedNorm`：真实加权 L² 积分按单元精确相加，物理节点质量按实际顶点组装，因而没有单元个数损失；原固定 C¹ 轮廓在紧凸域的 Lipschitz 常数 L 给 `W=exp(Ld)`，可取共同平方界常数 `C=W⁴(d+2)`。局部权比较和锚点均在已有定理内部供应，非本批调用者额外假设。若写回原未平方范数式，只需取固定正平方根常数，统一性不变。

量词是固定 d、环境域 S 和轮廓 ρ 后，先 `∃ C>0`，再量化所有 o、正 δ、N、`Ω_g⊆S`、h、w、τ、t、η 和全部 f。只有 `h>0`、`δ_r≤h`、`|η|=1`、`h q(t)≤1`。原矩形取 `S=Ω_g`、`o=0`、`δ_r=L_r/N_r`、`h=max δ_r`，原 `h q_max≤δ_num≤1` 给时刻小量条件。两符号均包含；τ 全实数覆盖原指数范围；常数先于整个 TimeWeight，故对原周期 T 统一。此稳定性步骤不要求步长下界，是对原可比网格条件的加强，而非额外限制。

## 固定依赖与公理

递归导入闭包共 **324** 个 `Carleman.*` 源码文件，其中 **321** 个既有文件与基线逐字不变；三新模块均由固定 `Carleman.lean` 根目标导入。新增源码无 `sorry`、`admit`、`axiom`、`native_decide`。依赖顺序从已验收真实节点/质量/重构/载荷/测试组件到新物理算子和范数，未反向调用后续 N3 或数值数据总接口，无循环清偿。

三份治理文件、原稿、工具链和 mathlib 锁定文件与基线一致；全环境递归审计程序实现未变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定原始证据中 19 项清单完整。全文件可见 2207 个带公理的打印记录（2203 个不同名称）和 8 个无公理记录，全部依赖只含 `propext`、`Classical.choice`、`Quot.sound`。打印记录数不等于全部环境声明数；递归审计明确通过 **6545** 项 Carleman 声明，包括自动生成对象，无非基础公理。

## 同 SHA CI 和原始证据

独立读取 [main CI run 39197402706 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39197402706/attempts/1)。这是 main/push 运行，`head_sha=b1611e7c3fe37e6b3ed31556e932f61b657e2be1`，最终 **completed/success**，API `updated_at=2026-10-19T04:04:09Z`。

| Job | ID | 最终状态 |
|---|---:|---|
| `state-check` | 117883023378 | completed / success |
| `lean` | 117883023713 | completed / success |
| `dashboard / snapshot` | 117883706058 | completed / success |

验收者自行下载的原始 artifact：

- **12162895201**，`lean-ci-result` → `/tmp/carleman-fd-physical-numerics-main-ci/result.json`。
- **12161744050**，`lean-declaration-evidence` → `/tmp/carleman-fd-physical-numerics-main-axioms/axioms.txt`。

实际 `result.json` 为 `status=PASS`；`checked_sha` 与 `source_head_sha` 均为完整固定 SHA；目标 `Carleman`；`finished_at=2026-10-19T04:03:03.175212+00:00`。Lean **4.35.0**，Linux 构建提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib **56a005855ea17e0b0958f73ec801ae140b0a1679**，与固定配置一致。

远端 `axioms.txt` 与固定 `/tmp/carleman-fd-physical-numerics-local-axioms.txt` 已独立逐字节比对，完全相同：**1,935,658 bytes**；SHA256 **`b02354e8474428f9e08778bd69bb0742d2b7fa7f6b8f6874d049884bdc2a34e4`**。

固定 `/tmp/carleman-fd-physical-numerics-target.log` 实际记录 **3515 jobs** 成功；固定 `-full.log` 记录全库 **3830 jobs** 成功及 **6545** 项递归审计通过。未使用后续工作区 `.ci/axioms.txt` 代替固定证据。

## 最终判定

**19/19 PASS，无需修复的数学、类型、量词、公理或版本绑定问题。** 本阶段真实刚度、自伴/非负、原权范数及齐次性、测试严格正性、原重构/载荷/测试统一稳定性均可验收。

C125 保持 **AUXILIARY**。N3 和全部数值接口的最终组装不属于本次完成范围，不能据此宣布完整 FD / P012 完成；原文覆盖保持 **14/26**。
