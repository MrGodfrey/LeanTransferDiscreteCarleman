# T108 / C124 独立本机验收

- `checked_sha`: `cd4c4c9e459a1757a027c36fd05fa3dbfd83fc92`
- `base_commit`: `513b40027762c901232372629409f0001dea82ab`
- `reviewed_at`: `2026-10-19T03:57:44+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**；同一原 FD 平方权测试在真实物理 Hilbert 空间上的算子范数导数、配对性质及完整 `Section4.WeightedTest` 组装。完整 FD/P012 不提升，原文保持 **14/26**。

本次直接从固定 Git 对象读取三模块全部源码与证明、14 项实际展开类型、`governance/analysis/T108-fd-weighted-test.md`、对应 MATH_SPEC 和关键依赖，对照原 `paper/main.tex` 的允许权及 `eq:qclass`（291–302）、原 `eq:graphnorms`（304–312）、N4（453–464）、FD 测试定义（1672–1676）和 Appendix B Step 3（2878–2889）。没有以执行者说明、规格或 CI 代替数学核查。自行查询同 SHA main CI、自行下载原始产物并逐字节比对；后续工作树的 `CartesianPhysicalStiffness` 等 T109 增量不属本次范围。

## 全部 14 项声明

名称省略公共前缀 `Carleman.`；位置相对于固定提交的 `Carleman/`。名单与交付 JSON、固定 C124/T108 台账逐项一致。

| # | 声明 | 固定位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `PhysicalFiniteSpace.multiplierFamily` | `Spatial/PhysicalFiniteDiagonal.lean:14` | PASS；有限节点系数到真实物理 Hilbert 连续算子的 CLM，值域使用物理空间的实际算子范数。 |
| 2 | `PhysicalFiniteSpace.multiplierFamily_apply` | `Spatial/PhysicalFiniteDiagonal.lean:35` | PASS；作用精确为逐节点乘 b_i，无坐标或质量重标定。 |
| 3 | `PhysicalFiniteSpace.multiplierFamily_hasDerivWithinAt` | `Spatial/PhysicalFiniteDiagonal.lean:38` | PASS；有限 Pi 导数与实际 CLM 的 Fréchet 链式法则给物理算子范数导数。 |
| 4 | `cartesianPhysicalTest` | `Spatial/CartesianPhysicalTest.lean:15` | PASS；真实物理全状态上的原 σ(x_i)² 对角连续算子。 |
| 5 | `cartesianPhysicalTestDerivative` | `Spatial/CartesianPhysicalTest.lean:21` | PASS；系数精确为 2σ_i²(τq′/q+ηρ_iq′)，第 8 项确认它是真导数。 |
| 6 | `cartesianPhysicalTest_values` | `Spatial/CartesianPhysicalTest.lean:29` | PASS；节点值严格等于 T102 已使用的同一原测试算子。 |
| 7 | `cartesianPhysicalTestDerivative_values` | `Spatial/CartesianPhysicalTest.lean:35` | PASS；节点导数严格等于既有原导数公式。 |
| 8 | `cartesianPhysicalTest_hasDerivWithinAt` | `Spatial/CartesianPhysicalTest.lean:42` | PASS；真实物理连续算子空间上的 HasDerivWithinAt，覆盖闭时间区间两个端点。 |
| 9 | `cartesianPhysicalTest_pairing_hasDerivWithinAt` | `Spatial/CartesianPhysicalTest.lean:52` | PASS；由算子导数、实际求值和内积微分推出任意固定状态的真实二次配对导数。 |
| 10 | `cartesianPhysicalTest_endpoint` | `Spatial/CartesianPhysicalTest.lean:63` | PASS；原 q(0)=q(T) 精确传给同一算子的端点相等。 |
| 11 | `cartesianPhysicalTest_symmetric` | `Spatial/CartesianPhysicalTest.lean:71` | PASS；任意独立 f、z 在实际物理内积中的对称身份。 |
| 12 | `cartesianPhysicalTest_pairing` | `Spatial/CartesianPhysicalTest.lean:83` | PASS；实际二次配对严格等于原物理加权节点能量。 |
| 13 | `cartesianPhysicalTest_nonneg` | `Spatial/CartesianPhysicalTest.lean:95` | PASS；正物理质量和真实平方和证明非负，无目标估计假设。 |
| 14 | `cartesian_weightedTest_interface` | `Spatial/CartesianWeightedTestInterface.lean:16` | PASS；先选统一阈值/常数，再组装同一实际 R/J 上的完整 WeightedTest，并明确指定 op 与 derivative 身份。 |

## 物理 Hilbert 算子范数中的真实导数

已直接读取 `PhysicalFiniteSpace` 的全部定义和实例：其内积为 `mass Σ_i f_i g_i`，正质量给正定性；`NormedAddCommGroup` 由这个内积 core 构造，`InnerProductSpace` 使用同一 core，`FiniteDimensional` 和 `CompleteSpace` 随后建立。实际范数平方严格为 `mass Σ_i f_i²`。`CartesianPhysicalState` 的质量是正的 ∏δ_j，指标为完整 `CartesianInteriorIndex N`。因此新测试值域的范数确是原物理范数。

第 1 项把 b 映到物理空间上的实际对角连续线性算子，再证明系数映射线性；有限维定义域使它成为真正 CLM。第 3 项先将每个坐标的 HasDerivWithinAt 合成有限系数向量的导数，再通过该 CLM 的 `hasFDerivAt` 和链式法则得到算子值路径导数。系数空间自身可使用标准有限 Pi 范数；导数结论的目标是物理 Hilbert 连续算子空间，使用该空间的算子范数。它不是仅逐状态的强导数，也不是只在原有限函数 sup 范数算子空间中求导。

有限维连续性只用于构造对象和应用链式法则，没有将其非显式连续性界用于统一数值估计。时间常数的证明始终通过原物理配对和原质量比较进行，未引入随网格、质量或节点数变化的范数等价常数。

原权 `σ_i=q(t)^τ exp(ηρ(x_i)q(t))` 的节点平方是实际测试系数。`TimeWeightRegularity.derivative` 伴随原 q 的真实 HasDerivWithinAt 和导数界，并非自由指定的候选 q′；已有 `ofContDiffOn` 从原闭区间 C² 数据供应它。q≥1 保证所有除法和实幂求导合法。逐节点允许权求导后再对平方求导，得到精确系数 `2σ_i²(τq′/q+ηρ_iq′)`，没有遗漏因子 2 或指数轮廓项。

第 9 项先用真实 CLM 求值微分于固定 f，再用真实物理内积的微分法则；f 的导数为零，故二次配对的导数正是 `(f,T′f)_X`，没有假定演化轨迹的时间导数。区间是 `Icc 0 g.period`，两个端点使用相对导数。第 10 项只使用原 q 的端点相等；报告不从这个较弱前提虚构全实线周期性。原周期延拓的 q 可使用已有周期身份，当前 WeightedTest 正确要求的是端点匹配。

第 11 项对两个独立状态展开实际物理内积，逐节点证明对称；第 12 项精确识别原加权平方和。第 13 项供应 WeightedTest 所需非负性。原 N4 的严格正定性和 `eq:test-norm` 已由既有 `cartesianSquaredWeightTest_positive` 与 `allowed_weight_cartesian_test_norm` 对同一节点公式证明：允许权在每个节点为正，正物理质量和非零状态给严格正配对。新节点身份及物理内积身份保持这些既有结论。`WeightedTest` 本身仅储存 Section 4 使用的非负性等字段，不将它误称为额外新增了正定性或 test-norm 字段。

## 同一 R/J、完整弱残差与逆权

最终对象的类型明确指定 `hdom ▸ cartesianReconstruction o δ hδ N`。已直接读取该 Reconstruction：R 是原实际 Kuhn 重构 L² 映射在原 `dirichletSubspace` 中的 codRestrict；J 是同一物理 Hilbert 重构的真实伴随，节点值等于原归一化帽函数积分。Q=RJ、G=JR 没有被替换成投影或恒等。域等式 hdom 将实际物理盒识别为固定 S，证明中的 `subst S` 消除这次运输，未改动 R/J。

构造局部 `T` 时，op 和 derivative 直接取第 4、5 项的 `.toLinearMap`；最终结论又给出两个函数的精确等式。所构造对象不是某个仅满足估计的未指定测试。endpoint、hasDeriv、symmetric、nonneg 字段分别调用同一算子的已证性质。

time_bound 将实际物理内积通过 `cartesianPhysicalState_inner` 化为原节点物理配对，直接调用 T102 对相同导数和相同重构的界。右端先为 `Ctime q(t)² ‖σR_hz‖²`，再用纯代数恒等改为接口中的 `Ctime (q(t)‖σR_hz‖)²`，无额外质量常数、时间尺度或状态限制。

superapprox 调用 T104 于完整原节点数据 `a↦z a`，得到真实 H¹ 弱 jet e，且其 L² 值类精确为 `R_h(T_hz)−(σ·σ)R_hz`。本批另取 V 中的 `v=R_h(T_hz)−conformingWeight σ hw (conformingWeight σ hw (R_hz))`。使用 `BoundedMultiplier.mul_map` 后，两者的实际 L² 值类相同；`WeakSobolevJet.value_injective` 在开域及真实受限 Lebesgue 测度上给出 **整个弱 jet** 的相等。第二次值单射性又把真实重构 jet 识别为 `domainSobolevJet (R_hz)`。

已核对值单射性证明确由完整弱导数身份和唯一性逐阶推出，并非将梯度定义成任意值字段函数；这里没有额外连续代表、H² 离散状态、节点取值正则性或目标梯度身份前提。残差方向是原论文的 `R_hT_hz−σ²R_hz`，并未错用早期未取负的节点残差。

接口中的 hw 是原 A2 乘法保持性用来在 V 内定义 `conformingWeight` 的参数。构造对每一份这样的 hw 完成 superapprox；最终 `∃T` 外层没有新增待验证的 hw 或残差成员资格前提。T104 的 e 本来是 H¹ jet，通过与上述 V 中实际残差的 jet 相等接入接口，未假定任意 H¹ 残差自动属于 H¹₀。

逆权使用 `ρ.scaled (-η)=(ρ.scaled η).neg` 的真实结构身份，幂同时为 −τ，因此正是 σ⁻¹。该小身份是从 `FullP1Superapproximation` 模块调用的内容，没有引入 P1 正交投影或该模块其他定理的假设。`conformingWeightedNorm` 是真实 `domainSobolevJet` 的 weightedNorm；m=1 时平方精确为 `q²‖σu‖²+‖σ∇u‖²`，故这里接入的是原完整 N 范数，而非零阶 L² 上界。右端系数保持 `Csuper*h*w.max`，没有变成 q(t) 的较小系数或反向残差。

## 原假设与统一量词

第 14 项先固定 d、开凸且闭包紧的原物理域 S、实际 ρ 及闭包 C² 性、正网格可比常数 κ、正 β 和非负 τStar，再选 ε>0 且 ε≤1、Ctime>0、Csuper>0。其后才量化全部原点、正步长、N、物理盒等于 S 的网格、h、TimeWeight、TimeGrid/周期、时间正则性 H、固定实幂 τ、两种符号 η 和完整状态。原矩形域、光滑轮廓、互比步长、q 类和允许权满足这些条件，没有附加较小状态族。

网格条件 `h/κ≤δ_j≤h` 精确表达原固定可比步长范围，h>0；原 h=max δ_j 的网格属于该范围。κ<1 等无可行正网格的参数不会制造错误结论，原可行 κ 范围照常覆盖。空内部指标及 d=0 的辅助类型没有非法除以节点数或 d；本批涵盖原 d≥1、N_j≥2 情形。

证明选择 `min 1 ε_super`，随后只从 hqmax≤ε 和 `w.upper t` 推出每个时刻 `hq(t)≤min 1 ε_super`。这同时供应时间质量界需要的 hq(t)≤1 和 T104 的空间阈值，没有对时间步长、周期或每个状态另加小条件。

Ctime 来自真实闭包点值界 R 和原统一质量常数 C₀，具体构造为 `2β(τStar+R)C₀`；Csuper 和 ε_super 来自固定 d、S、ρ、κ 的真实全状态超逼近。Ctime/Csuper/ε 均先于全部网格、周期、qmax、允许权、两符号及状态选择。原允许幂只需 abs τ≤τStar，符号只需 abs η=1；σ² 是实际测试系数和两次乘法，不据此扩大原允许权族。

## 依赖版本和完成边界

固定三模块的 Carleman 导入闭包共 **539** 文件；其中 **536** 个既有文件相对本批基线逐字节不变。三个新模块均已被固定 `Carleman.lean` 导入。进一步逐文件比较关键依赖的整个 Carleman 导入闭包：

- 物理空间 core 的 1 文件闭包，与 [T106 验收](T106-local-acceptance.md) 的 `337d9c1b8c5fadce4e638a2c96311e230ee94bb1` 一致；本次直接读取其实际范数、内积和完备实例。
- 实际 Reconstruction 的 315 文件闭包，与 [T107 验收](T107-local-acceptance.md) 的 `513b40027762c901232372629409f0001dea82ab` 一致。
- 时间估计的 310 文件闭包，与 [T102 验收](T102-local-acceptance.md) 的 `c749c4620eb0cba6f74a8a6ae58f6ce114645897` 一致。
- 全状态超逼近的 335 文件闭包，与 [T104 验收](T104-local-acceptance.md) 的 `29ebd0b76cccb70d6da4499eaa09d35cab2895ff` 一致。
- `Section4.TestData` 的 75 文件闭包，与已验收 Lemma 4.1 版本 `a315bdc449c58a705a982f0d009f1dde24d6af66` 一致；本次直接核对 WeightedTest 全部字段及其原假设来源。

原稿未改，SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本批完成原具体测试及全部 WeightedTest 字段，未宣称整个 A2、连续 CE 或完整 FD/P012 的其余数据已统一装配。未发现本批辅助目标新增未清偿数学前提或阻断性缺陷。

## 实际本机与同 SHA main CI 证据

独立读取 `/tmp/carleman-fd-weighted-test-target.log`：定向构建 **3751 jobs** 成功；`/tmp/carleman-fd-weighted-test-full.log`：全库 **3827 jobs** 成功，并记录 **6513** 项实际递归公理审计通过。

独立查询 [main CI run 39196739700 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39196739700/attempts/1)：head 为本次固定 SHA，分支 main，最终 `completed/success`，更新于 `2026-10-19T03:56:59Z`。已等待作业全部结束，没有把提前可下载的 PASS 产物当作整个 CI 已完成：

| Job | ID | 最终结论 | 完成时间 UTC |
|---|---|---|---|
| state-check | 117881036798 | success | 2026-10-19T03:52:46Z |
| lean | 117881036988 | success | 2026-10-19T03:56:45Z |
| dashboard / snapshot | 117881997687 | success | 2026-10-19T03:56:58Z |

自行下载的 `lean-ci-result` artifact ID **12161399006**，原始文件 `/tmp/carleman-fd-weighted-test-main-ci/result.json`：status PASS；`checked_sha=source_head_sha=cd4c4c9e459a1757a027c36fd05fa3dbfd83fc92`；目标 `Carleman`；`finished_at=2026-10-19T03:55:24.967216+00:00`；CI URL 与上述 run/attempt 一致。

自行下载的 `lean-declaration-evidence` artifact ID **12162002614**，原始 `/tmp/carleman-fd-weighted-test-main-axioms/axioms.txt` 与固定 `/tmp/carleman-fd-weighted-test-local-axioms.txt` **逐字节相同**：**1,925,576 bytes**；SHA256 **`29f62e38b53d318302863184a77f5478cd4895ecf8756ca9cef8189e3ce66229`**。两 artifact 的 workflow_run 元数据均为同一 main/head/run，未拼接后续 `.ci` 文件。

14 项各有一份完整类型打印及对应公理记录，全部仅使用 `propext`、`Classical.choice`、`Quot.sound`。全产物的显式记录是 2188 条非空公理打印和 8 条无公理打印，合计 2192 个不同显式名称；包含生成声明的实际递归审计计数为 **6513**，两者不混称。固定检查器对全部 Carleman 常量使用 `collectAxioms`，拒绝三项基础公理以外的依赖；其遍历和允许列表相对基线未改。未见 sorryAx 或额外数学公理。

原始结果记录 Lean **4.35.0**、mathlib **`56a005855ea17e0b0958f73ec801ae140b0a1679`**，与固定工具链和 manifest 一致；本机 mathlib HEAD 相同且工作树干净。治理协议和原稿相对前次已读取版本不变。此次仅写本报告，未修改证明、台账或提交。

## 验收决定

**C124 可升为 REVIEWED / AUXILIARY。** 14/14 项声明的原命题对应、真实物理算子导数、原节点配对、完整时间/空间字段、同一 R/J、全状态和常数量词均通过；没有需要修复的数学缺陷。完整 FD/P012 仍待其余数值数据装配，原文保持 **14/26**。本报告定稿后不再刷新验收时间。
