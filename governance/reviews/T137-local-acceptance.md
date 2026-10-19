# T137 / C153 / P020 独立本机验收

- checked_sha: `ac30cc21022f162809fdd7f88550a3fd58e5ad35`
- base_commit: `fe4cd0a34c2c118548b17ce534eae0f210bea70c`
- reviewed_at: `2026-10-19T08:10:33+00:00`
- reviewer: `/root/accept_spatial_foundations`，独立于实现者的本机验收 Agent。
- result: **PASS / PAPER**；axiom_check: **PASS**。
- 原命题：**Proposition 7.8 / P020 / `prop:filter-fd`**。
- 验收决定：C153 与 P020 可在本固定版本登记 REVIEWED / PAPER；仅增加 P020，原文覆盖可由 **15/26** 更新为 **16/26**，其它命题状态不由本报告改变。

本报告从固定 Git 对象读取六模块全部证明、27 项展开类型、原稿、T137 分析、MATH_SPEC 与台账，并独立核对关键依赖版本、同 SHA 三项正式 CI 及自行下载的原始产物。没有把执行者说明、旧辅助验收或 CI 成功单独视为原命题完成。仅新写本报告，未改实现、台账、原稿或根导入，未提交/推送；动态工作树和 `.ci/axioms.txt` 排除在证据之外。

## 全部 27 项声明

行号对应 checked_sha。Spatial 文件位于 `Carleman/Spatial/`，Geometry 文件位于 `Carleman/Geometry/`，最后一个模块位于 `Carleman/Control/`。声明 JSON 与固定 C153/P020 的清单一致；六模块全部由固定 `Carleman.lean` 导入，27 项均有 `#check @...` 和 `#print axioms ...`，原始产物逐项包含实际类型。

| # | 完整声明 | 固定源码位置 | 逐项核查 |
|---|---|---|---|
| 1 | `Carleman.linearRefinementBasis` | Spatial/TensorLinearProlongation:13 | PASS。对真实一维线性插值输入单个粗节点 Kronecker 数据，得到原节点基函数。 |
| 2 | `Carleman.tensorLinearProlongation` | Spatial/TensorLinearProlongation:16 | PASS。对全部粗内节点 a 求 u(a) 乘各坐标基函数之积；输入是完整粗节点函数空间。 |
| 3 | `Carleman.linearRefinementBasis_node` | Spatial/TensorLinearProlongation:20 | PASS。正整数细分下，每个粗节点精确恢复 Kronecker 值。 |
| 4 | `Carleman.uniformLinearProlongation_sum` | Spatial/TensorLinearProlongation:24 | PASS。实际商/余数线性公式与任意有限和交换。 |
| 5 | `Carleman.uniformLinearProlongation_const_mul` | Spatial/TensorLinearProlongation:31 | PASS。实际插值与实数倍交换，无有界性或可分离性限制。 |
| 6 | `Carleman.tensorLinearProlongation_zero_face` | Spatial/TensorLinearProlongation:36 | PASS。任意坐标等于 0 或 mᵣKᵣ 时整项为零，覆盖两侧所有面。 |
| 7 | `Carleman.tensorLinearProlongation_node` | Spatial/TensorLinearProlongation:53 | PASS。任意原粗内节点全部数据严格恢复，不仅恢复单个基向量。 |
| 8 | `Carleman.tensorLinearProlongation_slice` | Spatial/TensorLinearProlongation:71 | PASS。对任意状态及任意其它坐标，坐标截面恰为该截面粗节点值的一维线性插值。 |
| 9 | `Carleman.cartesianAxisFill` | Geometry/CartesianAxisSum:12 | PASS。由一个轴位置及其它全部坐标真实组装自然数格点。 |
| 10 | `Carleman.cartesianAxisFill_self` | Geometry/CartesianAxisSum:16 | PASS。组装点的指定坐标严格为输入 k。 |
| 11 | `Carleman.cartesianAxisFill_update` | Geometry/CartesianAxisSum:20 | PASS。更新指定轴与重新组装同一横截面一致。 |
| 12 | `Carleman.cartesian_sum_axis` | Geometry/CartesianAxisSum:28 | PASS。真实有限矩形节点和经 piSplitAt 双射精确分解为截面和与轴和。 |
| 13 | `Carleman.tensorLinearProlongation_line_inverse` | Spatial/TensorProlongationInverse:13 | PASS。每条真实截面零端点，一维估计给 12/(mᵣh)²；仅取消共同正 h。 |
| 14 | `Carleman.tensorLinearProlongation_direction_inverse` | Spatial/TensorProlongationInverse:36 | PASS。对全部横向节点求和，给同一方向完整差分能量界，无截面数量因子。 |
| 15 | `Carleman.tensorLinearProlongation_inverse` | Spatial/TensorProlongationInverse:54 | PASS。交换真实有限和后逐方向相加，常数为 ∑ᵣ12/(mᵣhᵣ)²。 |
| 16 | `Carleman.cartesianLatticeData_of_box_values` | Spatial/CartesianBoxValues:12 | PASS。闭盒自然格点的零边界值与原整数格点数据严格对应；边界和内部均处理。 |
| 17 | `Carleman.cartesian_sum_box_values` | Spatial/CartesianBoxValues:39 | PASS。去除实际为零的下侧面后，矩形和精确等于原内节点和。 |
| 18 | `Carleman.cartesianLatticeSuccessor_nat` | Spatial/CartesianBoxValues:51 | PASS。原整数前向格点等于自然坐标 update 后再转整数，无位移误差。 |
| 19 | `Carleman.cartesianCoarseProlongation` | Spatial/CartesianCoarseProlongation:14 | PASS。实际张量节点值通过原 valuesEquiv 进入同一物理细空间；真实加法与数乘保持。 |
| 20 | `Carleman.cartesianCoarseProlongation_values` | Spatial/CartesianCoarseProlongation:32 | PASS。每个细内节点的值严格为原张量插值公式。 |
| 21 | `Carleman.cartesianCoarseProlongation_mass` | Spatial/CartesianCoarseProlongation:38 | PASS。原物理范数平方严格等于 ∏hᵣ 乘矩形节点平方和，不用质量等价。 |
| 22 | `Carleman.cartesianCoarseProlongation_axis` | Spatial/CartesianCoarseProlongation:50 | PASS。原实际前向差商与张量值差商一致，包含 zᵣ=Nᵣ−1 到 Nᵣ 的末边。 |
| 23 | `Carleman.cartesianCoarseProlongation_energy` | Spatial/CartesianCoarseProlongation:73 | PASS。原 2d+1 差分算子的物理内积严格等于 ∏hᵣ 乘全部方向边差商平方和。 |
| 24 | `Carleman.Physical.cartesianCoarseFilter` | Control/CartesianFilterRayleigh:13 | PASS。F 定义为同一真实粗插值线性映射的 range。 |
| 25 | `Carleman.Physical.cartesian_coarse_energy_bound` | Control/CartesianFilterRayleigh:17 | PASS。精确质量/能量身份与张量逆界给原物理能量≤12∑Hᵣ⁻²乘原物理范数平方。 |
| 26 | `Carleman.Physical.fd_coarse_filter_rayleigh` | Control/CartesianFilterRayleigh:31 | PASS。对真实 range 中每个元素取原像，得到原 Rayleigh supremum 上界，包括零空间约定。 |
| 27 | `Carleman.Physical.fd_dividing_filter_rayleigh` | Control/CartesianFilterRayleigh:41 | PASS。直接接受原每轴整除条件，内部取 K=N/m；输出的实际线性映射由所有 u、所有细节点的精确张量公式确定，并满足原上界。 |

## 原文目标与最终量词

固定原稿 `paper/main.tex:2241`–2274 是 Proposition 7.8。它使用原 1650–1654 行 `eq:physicalFD` 的 2d+1 点 Dirichlet 差分算子，以及 1642–1646 行的对角质量 ω=∏hᵣ；F 为零边界粗节点值按张量分片线性插值后的像。2148–2152 行定义 Λ_F 为非零 F 元素的 Rayleigh 商上确界，并规定 Λ_{0}=0。目标系数精确为 12∑Hᵣ⁻²，Hᵣ=mᵣhᵣ。

第 27 项的实际完整类型量化任意维数 d、原点 o、全部正细步长 h、自然数轴分割数 N 与正整数 m，并要求每个 mᵣ∣Nᵣ。随后给出
`I : (CartesianInteriorIndex (N/m) → ℝ) →ₗ[ℝ] CartesianPhysicalState h hh N`，
同时要求每个粗状态 u、每个细内节点 a 都有精确张量公式，且
`filterRayleigh (cartesianPhysicalLaplacian o h hh N) I.range ≤ 12*∑r ((m r:ℝ)*h r)⁻¹^2`。

mᵣ>0 和 hᵣ>0 是原实际正粗细步长条件；整除关系通过自然数的精确乘除恒等式内部恢复 N=mK，未额外要求其它网格比、各向同性、维数上限或算子不变性。原盒长由 Nᵣhᵣ 确定，原点任意；结论甚至不使用原上下文的步长可比条件，故没有缩小原命题适用范围。原文引入的 H_c=max Hᵣ 不出现在本命题结论中，因此最终 Lean 类型直接保留每个 Hᵣ，未以另一个尺度替代原右端。

全部粗内节点函数都是允许输入；零边界由节点空间及基函数实现，不是额外选择的特殊状态。没有 H² 正则性、连续 CE、离散观测、目标能量界或谱分解前提。结论不含时间参数，常数 12 对网格、粗细比、状态和周期均没有依赖。

## 真实插值及存在映射的确定性

既有一维定义是
`uniformLinearProlongation m u k = u(k/m)+(k%m)/m·(u(k/m+1)−u(k/m))`。
T136 已证明其在每个完整闭粗单元上的线性公式，包括右端点；本次直接读取该证明及精确质量/能量公式，并核对其固定版本。

新 `linearRefinementBasis` 只把该实际插值作用于粗节点 Kronecker 数据；第 2 项再取所有内节点的有限张量基函数展开。每个一维因子在粗节点取 Kronecker 值，故第 6、7 项分别给全部边界面零值和完整粗节点恢复。这正是原张量分片线性插值在细节点的值，未混同于 Kuhn 单纯形上的分片仿射插值。

第 8 项把指定坐标基函数从乘积中分离，其余方向形成可依赖任意粗节点 a 的系数；有限和及实数倍与真实一维插值交换后得到整个截面身份。这里 u 是任意完整多维数据，不是假定 u 为各坐标函数的乘积，也未仅在可分离数据上证明能量界。

第 19 项通过原 `PhysicalFiniteSpace.valuesEquiv.symm` 构造实际线性映射；其底层保留每个节点值，物理内积由另一独立类型上的真实质量定义。第 27 项的存在量词没有留下可任意选择的替代映射：它直接提供第 19 项构造，并要求全部输入与全部细节点的相同公式。任意两个满足该公式的映射，经函数外延性与 valuesEquiv 的单射性必相同，range 也相同。边界节点本来不属于细状态坐标；其零延拓与张量边界公式另由第 6、16 项精确识别。

## 精确系数 12 与全状态张量求和

T136 的真实一维粗单元端点 a、b 满足
`mass=m(a²+ab+b²)/3+(a−b)²/(6m)`、
`energy=(b−a)²/m`。直接代数得
`(12/m²)mass−energy=3(a+b)²/m+2(a−b)²/m³≥0`。
乘回 h 后，物理质量是 H(a²+ab+b²)/3 加 h²/6 倍物理边能量，与原文一维质量修正一致；两端零值使梯形质量总和精确等于原内节点对角平方和。本批沿用已证有限和路线，不需要假定连续逆估计。

对每个轴 r、每个实际横向细节点 w，第 13 项以该截面粗节点值定义完整一维序列 v。第 8 项识别全部细值，第 6 项提供 v(0)=v(Kᵣ)=0。应用同一一维物理逆估计，再取消两边共同正 hᵣ，得到该线系数 12/(mᵣhᵣ)²。没有引入 Kᵣ 或线长因子。

第 12 项实际调用 mathlib 的 `Equiv.piSplitAt`，并通过其逆映射验证组装点的每个坐标。已读取固定 `Mathlib/Logic/Equiv/Prod.lean:491` 的定义：它把函数严格分成第 r 坐标与其余坐标，逆映射逐坐标恢复。故两侧矩形有限和是同一节点集合的一一重排，不是假设某个 Fubini 公式。第 14 项据此逐横向节点求和，第 15 项再逐方向求和，右端为 `(∑r12/(mᵣhᵣ)²)∑z V(z)²`。各向异性步长逐方向保留，不产生额外 d、节点数、张量质量谱界或 mesh-ratio 常数。

## 原物理质量、差分及边界

`CartesianInteriorIndex N` 是全部 `∀r, Fin(Nᵣ−1)`，物理节点对应 aᵣ+1。原 `CartesianPhysicalState` 的实际内积是 `(∏hᵣ)∑a f(a)g(a)`；已读取其 InnerProductSpace.Core 与 `norm_sq` 的证明，范数不是函数空间的 sup 范数。第 21 项只去掉矩形索引中的下侧零面，精确得到原内节点质量；上侧面在该半开矩形中本就未列入，且原值确为零。

第 16 项对闭盒节点逐点分为边界与内部：边界调用同一实际零延拓；内部明确构造 aᵣ=zᵣ−1 并证明其合法，原物理格点数据精确恢复 V(z)。第 18、22 项处理整数格点前向移动及自然数 update，并验证移动后的坐标仍≤Nᵣ。因此 zᵣ=0 的首边和 zᵣ=Nᵣ−1 到 Nᵣ 的末边均在能量和中，没有漏掉右端点。

旧 `cartesianPhysicalLaplacian` 的值正是 `∑r(2zᵢ−zᵢ₊ₑᵣ−zᵢ₋ₑᵣ)/hᵣ²`。第 23 项展开真实物理内积，应用已证明的离散分部积分边身份，再逐项用第 22 项替换，得到与张量差商平方和的严格等式。这里没有改成粗算子、投影算子或连续算子；也不需要原 Dirichlet H² 正则性。有限维自动连续性只用于把原实际线性差分算子装入 CLM，其算子范数没有进入最终常数。

第 25 项把张量界两侧乘同一 ∏hᵣ，并用严格质量等式恢复原范数；`∑r12/(mᵣhᵣ)²=12∑r((mᵣhᵣ)⁻¹)²` 是精确实数代数。没有质量等价损失，也没有时间或区域体积残余因子。

## 实际 Rayleigh 上确界与退化情形

`cartesianCoarseFilter` 定义上就是上述映射的 range；证明对 x∈range 取得真实 u 及 x=Iu，故能量界覆盖每个实际保留向量。旧 `filterRayleigh` 使用原 `rayleigh A x=⟨Ax,x⟩/‖x‖²` 和非零向量集合的 sSup，并单独将零子空间定义为 0。C151 的能量到 supremum 引理在 F≠0 时证明集合非空，对每个非零向量以严格正 ‖x‖² 除法，再取上确界；F=0 时使用非负右端。没有需要 A(F)⊆F 的步骤，也没有把 Rayleigh 上界偷换成特征子空间条件。

mᵣ=1 允许；任一 Kᵣ≤1 导致粗内节点空间为空时，实际粗状态空间只有零向量，range=0，原约定适用。Nᵣ=0 的更强退化情形也不引入非法除法；所有实分母只涉及正 mᵣ 与 hᵣ。d=0 时方向族为空、物理差分算子和右端均为零，状态由空乘积索引处理，证明无需伪造一个坐标。原通常的正维正盒情形全部包含。

因此新六模块完成 T136 原先缺少的多维张量、原物理算子/质量及真实 range 的连接，能够验收完整 Proposition 7.8。此决定只覆盖 P020，不自动完成完整 FD 数值实现命题、滤波控制定理、连续正则性或其它尚有义务的 PAPER 项目。

## 固定依赖及公理

六模块的 Carleman 递归 import 闭包为 331 文件，其中 325 个在 base 中存在，逐字节与 checked_sha 相同；另六个即本批新模块。关键已验收 declaration_version 的相关闭包也逐字节不变：

| 依赖 | 已验收版本 | 本次核对入口及闭包 |
|---|---|---|
| C152 / T136 | `fe4cd0a34c2c118548b17ce534eae0f210bea70c` | RefinedChainInverse，3 文件；并读取固定 T136 独立报告。 |
| C151 / T135 | `7ad1a9dd94d3abfe384564b1f24f351f5c60fe21` | FilterRayleighBound，12 文件。 |
| C126 所用实际物理对象 | `20523c258707a3864f45541d0eea83581360c86b` | CartesianPhysicalStiffness，316 文件。 |

C126 的其它数值接口保留的正则性前提并非本批定理输入；本批调用的是已经构造的实际物理空间、差分值和离散边配对恒等式。六模块全部新类型均已检查，无把待证 Rayleigh 或能量界作为前提。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，原文未改。

Lean 固定 4.35.0；mathlib 锁定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本次实际检查本地 mathlib HEAD 匹配且工作树干净。27 项的公理均为空或仅含 `propext`、`Classical.choice`、`Quot.sound` 的子集。独立解析完整原始文件的 2,501 条显式记录：2,492 条只含正常基础公理，9 条无公理依赖；无其它公理。递归审计末行为 **Axiom audit passed for all 7042 Carleman declarations.** 显式记录数与递归声明数未混用。

## 同 SHA 真实 CI 与独立下载

独立读取 [main run 39220063498 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39220063498/attempts/1)：event=push、head_branch=main，head_sha 精确为本报告 checked_sha；整体最终 completed/success，updated_at=`2026-10-19T08:06:41Z`。三个实际 jobs 均 completed/success：

| job | ID | 结果 |
|---|---|---|
| state-check | `117953016112` | success |
| lean | `117953016476` | success |
| dashboard / snapshot | `117954144317` | success |

本验收者使用 `gh run download` 独立下载该 run 原始产物：

- `lean-ci-result`，artifact ID **12171227749**，保存至 `/tmp/carleman-t137-tensor-main-ci/result.json`。
- `lean-declaration-evidence`，artifact ID **12171730668**，保存至 `/tmp/carleman-t137-tensor-main-axioms/axioms.txt`。

实际 result.json 为 PASS，checked_sha 与 source_head_sha 均为 `ac30cc21022f162809fdd7f88550a3fd58e5ad35`，target=Carleman，finished_at=`2026-10-19T08:05:30.636086+00:00`。CI Lean commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib_commit 与锁定值相同。

独立逐字节比较远端 axioms.txt 和固定 `/tmp/carleman-t137-tensor-local-axioms.txt`：完全相同，均 **2,165,149 bytes**，SHA256 **`cbb193ef1348054e358a3ed155a500878483f0f187abee4577b3f62accbca0a1`**。不是只对比执行者提供的摘要。

构建日志也按实际文件读取：`/tmp/carleman-t137-paper-target.log` 明确记录最终模块 CartesianFilterRayleigh 的 **3522 jobs** 成功；`/tmp/carleman-t137-tensor-full.log` 记录全库 **3941 jobs** 成功及 **7042** 声明审计。较早的 `/tmp/carleman-t137-tensor-target.log` 实际记录 **3318 jobs**，属于先前单模块定向构建，未将其误记为最终 3522。此处报告固定日志所见，不声称本验收另行重跑构建。

**最终签发：固定版本全部 27 项 PASS，完整 P020 / Proposition 7.8 为 PAPER PASS，无阻断缺陷。仅授权据此登记 C153/P020 完成；报告与 reviewed_at 在通知主 Agent 后冻结。**

