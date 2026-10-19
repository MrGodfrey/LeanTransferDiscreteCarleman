# T110 / C126 独立本机验收

- `checked_sha`: `20523c258707a3864f45541d0eea83581360c86b`
- `base_commit`: `b1611e7c3fe37e6b3ed31556e932f61b657e2be1`
- `reviewed_at`: `2026-10-19T04:14:32+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原 B.2 到实际 WeightedApproximation 的连接，以及同一原 FD 算子、质量、载荷、控制和权范数的 NumericalData 组装；实际闭形式定义域 D(A)⊆H² 仍为显式原 A1 前提。未证明具体 H² 正则性，不提升完整 FD/P012 或 PAPER，原文保持 **14/26**。

独立从固定 git 对象读取两模块全部证明、四项完整展开类型及关键依赖，对照原 `paper/main.tex` 的 `eq:graphnorms`、A1、N1–N5、`lem:fd-weighted-approximation`/`eq:fdapproxallD` 及其后推出 N3 的段落。已读取固定 T110 分析和 MATH_SPEC。执行者规格及 CI 没有替代数学审查；工作树 T111 和其他未来模块、变化中的 `.ci` 产物均排除。

## 全部四项声明

名称省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付 JSON、固定 C126 台账一致。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `cartesian_heat_error_from_b2` | `Spatial/CartesianApproximationInterface.lean:15` | PASS；由真实 B.2 值/梯度和式及 hq≤1，保留完整 q 因子，得到 Nσ(e)≤Ch Rσ(u) 和 L²≤Ch² Rσ(u)。 |
| 2 | `cartesian_weightedApproximation_interface` | `Spatial/CartesianApproximationInterface.lean:51` | PASS；同一实际 Q_h 及弱导数唯一性识别误差 jet，对全部 D 中元素和全部时刻供应 WeightedApproximation 两字段，C 先于网格、D、周期和权族。 |
| 3 | `cartesianErrorScales` | `Spatial/CartesianNumericalData.lean:19` | PASS；精确 aE=C h、a₀=C h²、ηA=0，三项非负性内部证明。 |
| 4 | `cartesian_numericalData` | `Spatial/CartesianNumericalData.lean:27` | PASS；先选统一阈值和常数，再组装同一实际闭形式、物理 Laplacian、R/J、lift、B* 和物理权 seminorm 的 NumericalData；hD 明确保留。 |

## B.2 到完整 H¹/q 逼近范数

已读取 `WeakSobolevJet.parameterNorm`、`weightedNorm_le_parameterNorm` 和既有真实弱 jet/字段定义。对 m=1，论文 N 范数为

\[
\mathcal N_\sigma(e)=\bigl(q^2\|\sigma e\|_2^2+\|\sigma\nabla e\|_2^2\bigr)^{1/2},
\]

对二阶 jet u，parameterNorm 正是原 R 型和式 q²‖σu‖₂+q‖σ∇u‖₂+‖σD²u‖₂。最高阶字段是全部二阶分量的真实 L² 场，不是一个形式上的标量界；其加权范数是该非负和式的一项。

第1项先由真实有限平方和与和式的比较得到 Nσ(e)≤q‖σe‖₂+‖σ∇e‖₂。再将其乘以严格正 h，利用 hq≤1 得

\[
h\mathcal N_\sigma(e)
\le hq\|\sigma e\|_2+h\|\sigma\nabla e\|_2
\le\|\sigma e\|_2+h\|\sigma\nabla e\|_2
\le Ch^2\|\sigma D^2u\|_2
\le Ch^2\mathcal R_\sigma(u).
\]

以 h>0 合法消去 h，得 Ch Rσ(u)。L² 界由丢去原 B.2 左侧非负梯度项给出。没有把 Nσ 当作单独 L² 范数，没有遗漏 q，也没有利用 h≤1 冒充 hq≤1；不除以 q、C 或状态范数。辅助声明的 B.2 不等式是明确输入，但第2项通过已验收实际 B.2 定理内部证明它，最终接口不再要求目标误差界作前提。

## 同一实际 Q_h、canonical jet 与原域范围

第2项从固定 S、ρ 的闭域 C¹ 正则性及 κ≥1 取得 B.2 的统一 C，之后才量化所有正可比步长网格、h、D、时间权、时间网格、τ、η 和状态。原正维数表示为 d+1，覆盖论文任意固定正维数。hdom 令网格物理盒恰为原固定 S，没有随网格缩域；h/κ≤δⱼ≤h 是原步长可比条件。

输入 D 是任意 L² 子空间，显式要求 D⊆H² 和 D⊆H¹₀。对每个 v∈D，`domainSobolevJet` 从原 L² 元素及真实 Sobolev 子空间的双射取得二阶弱 jet，value 严格为 v。其一阶截断进入实际 `cartesianKuhnErrorJet`；该 jet 是截断 u 减去同一实际 Q_h 的弱重构 jet。

证明使用 `cartesianReconstruction_QH` 把接口中的 R_hJ_h 与先前 B.2 的 `cartesianKuhnProjectionLp` 严格对齐，然后以原开放域上的 `WeakSobolevJet.value_injective` 证明该误差 jet 等于

\[
\operatorname{domainSobolevJet}\bigl(\operatorname{inclusion}(v)-R_hJ_hv\bigr).
\]

这是完整 jet 的等式，因而实际所有弱一阶导数一并对齐；没有只对齐 L² 值而任意指定梯度，没有假设 v 有节点点值。v 的 H¹₀ 成员由 hDV 提供，实际 Q_h 的 H¹₀ 重构资格已内部构造，因此差确实属于原 V。

原 hqmax≤1 与 h≥0、q(t)≤qmax 给每个时刻的 hq(t)≤1。B.2 在全部真实时间上提供界，随后直接填入 WeightedApproximation 对整个闭周期 [0,T] 的 energy 和 l2 字段。结论保持 aE=Ch、a₀=Ch²；两个字段的右侧均为同一 v 的实际 Rσ 参数范数。没有加入时间轨迹正则性、额外可积性或节点采样条件。

第2项对任意实 τ 和 |η|=1 成立，覆盖原 |τ|≤τStar 和两种指数符号。C 在 D、w、g、τ、η、时刻和状态之前，故不依赖周期 T 或时间/空间节点数。

## 真实闭形式定义域与保留的 A1

第4项的 a 是 `boundedDirichletOriginalForm`：原 H¹₀ 图闭包的 Sobolev Hilbert 拓扑，真实全梯度 L² 配对，实际稠密性和 Poincare 强制性。已读取 `OriginalForm.model`、`domain_le` 和原变分关联身份；其 domain 是此闭形式的完整关联算子定义域，不是新定义的 H²∩H¹₀ 缩域，也不是任意替代算子。

最终展开类型明确量化

`hD : a.model.domain ≤ sobolevSubspace (d+1) 2 (volume.restrict S) S`。

这是原 A1 中 D(A)⊆H² 的集合包含部分，仍须由连续解析结果提供。原 a.domain_le 已内部证明 D(A)⊆V，用于调用第2项；不需要另加 Dirichlet 成员假设。本批没有证明具体 Dirichlet 算子的 H² 正则性或 A1 的椭圆定量估计，也没有将 hD 隐藏在数值稳定性字段中。即使后续可从原正则性定理供应 hD，本报告也只验收当前带显式前提的 AUXILIARY 结论。

## NumericalData 的各实际字段及统一常数

完整类型固定 a、原域/轮廓、κ、β、τStar 和观察区域后，先给 ε>0、ε≤1、Ctime>0、Csuper>0、Capp>0、Cnum>0，再量化所有 o、δ、N、h、hD、TimeWeight、TimeGrid 及原 `TimeWeightRegularity w g β`。这些常数在网格和周期之前；原光滑轮廓供应 C²/C¹，β>0、τStar≥0 与原范围一致。

实际选择为 ε=min(εtest,h₀)，其中 εtest≤1 来自同一测试接口，h₀ 是同一观察几何阈值。由 q≥1 和 q≤qmax 得 qmax≥1，所以 h≤hqmax≤h₀；同时 hq(t)≤hqmax≤ε≤1。观察和各权比较的小量前提均内部清偿，没有独立追加 h≤h₀ 条件。误差尺度为同一 Capp h、Capp h²、0。

各字段已逐项检查：

- **stiffness/defect**：A 是同一原零边界 (2n+1) 点物理 Laplacian（n=d+1），使用同一物理 Hilbert 内积及 R；真实 Dirichlet scalarForm 的精确刚度身份给 b=0，缺陷界严格为零，没有用一个任意自伴矩阵代替。
- **approximation**：分别把 Bool 两符号化为 η=±1，利用 `scaled_one`/`scaled_neg_one` 对齐 signed 轮廓，在完整实际 D(A) 上调用第2项。没有截断原允许 τ 范围。
- **test**：从已证 `cartesian_weightedTest_interface` 选择其实际对象。该存在结论还证明 op 恰为原 σ² 节点对角测试、derivative 恰为原导数；选择没有换成任意测试。端点、实际时间导数、对称/非负及真实空间超逼近来自同一对象。
- **reconstruction_upper/lower 与 lift_bound**：调用同一实际物理稳定性定理，R/J/lift 与 T107 对象严格一致。状态和载荷 seminorm 都是同一物理 X_h 中节点乘权后的真实 Hilbert 范数；F=X、Γ=Id 和实际 L² lift 没有改变。
- **observation_bound**：Bstar 明确为真实节点零延拓 CLM 的 Hilbert adjoint，使用原控制节点子空间及其物理质量范数。连续观察仍是原区域 ω₀ 上的实际 L² 观察，未替换为未识别的线性观测。

质量/载荷界原常数 Cm 已是平方界常数；观察界原为 norm≤Co·norm，代码在两边非负下平方得到 Co²。选择 Cnum=Cm+Co²>0，以 Cm≤Cnum、Co²≤Cnum 和真实范数平方非负性扩大三类界，没有误用 Co 代替 Co²，也没有产生 T、节点数或有限维范数等价损失。

精简 `Section5.NumericalData` 的质量、载荷、观察字段按定义存储基本 θ=ρ.multiplier(w,0,t) 的节点平方界；其 approximation/test/defect 字段显式遍历全部两符号和 |τ|≤τStar。调用来源的实际稳定性与观察定理本身保留全允许权族。不能把基本 θ 字段误读成已在该字段中量化所有 τ/η，也不能据精简记录忽略原 N1/N4 的额外要求：重构单射、A 的真实自伴/非负、测试严格正定及测试质量等价已在此前实际声明单列证明。本批没有重新定义这些要求。

`WeightedTest.superapprox` 沿用原接口的乘权保 V 参数 hw，以便表达 V 中的乘积；这属于连续 A2 的接口，不是本批新加的数值误差假设。本批也没有因此宣称完成全部连续 A1/A2 或整个 PAPER FD。空间数据和常数不依赖离散时间方向；两符号完整保留，真实原状态没有频谱或支撑缩小。

## 固定依赖与本机构建、公理证据

两模块的 Carleman 导入闭包共569模块，567旧模块与 base 完全不变，新增恰为本批两模块。又逐模块比较关键已验收版本：C113 `AllowedCartesianKuhnError` 的283模块闭包相对 `a9ca6fccf19cc677a4a60b07f373eb533df9d502` 不变；C123 `CartesianReconstructionInterface` 的315模块闭包相对 `513b40027762c901232372629409f0001dea82ab` 不变；C124 `CartesianWeightedTestInterface` 的539模块闭包相对 `cd4c4c9e459a1757a027c36fd05fa3dbfd83fc92` 不变；C125 `CartesianPhysicalStiffness`/`CartesianPhysicalStability` 的316/323模块闭包相对 base 不变；C122 `CartesianHilbertObservation` 的312模块闭包相对 `337d9c1b8c5fadce4e638a2c96311e230ee94bb1` 不变；C056 `DirichletForm` 的49模块闭包相对 `4f669626b3228adea39a16fbf6c1d22313763331` 不变。没有混用改变后的旧 declaration_version 依赖。

原稿、既有治理协议、工具链pin和CI工作流自上一已审阶段未改变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。固定 Lean 为4.35.0，mathlib pin及本机实际HEAD均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机mathlib工作树干净。root显式导入两模块，`tools/CheckAxioms.lean` 含四项完整类型和公理输出，并递归审计全部Carleman声明。

实际读取 `/tmp/carleman-fd-approximation-interface-target.log`，其中为 `Build completed successfully (3781 jobs).`；实际全库 `-full.log` 为 `Build completed successfully (3832 jobs).`，末行为 `Axiom audit passed for all 6554 Carleman declarations.`。

固定 `/tmp/carleman-fd-approximation-interface-local-axioms.txt` 为 **1,943,313 bytes**，SHA256 **`945d9f7e41bd4661019239c792278154555daca6022e6308ffe5f619308a995c`**。四项完整展开类型已逐项核对，全部2219条显式公理记录中2211非空、8无公理，均无 `propext`、`Classical.choice`、`Quot.sound` 之外的公理，无sorryAx。

## 实际同 SHA CI 与原始远端产物

本验收 Agent 自行经 GitHub connector 查询 [main CI 39198141744 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39198141744/attempts/1)。实际run为main/push、completed/success，head SHA精确等于本报告固定提交。三个job均completed/success：state-check **117885263045**、lean **117885263171**、dashboard / snapshot **117886100275**；最终读取的全部实际步骤均success。

同run原始artifact元数据：`lean-ci-result` **12162731613**、`lean-declaration-evidence` **12162776480**，两者workflow_run.head_sha均为固定SHA。本Agent自行通过 `gh run download 39198141744` 下载两份原始产物至约定目录。

实际 `/tmp/carleman-fd-approximation-interface-main-ci/result.json` 为PASS，`checked_sha=source_head_sha=20523c258707a3864f45541d0eea83581360c86b`，targets为Carleman，`finished_at=2026-10-19T04:12:49.925840+00:00`，ci_url与上述run/attempt一致。Lean4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

独立逐字节比较 `/tmp/carleman-fd-approximation-interface-main-axioms/axioms.txt` 与固定本机副本，完全一致：**1,943,313 bytes**，SHA256 **`945d9f7e41bd4661019239c792278154555daca6022e6308ffe5f619308a995c`**。另逐名确认远端4/4完整类型及基础公理记录，实际末行为 **6554项全声明递归审计PASS**。未使用其他SHA或后续工作区 `.ci/axioms.txt`。

## 验收决定

**C126：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定四项声明未发现需要修复的数学缺陷。原完整 H¹/q 与 H²参数范数、同一 Q_h 的 canonical 误差 jet、全域/全权族/全状态及统一常数量词、真实 A/R/J/lift/B* 与物理权范数的数据组装均已独立核对。同SHA正式三项CI与自行下载的原始公理证据已核实。

原实际 D(A)⊆H² 仍是明确的 A1 输入；本批不证明具体 H² 正则性，不提升完整 FD/P012 或 PAPER，原文保持 **14/26**。本次仅新建此报告，没有修改实现、台账、原稿或root导入，没有commit/push。以上签发UTC固定，通知主Agent后不再变更报告或时间戳。
