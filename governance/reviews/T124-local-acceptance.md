# T124 / C140 独立本机验收

- `checked_sha`: `f3e3ddb8621286134d4560b73a682b495d0c0907`
- `base_commit`: `e56df9d1895554e8cdfacc7e52c86bac51a08e6c`
- `reviewed_at`: `2026-10-19T06:06:44+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原全部弱 H²∩H¹₀ 状态的同一实际节点插值和 H¹₀ 误差，满足原 P1 Step 2 的两个全域允许权节点估计。原 L² 投影组合、数值接口及完整 P011 不在本次范围，原文覆盖保持 **14/26**。

本 Agent 直接读取固定 git 对象中的五模块全部证明、10项完整展开类型、关键依赖、原 `paper/main.tex` P1 定义和 Step 2、T124 分析、MATH_SPEC 及 C140/T124 条目。已读 AGENTS、PROJECT_OPERATIONS、state/README 与基线逐字节不变。数学判断不以规格、执行者自检或 CI 代替；工作树后续投影及数值组装、变化中的 `.ci/axioms.txt` 均未用作依据。

## 全部十项声明

名称省略公共前缀 `Carleman.`；源位置以 `Carleman/Spatial/` 为根。顺序与固定 C140、T124 及交付 JSON 清单一致。类型行号指独立下载并与固定本机副本逐字节相同的原始 axioms.txt。

| # | 声明 | 固定源位置 / 完整类型行 | 独立结论 |
|---|---|---|---|
| 1 | `BoundedMultiplier.integral_transfer` | `WeightedIntegralTransfer.lean:26` / 26673 | PASS；真实 L² 类的局部两侧权比较给 W⁴ 倍平方积分转移，正锚 s 精确消去。 |
| 2 | `BoundedMultiplier.integral_transfer_memLp` | `WeightedIntegralTransfer.lean:45` / 26684 | PASS；通过同一函数真实 toLp 的 a.e. 身份回到 MemLp 函数积分，未使用不可积函数的默认积分。 |
| 3 | `SimplicialPartition.cellWeight` | `CellwiseScaledWeight.lean:15` / 26697 | PASS；实际定义为 inverseWeight 对单元系数双逆，得到 cᵢw 的真实乘子，允许 cᵢ=0。 |
| 4 | `SimplicialPartition.cellWeight_on_cell` | `CellwiseScaledWeight.lean:18` / 26706 | PASS；在完整闭单元的受限 Lebesgue 测度下，实际代表 a.e. 等于 cᵢw。 |
| 5 | `SimplicialPartition.cellWeight_sq_sum` | `CellwiseScaledWeight.lean:26` / 26714 | PASS；标量或向量真实 L² 乘权范数平方精确等于各闭单元 cᵢ² 加权积分之和。 |
| 6 | `SimplicialPartition.cellWeight_seminorm_le` | `CellwiseScaledWeight.lean:40` / 26724 | PASS；逐单元 \|cᵢ\|≤B 给全域乘权范数≤B倍原范数，无单元数常数。 |
| 7 | `SimplicialPartition.weighted_cell_errors_sum` | `WeightedCellAssembly.lean:16` / 26735 | PASS；逐单元 A cᵢ² 能量界精确求和、非负开平方，得到 √A 倍真实 cellWeight 范数。 |
| 8 | `SimplicialPartition.weighted_cell_inverse_errors_sum` | `WeightedCellAssembly.lean:27` / 26750 | PASS；对实际 inverseWeight 使用 (ℓ⁻¹)²ℓ⁴=ℓ²，得到所需逆尺度误差界。 |
| 9 | `weak_h2_weighted_nodal_approximation` | `WeakH2WeightedNodal.lean:15` / 26766 | PASS；全部原弱 H²∩H¹₀、同一 f/e 先于所有局部可比权，保持真实 ℓ²/ℓ 单元 Hessian 范数。 |
| 10 | `weak_h2_allowed_nodal_approximation` | `WeakH2AllowedNodal.lean:13` / 26812 | PASS；原空间 profile 的局部比较和严格正锚全部内部构造，统一覆盖所有 TimeWeight、实幂、时间和两种符号。 |

## 原文目标和完整状态范围

原稿1467–1494行给出固定有界凸多面体、d∈{2,3}、conforming 形状正则单纯形网格、正尺度 ℓ_K，以及原 L² 物理范数。1523–1544行要求同一个节点插值 I_h 满足

\[
\|\sigma(v-I_hv)\|_{L^2(\Omega)}
\le C\|\ell^2\sigma D^2v\|_{L^2(\Omega)},
\]
\[
\|\sigma\nabla(v-I_hv)\|_{L^2(\Omega)}
+\|\ell^{-1}\sigma(v-I_hv)\|_{L^2(\Omega)}
\le C\|\ell\sigma D^2v\|_{L^2(\Omega)}.
\]

本批第9、10项确实对应这两个节点估计。输入为任意 `WeakSobolevJet d 2 (volume.restrict S) S` 及其 value 属于原 `dirichletSubspace S`，不是仅光滑子类。各阶字段是实际弱导数 L² 类；同一原状态内部取得闭包连续代表 f，与原值 a.e. 相同且在整个 frontier S 上零值。第9项先调用已验收 C139，再在引入任何权之前固定 f 和真实误差 e。

已直接复核 `WeakH2ConformingNodal`、`H2NodalErrorJet`、`H2NodalCellError`。实际插值是同一节点值的 `M.nodalLp`，成员属于真实逐片仿射 L² 空间与原 H¹₀ 空间的交；实际误差是原弱 H² 的一阶截断减同一节点弱 jet。输出 `e ∈ dirichletJetSpace S`，值严格等于原值减 nodalLp，整个一阶字段由真实弱导数身份确定。没有将任意候选梯度作为输入，也没有另选一个依赖权或单元的插值。

原 H¹₀ 空间是紧支光滑测试 jet 在线性 H¹ 图拓扑下的闭包；本批沿用 C139 已清偿的连续代表、边界零值及实际节点 H¹₀ 资格，未重新假定这些目标。d≤3 包含原 d=2、3；没有额外原状态光滑性、H² 零延拓、目标误差或候选逼近序列前提。原 D(A) 的 H²∩H¹₀ 状态因而被上述更广的原弱状态接口覆盖；本批自身不新增算子域与 H² 正则性定理。

## 正锚转移、真实可积性与精确单元求和

第1项对任意测度和实内积空间中的实际 L² 类 u、v，假设 W≥0、s>0、A≥0，以及 a.e. 的 \|w\|≤Ws、s≤W\|w\|。已有真实乘权范数估计分别给出 \|wu\|≤Ws\|u\|、\|v\|≤(W/s)\|wv\|。将无权平方能量界插入后，系数为 (Ws)²A(W/s)²=W⁴A；`field_simp` 的分母正性来自显式 s>0。W 不需要除法，u/v 或 A 为零均合法。私有平方积分身份使用真实 L² 内积；第2项用 MemLp.toLp 的 a.e. 相等把同一结论返回实际函数积分。

每个局部应用都将原真实 BoundedMultiplier 限制到闭单元测度，将原值、全梯度和原 Hessian 的 MemLp 通过 `cell_measure_le_domain` 限制。该比较并未误用闭单元 K⊆S：单纯形边界零测，interior K⊆S 来自开凸域和闭单元包含于 closure S，因此 volume.restrict K≤volume.restrict S。所有乘权平方密度可积，所用积分不是不可积时的默认零值。

`cellWeight c w` 复用实际 `inverseWeight (fun i => (c i)⁻¹) w`，双逆恒等式包含 c_i=0。`cellWeight_on_cell` 从真实 a.e. 分区和测度比较得出闭单元上的 c_iw 代表。第5项调用实际 `integral_eq_sum_cells`：网格覆盖原域，单元内部两两不交，共享面零测，故完整闭单元积分精确相加。真实向量范数平方同样适用，未按坐标重新加入维数或单元数量损失。

有限网格乘子本身的有界性打包可以使用有限系数总和，但最终估计从精确单元身份导出，未调用这个可能依赖网格的粗有界常数。第6项只用逐单元 |c_i|≤B，得统一 B；第7项求和后用真实 L² 范数非负性及 √A²=A 取根。第8项在同一求和中乘 (ℓ_i⁻¹)²，再用 (ℓ_i⁻¹)²ℓ_i⁴=ℓ_i²。该辅助代数身份对 ℓ_i=0 也合法；最终节点定理仍保留原 ℓ_i>0，没有以零尺度替换原假设。

## 原局部 Hessian、尺度与统一常数

记 D_i 为真实单元直径，H=field₂u，C_d=`tensorCoordinateBound d 2`。C139 的无权局部界右端始终是同一闭单元上的 ∫K_i‖H‖²。第9项先在该单元进行 W⁴ 权转移，再由 D_i≤Bℓ_i 分别控制四次与二次幂，得到

\[
\int_{K_i}|w|^2|e|^2\le A_0\ell_i^4\int_{K_i}|w|^2\|H\|^2,
\qquad
\int_{K_i}|w|^2\|\nabla e\|^2\le A_1\ell_i^2\int_{K_i}|w|^2\|H\|^2,
\]

其中实际选取

\[
A_0=W^4\,16C_d^2d^2B^4,\qquad
A_1=W^4\bigl(2^dd+128\kappa^2\|\operatorname{derivativeOneFiber}_d\|^2\bigr)C_d^2d^2B^2,
\quad C=1+\sqrt{A_0}+\sqrt{A_1}>0.
\]

C_d 和 derivativeOneFiber 的范数只依赖维数，来自实际弱张量坐标及完整一阶纤维；没有用任意 Hessian 替代原二阶导数字段。局部真实 Hessian 与原 D²v 的维数范数对应已在前置局部估计中清偿。上述公式没有位置、域、单元数、状态或时间参数。两个局部界分别用第7项取 c_i=ℓ_i²、c_i=ℓ_i，再用第8项处理逆尺度值误差，产生同一个 C。

右侧全程保持真实 `cellWeight (ℓ²) w` 或 `cellWeight ℓ w` 作用于原 H 的范数，等于 ℓ²wH 或 ℓwH 的实际分片乘权范数。没有替换为全域最大尺度乘无权 Hessian，也没有扩大局部能量到其他单元。原 grading 的下界 cD_i≤ℓ_i 与 D_i≤Bℓ_i 在 B=1/c>0 时等价；原上界及相邻单元 γ 比较不被这两个节点估计使用，省略它们是加强辅助命题，不是收紧原网格类。后续转成全局 h²/h 或投影稳定性仍需要相应条件和证明。

真实内球 B(a_i,r_i)⊆K_i、r_i>0 和 D_i≤κr_i 表达原形状正则性。原形状正则网格可选相应内球，不要求固定网格专用函数估计。d=0、空域和空索引未被人为排除；证明没有除以 d 或 D_i，退化情形沿用实际 L²、代表和分区结论。最终显式的有限测度类型类由有界 Euclidean 域推出，compact closure 也由原有界域给出，属于可从原几何条件供应的接口实例，不是额外实质假设。

## 全允许权、同一 f/e 与周期统一性

第9项的量词是固定 d、κ、B、W 后先选 C，然后才量化索引类型、域、网格、原状态；对每个状态先选同一 f/e，再量化所有局部可比 BoundedMultiplier 和全部正锚。原依赖 C139 给出的真实 f/e 未随 w 重新选择。

第10项固定原 S、空间 profile ρ 和 κ、B 后，先从真实 C¹ 闭包假设经 `smooth_profile_lipschitz` 得到 L≥1，并选 W=exp L。该依赖用开凸域的实际闭包可微唯一性、紧闭包上的导数界及凸域均值估计，空域也有分支。原光滑 profile 满足这个 C¹ 条件；没有增添光滑边界假设。

随后 C 在所有网格、状态、TimeWeight、τ、t、η 之前选定。对任意 |η|=1 及 hq(t)≤1，σ 是实际 `(ρ.scaled η).multiplier w τ t`，即 q(t)^τ exp(ηρ(x)q(t))。每个单元内部选真实顶点 x_K，令 s_K=σ(x_K)>0。`allowedWeight_cell_comparison` 以实际直径、h=max D_i、profile Lipschitz 界和 q(t)≥0 证明双向比较，完全消去第9项中的局部权比较和锚点前提。原 τ 因子在空间比值中严格抵消，不产生 τ 依赖常数。

所有实幂、两符号都在最终类型中；σ 的倒数由同时取 −η、−τ 得到，未误将只翻转 η 视为一般 τ 下的完整倒数。原数值阈值可取 δ_num≤1，故 hq≤1 是本批明确供应的统一允许阈值。最终没有预先固定 T、TimeWeight 或时刻，常数不依赖周期 T；同一个 f/e 同时适用于这些全部权参数。

据此，原 `eq:p1-interpolation` 与 `eq:p1-interpolation-energy` 的节点插值部分在原几何和状态范围内成立。此结论没有把节点插值当成原正交投影 Π_h，也没有证明后续投影误差、N3 或完整 P1 数值假设；C140 保持 AUXILIARY，P011 不提升。

## 固定版本、构建和递归公理

直接检查的关键依赖包括 C139 的原全部弱状态、真实 nodalH2ErrorJet 及同单元原 Hessian 界，SimplicialIntegrals 的实际闭单元分区求和，CellwiseInverseWeight 的真实分片逆尺度，LocalWeightedNorm 的两侧正锚估计，以及 SpatialComparison / SimplicialAllowedComparison 的实际指数权比。已核对其调用条件和对象，未仅依靠历史 PASS 标签。

五新模块的 Carleman 导入闭包为222模块，其中217旧模块与已验收基线 `e56df9d1895554e8cdfacc7e52c86bac51a08e6c` 逐字节相同。该基线的 [T123 / C139](T123-local-acceptance.md) 为正式 PASS；其完整原状态、实际节点和误差依赖未被本批修改。固定 root 导入五模块，固定 CheckAxioms 输出本批10项完整类型并继续执行全部声明的递归公理审计；递归审计主体与基线不变，涵盖生成声明及 privateToUserName 后的私有 Carleman 声明。

原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与已验收版本相同。Lean 固定4.35.0，mathlib pin 及本机实际干净 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。实际读取 `/tmp/carleman-weak-weighted-target.log` 的3400 jobs成功记录、`-full.log` 的3884 jobs成功记录和6740声明递归审计PASS。

固定本机 `-local-axioms.txt` 为 **2,061,805 bytes**，SHA256 **`96d63e0cd091e26aa0e452ab5323ef969447a8f055fbe6d03f6430bb400b5b4b`**。10项完整展开类型均存在，全部公理为 `propext`、`Classical.choice`、`Quot.sound`；全文2349条非空和8条无公理打印记录均未出现其他公理，最终递归审计覆盖6740项。新增源码无 sorry、admit、额外 axiom 或 native_decide。

## 同 SHA 正式 CI 和独立下载

本 Agent 经 GitHub connector 自行查询 [main CI 39207488120 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39207488120/attempts/1)。run 为 main/push，head SHA 精确匹配，最终 completed/success，`updated_at=2026-10-19T06:04:30Z`。三 job 全部 completed/success：lean **117913389696**、state-check **117913390022**、dashboard / snapshot **117914364866**。Lean 的 pinned toolchain、证明构建、结果记录、两份证据保存及收尾步骤均实际成功。

同 run 原始 artifact 为 `lean-ci-result` **12165968989**，压缩产物493 bytes，digest `sha256:18a5c1554d9cad2769b5f2129b3ec51e810086a2630095e0747f8e3a662b0800`；`lean-declaration-evidence` **12166650960**，压缩产物189197 bytes，digest `sha256:ffca704c49523959aa1b68db78f5c76f3a2761a849cb53738c252875bda00bdf`。两份 workflow_run 元数据均绑定该 run、main 和精确 SHA。本 Agent 自行执行两次 `gh run download 39207488120` 至约定 `-main-ci`、`-main-axioms` 目录，两次下载均 exit 0。

实际 `/tmp/carleman-weak-weighted-main-ci/result.json` 为 **PASS**，`checked_sha=source_head_sha=f3e3ddb8621286134d4560b73a682b495d0c0907`，targets 为 Carleman，`finished_at=2026-10-19T06:03:20.096643+00:00`，ci_url 指向上述 run/attempt。Lean 编译器提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 为上述 pin。解压 result 为537 bytes，SHA256 `ec31be7c4e58e7d9c2e8be23343049cc3f89df8cf26b739c2645763bd38176e1`。

实际远端 `/tmp/carleman-weak-weighted-main-axioms/axioms.txt` 与固定本机副本独立逐字节比较完全一致：**2,061,805 bytes**、SHA256 **`96d63e0cd091e26aa0e452ab5323ef969447a8f055fbe6d03f6430bb400b5b4b`**，末行实际为 **6740项全声明递归审计PASS**。本批10项的实际类型及全部公理均在该同版本证据中，未混入后续源码或审计结果。

## 验收决定

**C140：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 10项声明未发现需修复的数学缺陷。真实正锚消去、实际可积性、闭单元精确求和、局部 ℓ²/ℓ Hessian、原全部弱状态、同一 f/e、全部允许权以及统一常数量词均已核实；同 SHA 三项正式 CI 与独立下载的原始公理证据一致。

P011 不提升，原文覆盖保持 **14/26**。本次仅新增本报告，未修改实现、台账、root 或原稿，未 commit/push。签发 UTC 如上固定；最终核对并通知主 Agent 后冻结本报告内容和时间戳。
