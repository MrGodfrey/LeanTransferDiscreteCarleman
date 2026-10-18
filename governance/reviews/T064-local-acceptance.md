# T064 / C080 独立本机验收

- checked_sha: `7d5b98f23e305b99c69543c953bb545fefc42cb7`
- base_commit: `36278e60193f3453a60bcdf33ef089ace1398350`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result: `PASS`（固定版本 9 项可升 REVIEWED；仅 AUXILIARY 范围）
- axiom_check: `PASS`
- reviewed_at: `2026-10-18T21:43:01+00:00`
- scope: `AUXILIARY`。真实弱 H¹ 残差、完整原 V_h 状态及原允许权乘子范数的连接；未完成 ℓ⁻¹ 残差项、投影组合或残差的 H¹₀ 资格。原文完成数保持 **12/26**。

## 固定范围与核验方法

依仓库 `AGENTS.md`、`governance/PROJECT_OPERATIONS.md`、`state/README.md`，直接读取固定提交六模块的全部证明、9 项实际展开类型和递归公理输出，读取其实际调用的弱导数、节点空间、残差积分、乘子等依赖，并对照原 `paper/main.tex` Section 6 Step 3 与 `governance/analysis/T064-weak-nodal-norms.md`。没有以执行者说明或构建通过代替数学审查；后续未提交文件不在本次范围。

六模块为 `Spatial/SupportedLipschitzProduct`（2 项）、`Spatial/NodalResidualSobolev`（2 项）、`Spatial/NodalResidualLp`（1 项）、`Weights/FullWeakNodalResidual`（1 项）、`Weights/SquaredWeightNorm`（2 项）、`Weights/FullNodalWeakNorms`（1 项），均在 `Carleman/` 下。9 项精确匹配固定 C080 与 `/tmp/carleman-weak-nodal-norms-declarations.json`；固定 root 导入全部六模块。递归项目 import 闭包有 180 个模块，174 个既有模块相对基线逐字节不变。

原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean pin 为 `leanprover/lean4:v4.35.0`，mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`；实际本机 mathlib HEAD 相同且工作树干净。治理指令、CI workflow 与构建脚本相对基线未改。

## 全部 9 项实际声明

以下使用完整 Lean 名称；逐项数学语义及本机、同 SHA 远端公理核查均 PASS。

| 声明 | 实际内容、假设和使用核对 |
| --- | --- |
| `Carleman.supported_lipschitz_product` | 任意集合 K 上 w 有界且 Lipschitz、u 全局有界且 Lipschitz、u 在 K 外为零，则真实乘积 wu 全局 Lipschitz，常数 `BL+PD`。两点在 K 内、跨 K、均在外的分支齐全，不要求 w 在 K 外有界/连续。 |
| `Carleman.SimplicialPartition.squared_nodal_product_lipschitz` | 原开凸紧闭域、C² profile、FaceMatching、BoundaryFitted 和零边界节点给真实 `σ²·nodalFunction f` 的全局 Lipschitz 性。σ² 的闭域有界/Lipschitz 数据与节点函数的全局界均内部供应；存在性常数可依赖状态、网格和权。 |
| `Carleman.compactLipschitz_restricted_jet_exists` | 任意真实紧支全局 Lipschitz f 构成全空间实际弱 H¹ jet，再限制到 S；零阶字段 a.e. 为 f，一阶完整 Euclidean fiber a.e. 为真实 fderiv f。不是自由指定梯度。 |
| `Carleman.SimplicialPartition.squared_nodal_residual_weak_jet` | 两项全局 Lipschitz、紧支函数之差恰为真实 `nodalProductResidual σ² f`，由前项构造实际 H¹ jet e，并给其 value 和 field 1 的准确 a.e. 代表。加权节点数据的零边界值通过乘以零实际证明。 |
| `Carleman.allowedSquaredWeight_full_weak_residual` | 对任意原完整一致 H¹₀ 空间中的状态，内部产生零边界节点表示 f 及真实弱残差 e，保持同一节点测试属于原空间，并把已有真实积分界转换为 e 的真实零阶/一阶字段积分界。统一 C 先于网格、权和状态。 |
| `Carleman.SimplicialPartition.nodalProductResidual_lp` | 在实际 L² 商空间中证明 `e=w.map u−nodalLp(wf)`；所有点态代表转换都是同一受限测度下的 a.e. 恒等式。保持残差符号，不把任意 L² 类作节点求值。 |
| `Carleman.allowed_weight_sq_integral` | 对标量或任意真实实内积空间值 L² 状态，实际 σ 乘子 seminorm 的平方恰为 `∫σ²‖u‖²`，由真实 L² 内积/乘子公式推出。 |
| `Carleman.allowed_inverse_weight_sq_integral` | τ、η 同时反号所得实际 ξ=σ⁻¹，给 `‖ξu‖₂²=∫‖u‖²/σ²`。没有把 σ² 错作倒数权本身或漏平方；不只覆盖标量字段。 |
| `Carleman.allowed_full_nodal_weak_norms` | 任意原完整 V_h 状态内部获得 `I∈V_h` 及真实弱 H¹ jet e，满足 `value(e)=(σ.mul σ).map(value(u))−I` 和原 ξ 加权零阶/一阶字段的 h⁴/h² 平方范数界。右端同为原 u 的 σ 加权标量和完整弱梯度范数，未加节点表示或额外正规性前提。 |

## 支持集乘积与域外边界

一般乘积引理的 K 不需要闭、凸或光滑。两点 x,y 都在 K 时，准确分解

`w(x)u(x)−w(y)u(y)=w(x)(u(x)−u(y))+(w(x)−w(y))u(y)`，

两项分别由 B·L 与 D·P 控制。x∈K、y∉K 时，u(y)=0，故 `|u(x)|=|u(x)−u(y)|≤L dist(x,y)`，仅用 K 内的 |w(x)|≤B 即得 BL 项；反向跨界通过距离/绝对值对称性，均在外时乘积都为零。这里从未尝试控制域外 w(y)，也没有从仅 K 上 Lipschitz 自动断言全空间 Lipschitz。

平方权实例取 K=closure S。真实 C² 平方权在闭域 C¹，由实际域内导数和凸集均值定理得到 D，由紧性得到 B；B 可能先是实数，所以确实用 `max B 0` 包装。节点函数的 P 是有限节点绝对值之和，L 是有限局部真实仿射导数范数之和。已检查其全局 Lipschitz 依赖使用 FaceMatching、BoundaryFitted、真实零边界节点和有限连续选择定理，而非仅在每个单元各自 Lipschitz 后直接拼接。`nodalFunction_zero_outside` 的结论恰为 closure S 外为零，与本次 K 精确匹配。

对残差 `E(x)=σ²(x)N(f)(x)−N(σ²f)(x)`，加权节点数据在边界节点为零，故第二个节点函数也全局 Lipschitz。真实紧支撑来自有限单元并/closure S；乘积的支撑包含于 N(f) 的紧支撑，使用此包含不要求 σ² 在域外连续。两项之差于是为真实紧支全局 Lipschitz 函数。q、τ、η 在这些仅用于成员资格的引理中可任取实数，因为平方权的空间光滑性依然成立；最终误差/倒数范数使用的 q≥1、TimeWeight 正值明确保留。

这些成员资格常数可以依赖网格节点数、状态和当前权，也没有被错误称作统一逆估计。关键是最终 `allowedSquaredWeight_full_weak_residual` 在调用这些存在性构造**之前**已经从 T063 取出 C，随后只保留 e 的 a.e. 字段身份；构造中的 B、P、L、D 从未进入误差不等式的 C。

## 完整弱 H¹ 构造、Rademacher 与真实限制

直接追踪 `compactLipschitzSobolevJet`：f 的连续紧支撑供应真实全空间 L² 类；实际 fderiv 的范数由 Lipschitz 常数控制，在 tsupport f 外实际 fderiv 为零，因此用紧支撑指标函数得到它的真实 L² 可积性。不是单纯因全局有界就在无限体积空间上断言 L²。

固定 mathlib 的 Rademacher 定理在此有限维实空间、实值函数和 volume 上给 a.e. 可微性。依赖 `lipschitzGlobalJet` 对每个正交方向使用真实 a.e. HasFDerivAt，然后用 `weakSpatialDerivative_of_lipschitz_full` 证明完整弱身份。已直接核查该证明及 mathlib 的 `integral_lineDeriv_mul_eq`：对任意原 SpatialTest，测试 C∞ 紧支撑给 Lipschitz 性，真实差商积分分部公式中的 −方向经测试真实 fderiv 变为负号，得到 `∫D_eφ·u=−∫φ·v`。没有只测试有限元函数、没有把梯度作为不受约束字段塞入 jet，也没有忽略单元面跳跃项。

随后 `WeakSobolevJet.restrictDomain S` 逐字段使用真实 L² 限制；每个 SpatialTest S 原样成为全空间测试。测试值及其真实导数在 S 外因 tsupport 包含而为零，两种积分准确限制到 S。原任意坐标的弱身份和负号均保留；`derivativeComponent_restrict` 保证限制与完整坐标字段交换。新定理再用受限测度≤volume 将全空间 a.e. fderiv 身份转为 S 上的身份。`derivativeOneFiber` 是原 Euclidean 一阶全部坐标各一次，不是另定义的能量。

这样得到的 e 是完整 `WeakSobolevJet d 1 (volume.restrict S) S`，具有真实 L² 零阶和一阶字段。骨架上的普通导数可能不存在，但只使用 Rademacher 的 a.e. 身份及旧单元内部导数的 a.e. 恒等式；不声称边界/骨架逐点可微，也不靠选择一个跳跃代表来绕过弱导数条件。

## 原完整状态、节点测试与 L² 恒等式

输入是任意实际弱 H¹ jet u，且 `value u∈M.conformingSpace(dirichletSubspace S)`。该原空间是逐单元 a.e. 仿射空间与实际 H¹₀ 标量实现的交，并非预先缩成节点映射的像。H¹₀ 标量成员按其定义已有 H¹ 见证；因此这一 jet 表述不丢失原完整 V_h 的状态。

已直接检查 `conforming_dirichlet_nodal_with_gradient` 及实际节点表示依赖：从原完整空间内部取得零延拓的连续 Lipschitz 代表，利用闭单元连续代表与 a.e. 仿射身份推出整个闭单元上的仿射身份；零延拓和连续性给边界节点为零。再通过完整弱梯度唯一性及真实单元 a.e. 分区识别原任意 u 的 field 1。没有在最终定理中额外假设原状态已由节点函数表示、原梯度已等于分片梯度，或 u 更光滑。

同一 f 的加权节点函数 `N(σ²f)` 通过已证真实节点 H¹₀ 成员定理进入完整 V_h：权乘零边界节点仍为零。这个 I 是实际插值类，不是自由存在的有利测试，也不是本阶段尚未应用的正交投影。

`nodalProductResidual_lp` 将 e 的实际 a.e. 代表、u=nodalLp f、原乘子 map 的 a.e. 作用和 Lp 减法代表逐项合并，再用 Lp.ext 得等价类精确相等。最终用平方权与 `(σ.mul σ).value` 的逐点恒等式得到

`value(e)=(σ.mul σ).map(value(u))−I`。

乘子 `mul` 的实际值就是两个乘子值相乘，其 map 已定义在真正 L² 等价类上；不是把平方能量当作平方状态。残差方向与原 `σ²z_h−I_h(σ²z_h)` 一致。

## 原乘子范数、积分可积性与统一性

两个新积分身份从真实 `BoundedMultiplier.seminorm_sq_integral` 出发。σ 的真实平方是 `allowedSquaredWeight`；ξ 使用同一 profile、τ 与 η 同时反号，通过已有真实实幂/指数倒数恒等式满足 ξ=σ⁻¹。`|σ|²=σ²`、`|ξ|²=(σ²)⁻¹` 与除法的转换准确。定理量化任意实内积空间 E，最终分别实例化标量和原完整 Euclidean derivative fiber，因此未把向量场降为单方向。

所有涉及积分的量都真实可积：新范数身份有实际有界乘子作用的 L² 对象；所承接的 T063 积分证明也已内部供应残差值/导数、原状态值/导数四种密度的可积性。本次直接检查 `squaredNodal_integrability`，其中正平方权、紧单元连续字段及骨架外 a.e. 导数身份给可积性，再用有限覆盖转到 S，未借用 Lean 对不可积函数积分默认值为零来完成估计。

记 `q=w.q t`、`h=M.maxDiameter`，最终实际能量为

`A=q⁴‖σ value(u)‖₂²+q²‖σ field₁(u)‖₂²`。

输出精确是 `‖ξ value(e)‖₂²≤Ch⁴A` 和 `‖ξ field₁(e)‖₂²≤Ch²A`。这与旧真实积分界逐项 a.e. 替换、再按上述真实范数平方身份改写一致，没有更换右端为构造节点代表的任意梯度或丢失 q 的幂。对 m=1，这一能量在数学上等于 `q² N_σ(u)²`，但本报告不把未在本阶段导出的完整 eq:testsuper 登记为完成。

C 在固定 d、S、profile 和非负形状参数 κ 后选择，先于全部网格/index 类型、FaceMatching/BoundaryFitted 证据、TimeWeight、τ、t、η、内球数据 a/r 及完整状态 u。构造 f、I、e 全在这些对象之后；成员资格 Lipschitz 界不会倒流进入 C。原 hq≤1、每个 r_K>0、真实内球及 diam(K)≤κr_K 均明确保留，未把形状正则偷偷改成对一个特殊网格的选择。额外写出的 `1≤w.q t` 已由真实 TimeWeight.lower 恒成立，不增加原条件。空间结论对所有实 τ 和两个 η 符号成立，包含原允许族，C 不随 T、qmax、τ、时刻或状态变化。

空网格/空域的有限和与真实零类论证不要求挑选不存在的单元。d=0 不依赖空间单点零测；e 的全局 H¹ 构造使用合法零维坐标和有限维 Rademacher 接口，完整一阶 fiber 此时为空坐标零空间。成员资格阶段允许零 Lipschitz 常数，最终也没有除以状态范数或误差范数。

## 原文定位、依赖验收及范围

原 Section 6 Step 3（`paper/main.tex:1569–1593`）需要实际残差的 σ⁻¹ 加权弱梯度、ℓ⁻¹ 加权零阶项、节点测试属于 V_h，再与投影和逆估计组合。T063 的左端此前是普通 fderiv 的真实积分；本阶段确实补上了真实弱 H¹ jet 及原乘子范数接口，不能再将其仅视为未连接的经典导数估计。

但本阶段没有证明 e 的 `dirichletJetSpace` / `dirichletSubspace` 成员资格，不能仅凭紧支全空间 Lipschitz 或值在域外为零就把未导出的 H¹₀ 闭包结论算作已形式化。ℓ⁻¹σ⁻¹ 残差项、投影/逆估计组合、最终 `eq:testsuper`、一般 H² 插值及完整 `prop:p1` 仍未由本批完成。范围应保留 AUXILIARY，原文仍 12/26。

读取并核实 [T063 / C079 独立验收](T063-local-acceptance.md)，其 checked SHA 正是本阶段基线；本次实际检查其 `FullNodalResidual`、`FullNodalGradient`、`SquaredNodalGlobal`、`SquaredNodalIntegrability` 的前提与调用，及其真实非负能量/单元积分求和，原 C 被原样保留。另直接追踪全节点表示、全局节点 Lipschitz/边界、紧支 Lipschitz Sobolev、全部弱测试限制、乘子代数和平方密度；依赖已有结论没有被扩大使用。

## 本机与远端构建证据

已独立读取 `/tmp/carleman-weak-nodal-norms-full.log`：实际 `Build completed successfully (3653 jobs)`，末行确认全部 4974 个 Carleman 声明递归公理审计通过。固定 `/tmp/carleman-weak-nodal-norms-local-axioms.txt` 实测 **1,462,594 bytes**，SHA256 **`57dbfd126401431327a3ae50f04a2b5c4678a93c16104ef3cf68445415be9fee`**。9 项完整展开类型逐名核对，递归公理每项恰为 `propext`、`Classical.choice`、`Quot.sound`；没有 sorryAx 或额外数学公理。固定 `CheckAxioms` 对本批逐项打印并对整个 Carleman namespace 递归 collectAxioms，未只审计外层包装。

已独立读取 GitHub 实际 run 和 jobs API：[main/push run 39168606941 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39168606941/attempts/1) 为 completed/success，head SHA 与本次固定 SHA 精确相同。全部三项 job 均为同一 SHA 且 completed/success：`lean`（117796754611，2026-10-18T21:39:38Z）、`state-check`（117796754961，21:36:56Z）、`dashboard / snapshot`（117797389368，21:39:49Z）。实际 artifacts API 中 `lean-ci-result`（12151776312）及 `lean-declaration-evidence`（12151756501）均来自同一 run/SHA 且未过期。

已直接读取原始 `/tmp/carleman-weak-nodal-norms-main-ci/result.json`：status 为 PASS，checked_sha 与 source_head_sha 均为 `7d5b98f23e305b99c69543c953bb545fefc42cb7`，ci_url 指向上述 attempt，finished_at 为 `2026-10-18T21:38:38.182005+00:00`，target 为 Carleman，Lean 4.35.0 与 mathlib pin 均匹配。该时间是检查结果生成时间，三项 job 最终成功时间另如上，不混同为整个 run 完成时间。

已读取 `/tmp/carleman-weak-nodal-norms-main-axioms/axioms.txt` 并与固定本机产物逐字节比较：完全相同，均为 **1,462,594 bytes**、SHA256 **`57dbfd126401431327a3ae50f04a2b5c4678a93c16104ef3cf68445415be9fee`**。远端全部 9 项均只使用上述三项标准基础公理，末行明确全部 **4974** 声明审计 PASS。没有使用后续工作树的 `.ci/axioms.txt` 替代本次固定产物。

最终结论：本阶段 9 项声明的数学语义、实际依赖、全状态与常数量词、递归公理及真实同 SHA 三项 CI 均通过，C080 可在本报告界定的 AUXILIARY 范围内升 REVIEWED。没有发现需要修改证明的具体缺陷。残差 H¹₀ 成员资格、ℓ⁻¹ 残差项和投影组合仍为后续义务；不提升原论文命题完成数。本次仅写本验收报告，未修改证明或台账，未 commit/push。
