# T116 / C132 独立本机验收

- `checked_sha`: `fa02c379c6ee0f59172dadc1401b9a535e6d3c9c`
- `base_commit`: `f134750df6b8ef03c639f50dd5084d4c42d49272`
- `reviewed_at`: `2026-10-19T05:00:31+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：任意开域 S 上全部原弱 H² jet 在 d≤3 时的内部连续代表、同一实际卷积的内部逐点极限与代表唯一性。结论为 `ContinuousOn f S`，不是 `ContinuousOn f (closure S)`；边界节点资格、完整 P1 插值与全局允许权仍待，P011 不提升，原文保持 **14/26**。

本 Agent 从固定 git 对象读取五模块全部证明、14项完整展开类型及关键依赖，并对照原 `paper/main.tex` Section 6 Step 2（1527–1548）使用 H²(Ω)→C⁰(closure Ω) 定义节点插值的段落。已读取固定 T116 分析、MATH_SPEC 和 C132 台账。执行者说明和 CI 未替代数学核查；后续工作树增量与变化中的 `.ci` 文件均排除。

## 全部14项声明

名称省略公共前缀 `Carleman.`，文件以 `Carleman/Spatial/` 为根。表中顺序与固定声明 JSON 和 C132 台账逐项一致。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `continuous_memLp_compact` | `SmoothH2PointBound.lean:14` | PASS；真实连续函数在紧集限制体积上具有 L² 资格。 |
| 2 | `compact_integral_norm_le_l2` | `SmoothH2PointBound.lean:20` | PASS；有限测度下实际 Cauchy–Schwarz 给 ∫‖F‖≤√V‖F‖₂。 |
| 3 | `convex_smooth_h2_point_bound` | `SmoothH2PointBound.lean:32` | PASS；实际平均 Taylor 余项和真实三个 L² 范数给低维点值界，以 V>0 合法除法。 |
| 4 | `tensor_norm_le_coordinate_sum` | `TensorCoordinateL2.lean:13` | PASS；固定张量重构控制真实算子范数，全部有序坐标纳入。 |
| 5 | `tensor_L2_le_coordinate_sum` | `TensorCoordinateL2.lean:26` | PASS；实际 L² Minkowski 和明确 MemLp 资格给坐标范数和界。 |
| 6 | `convex_smooth_h2_coordinate_point_bound` | `TensorCoordinateL2.lean:35` | PASS；真实一阶导数与 iteratedFDeriv 一阶范数一致，点值界转为全部一、二阶坐标 L² 范数。 |
| 7 | `coordinateDerivative_sub` | `SmoothH2UniformLimit.lean:15` | PASS；在所需 Cᵏ 正则性下，实际 iteratedFDeriv 与坐标求值保持差。 |
| 8 | `bochnerL2Norm_sub_le_errors` | `SmoothH2UniformLimit.lean:22` | PASS；真实三角不等式，三个函数均明确在 L² 中。 |
| 9 | `convex_smooth_h2_uniform_limit` | `SmoothH2UniformLimit.lean:30` | PASS；全部有限坐标强 L² 收敛推出一致 Cauchy、实际实数极限及连续一致极限，没有点态收敛前提。 |
| 10 | `coordinateDerivative_one` | `WeakH2LocalContinuous.lean:15` | PASS；一阶坐标导数精确为原 fderiv 的标准方向值。 |
| 11 | `coordinateDerivative_two` | `WeakH2LocalContinuous.lean:21` | PASS；二阶坐标精确为实际 Fréchet 张量在有序两方向上的值。 |
| 12 | `WeakSobolevJet.exists_local_continuous_representative` | `WeakH2LocalContinuous.lean:30` | PASS；任意内部正体积紧凸 K 上，同一原弱 H² 卷积一致收敛到连续函数，且该函数与原 value a.e. 相同。 |
| 13 | `WeakSobolevJet.exists_continuous_representative` | `WeakH2Continuous.lean:15` | PASS；同一序列的 limUnder 经真实内部闭球得到开域 S 上单一连续代表和每个内部点收敛。 |
| 14 | `WeakSobolevJet.continuous_representative_unique` | `WeakH2Continuous.lean:61` | PASS；任意维数下，开域上的两个连续 a.e. 代表在 S 上逐点相等，结论不扩大到域外。 |

## 实际低维点值估计和 L² 资格

第1项通过连续平方范数在紧集上的可积性证明 MemLp，而非直接将可能无穷的 eLpNorm 转成实数。第2项在限制体积上建立有限测度实例，对常数1和 ‖F‖ 使用实际 Cauchy–Schwarz；随后以已证明的 L² 平方积分身份和非负性开平方。该辅助界无需正体积，零测紧集也合法。

第3项才引入 V=volume.real K>0。对 x∈K 令 g(y)=f(y)+Df(y)(x−y)，由真实直径上界和 CLM 算子范数得

\[
\left|\int_Kg\right|\le\sqrt V\|f\|_2+D\sqrt V\|Df\|_2.
\]

已检查所调用的实际平均 Taylor 余项：对全空间 C² 的 f、紧凸 K 和 d≤3，有 |Vf(x)−∫K g|≤2D²√(V∫K‖D²f‖²)。这里 D²f 是 `iteratedFDeriv ℝ 2 f` 的真实多线性导数。C² 和紧性使值、Df、D²f 及参与比较的函数全部可积，平方根严格等于 √V‖D²f‖₂。正 V 消去后得到

\[
|f(x)|\le\frac{\sqrt V}{V}
\left(\|f\|_2+D\|Df\|_2+2D^2\|D^2f\|_2\right).
\]

该界对全部闭 K 中的点成立，没有用上确界控制 Hessian，也没有用积分平均替代实际点值。其常数依赖局部 K 的体积和直径；本批没有把它宣称为任意开域的全局统一嵌入常数。

## 张量坐标与真实范数

已展开 `coordinateTensorEval`、`coordinateDerivative`、`tensorCoordinates`、`tensorReconstruction` 和 `tensorCoordinateBound`。坐标是所有 `Fin k → Fin d` 标准方向元组上的真实多线性张量求值。基上的多线性映射唯一性证明坐标映射单射；其固定线性左逆给 `tensorReconstruction_coordinates`，保证重构实际还原 A。

重构连续性由有限维理论提供，但映射仅依赖 d、k，常数明确为 C(d,k)=‖tensorReconstruction‖+1。因此没有借助随网格或状态变化的有限维自动连续性偷取统一常数。坐标函数空间使用有限 Pi 范数，先以每个坐标绝对值不超过总和控制其范数，再用重构算子范数得第4项。

第5项调用已读取的 `bochnerL2Norm_le_sum`：真实点态范数界经 Lp 范数比较及有限 Minkowski 得到 ‖F‖₂≤C(d,k)∑ᵥ‖Fᵥ‖₂。F 和各坐标的 MemLp 均由连续性与紧性提供；没有将“和的 L² 范数”等同于“L² 范数之和”。第6项用 `norm_iteratedFDeriv_one` 对齐真实 Df 与一阶张量范数，保留全部一阶和二阶有序坐标。混合二阶坐标的重复仅进入有限求和，不被误读为弱 jet 原 Sym 范数的精确等式。

## 强 L² 收敛到一致 Cauchy 和连续极限

第9项完整类型明确输入一个全空间 C² 序列 Fₙ，以及真实 L² 目标 a、所有 bᵥ、cᵥ，假定值及全部一阶、二阶坐标分别强 L² 收敛。它作为一般充分准则不要求目标字段预先满足弱导数关系；第12项会用真实 jet 供应这些字段和收敛，而不会把目标连续性作为输入。

证明定义 Eₙ 为值误差加 D·C(d,1) 乘一阶误差和，再加 2D²·C(d,2) 乘二阶误差和。有限求和与极限给 Eₙ→0。对 Fₘ−Fₙ 应用第6项，使用实际坐标导数线性和第8项，得到对全部 x∈K 同时成立的

\[
|F_m(x)-F_n(x)|\le B(E_m+E_n),\qquad B=\sqrt V/V.
\]

同一个 N 控制两指标及全部 x，因此是实际一致 Cauchy，不是各点分别 Cauchy 的替代。随后实数完备性给每点极限，mathlib 的 `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto` 给一致收敛，`TendstoUniformlyOn.continuousOn` 给连续性；这两个实际定理也已核对。K 外的选择值任意，未声称所得函数在全空间连续。没有预设点态极限、预设连续代表或额外支配函数。

## 原全部弱 H² 与同一卷积的 a.e. 身份

已读取原 `weakJetSubmodule`：所有阶数和所有方向都通过全部 `SpatialTest S` 的分布导数身份连接，field 是真实 Euclidean 分量的 L² 类。第12项接受任意原 `WeakSobolevJet d 2 (volume.restrict S) S`；没有附加光滑、节点采样或有界导数条件。

Uₙ 始终是原 value 的 `zeroExtendLp` 与同一 `spatialMollifier d n` 的真实卷积。zeroExtendLp 是 L² 零延拓，域内仅 a.e. 等于原值；未宣称它全空间保持弱 H²。已核对依赖 `local_mollification_strong_h2` 及其局部交换：紧 K⊆开 S 给统一正缓冲，缩小核最终使所有反射支撑 x−y 留在 S，因而能使用原局部分布弱链。

目标 bᵥ 是 field₁ 的 Sym.cons(v₀,nil) 分量；cᵥ 是 field₂ 的 Sym.cons(v₁,Sym.cons(v₀,nil)) 分量。第10、11项精确匹配实际导数与既有一阶、二阶卷积定理的方向次序。全部有限有序方向都供应，不遗漏混合坐标。限制测度单调性给这些真实 L² 字段在 K 上的资格；强收敛来自同一 Uₙ，而不是分别选择不相容的三个光滑序列。

局部一致极限 f 与原 value 的 a.e. 身份使用实际 `spatialMollifier_converges`：归一化非负光滑核的 rOut→0、rOut≤2rIn 以及原 L² 的局部可积性，给全空间零延拓值的 a.e. 卷积极限。将其限制到 K，再与一致极限的点态极限作 Hausdorff 极限唯一性比较，并调用 zeroExtendLp 域内 a.e. 身份。不存在对任意 L² 代表逐点取值后宣称其连续的操作。

## 内部闭球与单一代表、唯一性

第13项定义 f(x)=limUnder atTop(Uₙ(x))。对每个 x∈S，开放性给 ball(x,ε)⊆S；取 r=ε/2>0，真实 closedBall(x,r)⊆S，紧凸、正有限体积，直径≤2r。这些条件内部证明，不要求 S 本身有界、凸或有全域正体积下界。

在该闭球上，第12项给一个连续一致极限 g。对球中每个 y，极限唯一性给 limUnder(Uₙ(y))=g(y)，故同一个 f 在 x 的真实邻域与 g 相同，得到 ContinuousAt f x，进而 ContinuousOn f S。相同论证给每个内部点的 Uₙ(x)→f(x)。拼接没有随点选择不同卷积或仅在交叠处 a.e. 对齐局部函数。

全域 a.e. 身份直接复用同一全空间卷积的一个 a.e. 收敛集合及原 zeroExtendLp 身份；未对不可数多个局部异常零测集取并。第14项用开放集上 Lebesgue 体积的正性，将两个连续代表的 a.e. 相等提升为 EqOn S。已读取 mathlib 的 `Measure.eqOn_open_of_ae_eq`：不相等点构成开放零测集，必为空。该唯一性本身不需要低维限制；存在性才使用 d≤3。

空 S 和 d=0 没有新增排除条件；空域结论按定义为空范围，零维内部闭球的正有限体积由同一体积性质保证。结论对域外值不作唯一性要求，更没有边界或 closure S 上的连续性断言。

## 依赖版本、本机构建和公理

五模块导入闭包共107个 Carleman 模块，新增恰为本批5模块，其余102模块与 base 逐字节不变。又核对已验收版本：C131 `WeakH2LocalSmoothing` 的101模块闭包相对 base 不变；C130 `TensorCoordinateNorm` 的47模块闭包相对 `a5c68e2aaa4da98efe42da31ed0c1da04ba99952` 不变；C128 `SmoothAveragedTaylor` 的56模块闭包相对 `c8377e5f743689641ab84d5049b4d0fb291d29f5` 不变。没有混用改变后的旧 declaration_version。

原稿、已读治理协议、工具链pin与CI工作流自 T113 不变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean固定4.35.0，mathlib pin及本机实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机mathlib工作树干净。root显式导入5模块，`tools/CheckAxioms.lean` 对14项均含完整类型和公理输出，并递归审计全部Carleman声明。

实际读取 `/tmp/carleman-h2-continuous-target.log` 的3284 jobs成功记录及 `-full.log` 的3850 jobs成功记录，后者末行为6631声明递归公理审计PASS。固定 `-local-axioms.txt` 为 **1,986,368 bytes**，SHA256 **`364b815fa7148c77283e253a1b86c6b6a9a114941c28fbb333aaccf5d7aef157`**。14项完整展开类型逐一核对；全部2275条显式公理记录中2267非空、8无公理，无 `propext`、`Classical.choice`、`Quot.sound` 之外的公理，无sorryAx。

## 实际同 SHA CI 和原始远端证据

本 Agent 自行经 GitHub connector 查询 [main CI 39202007650 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39202007650/attempts/1)。实际run为main/push、completed/success，head SHA精确匹配固定提交。三个job均completed/success：state-check **117896769163**、lean **117896769358**、dashboard / snapshot **117897530111**。

实际同run原始artifact为 `lean-ci-result` **12164590365**、`lean-declaration-evidence` **12164381078**，两份元数据中的workflow_run.head_sha均精确匹配。本 Agent 自行通过 `gh run download 39202007650` 下载至 `/tmp/carleman-h2-continuous-main-ci` 与 `-main-axioms`。

实际 `-main-ci/result.json` 为PASS，`checked_sha=source_head_sha=fa02c379c6ee0f59172dadc1401b9a535e6d3c9c`，targets为Carleman，`finished_at=2026-10-19T04:58:49.565353+00:00`；ci_url与上述run/attempt一致，Lean提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

独立逐字节比较远端 `-main-axioms/axioms.txt` 与固定本机副本，完全一致：**1,986,368 bytes**，SHA256 **`364b815fa7148c77283e253a1b86c6b6a9a114941c28fbb333aaccf5d7aef157`**。另逐名确认远端14/14完整类型，实际末行为 **6631项全声明递归审计PASS**。未采用其他SHA或未来工作区产物。

## 验收决定

**C132：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 14项声明未发现需要修复的数学缺陷。实际低维点值估计、固定张量坐标重构、完整强 L² 收敛到一致 Cauchy、同一原弱 H² 卷积的 a.e. 身份、真实内部闭球拼接及连续代表唯一性均已独立核对；同SHA三项正式CI和自行下载的原始公理证据均已核实。

原论文所需 closure Ω 上的连续代表和边界节点资格仍未由本批证明；完整 P1 插值、全局允许权和P011不提升，原文保持 **14/26**。本次仅新建本报告，未修改实现、台账、原稿或root导入，未commit/push。以上签发UTC固定，通知主Agent后不再变更报告或时间戳。
