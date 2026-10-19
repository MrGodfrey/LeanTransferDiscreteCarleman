# T119 / C135 独立本机验收

- `checked_sha`: `6f051d6775dc64fbf1ccf1e93df232c43dee616f`
- `base_commit`: `4e727b83c3fcb821432ba4089e6f9ea0c9e0a277`
- `reviewed_at`: `2026-10-19T05:25:10+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：有界开凸域上全部原弱 H² 状态、d≤3、同一闭包连续代表在全部实际闭单纯形上的局部节点值误差。右端是同单元原弱 Hessian 的局部 L² 能量。梯度误差、H¹₀ 状态的边界零值、完整 conforming 插值及全域允许权仍待，P011 不提升，原文保持 **14/26**。

本 Agent 独立读取固定 git 对象的五模块完整证明、12项完整展开类型及关键依赖，对照原 `paper/main.tex` Section 6 P1 设置（1466–1476）和 Step 2 的节点插值及 `eq:p1-interpolation`、`eq:p1-interpolation-energy`（1527–1548）。已读取固定 T119 分析、MATH_SPEC 和 C135 台账。执行者说明及 CI 未替代数学审查；工作树 T120 及其他未来增量、变化中的 `.ci` 产物均排除。

## 全部12项声明

以下名称省略公共前缀 `Carleman.`，位置以 `Carleman/Spatial/` 为根；顺序与固定 JSON 和 C135 台账逐项一致。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `bochnerL2Norm_reverse_triangle` | `StrongL2NormLimit.lean:14` | PASS；真实 Lp 范数的反三角不等式，两函数明确具有 MemLp。 |
| 2 | `bochnerL2Norm_tendsto_of_error` | `StrongL2NormLimit.lean:21` | PASS；真实强 L² 误差趋零推出范数收敛。 |
| 3 | `l2_square_integral_tendsto_of_error` | `StrongL2NormLimit.lean:29` | PASS；明确 L² 资格下，以范数平方身份得到实际平方积分收敛。 |
| 4 | `l2_square_bound_of_ae_of_bound_tendsto` | `StrongL2NormLimit.lean:36` | PASS；实际 Fatou/下半连续性把收敛的数值上界传给 a.e. 极限，未增加支配函数前提。 |
| 5 | `smooth_hessian_integral_le_coordinate_sum` | `SmoothHessianCoordinateEnergy.lean:14` | PASS；真实二阶 Fréchet 张量的局部能量由全部有序坐标能量控制。 |
| 6 | `hessian_coordinate_energy_tendsto` | `SmoothHessianCoordinateEnergy.lean:29` | PASS；各真实坐标强 L² 收敛给全部有限坐标平方积分和的极限。 |
| 7 | `simplexNodalInterpolant_tendsto` | `SimplexH2ValueLimit.lean:14` | PASS；实际重心坐标有限和将全部顶点值收敛传到节点插值，在任意固定 x 成立。 |
| 8 | `simplexNodal_h2_value_integral_of_limit` | `SimplexH2ValueLimit.lean:22` | PASS；真实光滑值误差、节点极限和 MemLp/Fatou 给同单元极限函数的局部值界。 |
| 9 | `WeakSobolevJet.exists_smooth_h2_pointwise_approximation` | `WeakH2NodalSmoothing.lean:14` | PASS；同一实际向内卷积序列的闭域强逼近，与闭包代表唯一性一起对齐任意指定的原连续代表。 |
| 10 | `derivativeComponent_local_integral_le` | `WeakH2NodalValue.lean:15` | PASS；真实分量投影逐点范数界经 a.e. 身份和可积性给局部平方积分界。 |
| 11 | `WeakSobolevJet.simplex_nodal_value_integral` | `WeakH2NodalValue.lean:25` | PASS；给定任意合法闭包代表，其真实节点值误差由同一单元原 field₂ 能量控制，平滑序列和强收敛内部供应。 |
| 12 | `WeakSobolevJet.exists_nodal_value_representative` | `WeakH2NodalValue.lean:70` | PASS；先内部选择同一个闭包连续代表，再对全部单元和直径上界给值误差，无原状态光滑性或目标估计前提。 |

## 真实强 L² 极限与 Fatou

第1项将 bochnerL2Norm 转为真实 `MemLp.toLp` 的范数，利用 `MemLp.toLp_sub` 和原 Lp 范数反三角不等式。第2项据此夹逼，第3项使用实际平方积分等于 L² 范数平方的身份。这些步骤均要求明确的 MemLp，未利用 ENNReal.toReal 将无穷范数变成零。

第4项在 Bₙ→b、b≥0 时，对每个 ε>0 取得最终的能量界≤b+ε，调用已读取的 `l2_square_bound_of_ae_tendsto`，再令 ε 任意。依赖通过真实 `Lp.eLpNorm_le_of_ae_tendsto` 和有限范数转换实现 Fatou 传递。它只要求实际 L² 资格和 a.e. 收敛，没有未经证明的积分极限交换、支配函数或强收敛假设加到左侧误差上。

第5项对全空间 C² 函数在紧 K 上使用实际 `tensor_norm_sq_le_coordinate_sum`，所有坐标及张量平方范数均有真实可积性，故可以积分比较并交换有限和与积分。第6项将第3项用于每个有序二阶方向，再取有限和极限。被证明收敛的是完整坐标能量和；没有直接假定算子范数 Hessian 能量的强极限。

## 真实节点插值与光滑值误差的极限

`simplexNodalInterpolant` 是原真实单纯形 T 的仿射重心插值。第7项展开成 ∑ᵢ Fₙ(T.points i)·λᵢ(x)，每个 λᵢ(x) 与 n 无关，所以全部真实顶点的收敛给实际插值在任意固定 x 的收敛。不是另选一个仅有 a.e. 身份的多项式，也没有对 L² 等价类直接采样节点。

第8项在闭单元 K 上假定连续极限 f、光滑序列 Fₙ、全部点（因而包括全部顶点）的收敛和二阶坐标对 Zᵥ 的强 L² 收敛。已核对这些是中间传递引理的显式前提；第11、12项会由原弱 H² 数据内部证明它们。

误差 Fₙ−I_KFₙ 的 a.e. 极限由实际函数值与第7项给出；f−I_Kf 在紧 K 上连续，近似误差也连续，故极限及每个近似都有真实 MemLp。这里仿射映射的有限维自动连续性只用于资格，不提供任何统一误差常数。

已重新核对 C128 的实际光滑结论：

\[
\int_K|F_n-I_KF_n|^2\le16D^4\int_K\|D^2F_n\|^2.
\]

该结论使用真实平均 Taylor 余项、闭单元全部节点、正单元体积及精确体积抵消。第5项把右侧变成 16D⁴C(d,2)²∑ᵥ∫K|∂ᵥFₙ|²，第6项给此数值上界收敛到 16D⁴C(d,2)²∑ᵥ∫K|Zᵥ|²。第4项遂传给实际极限误差。没有把全域平滑误差当成单元能量，也没有留下平滑半径相关项。

## 同一实际光滑序列与闭包代表对齐

已读取 C134 的 `WeakH2ClosureSmoothing`、`WeakH2ClosureContinuous`，以及实际 `InwardMollification`、`InwardMollifierSequence`、`InwardApproximationLimit`。原 u 是全部 `WeakSobolevJet d 2 (volume.restrict S) S`，field₁、field₂ 通过全部真实 SpatialTest 的分布导数链联系；本批没有缩小原弱状态类。

平滑序列由同一个原 value 的 L² 零延拓、同一个核序列 φ 和实际向内仿射拉回构成。对固定内部点 a，闭包的每个向内像是紧集并有正域内缓冲；φₙ≥n 的同一几何选择使全部反射核支撑留在原 S。实际一、二阶导数分别带 inwardRatio 和其平方，这些因子连同真实 L² 强连续性一起趋于正确原弱场。零延拓只用作 L² 数据，未当作跨边界 H² 延拓。

第9项从此取得同一 Fₙ 在整个 closure S 上的值、全部一阶和二阶坐标强 L² 收敛。低维点值准则产生连续一致极限 g。真实 `l2_limit_ae_eq_of_ae_tendsto` 将同一序列的强 L² 极限和点态极限识别为同一 L² 类，再用闭包连续代表唯一性把 g 与任意指定的合法 f 在整个 closure S 上对齐。

闭包唯一性先在开放 S 上将连续函数的 a.e. 相等提升为逐点相等，再以 S 在 closure S 中稠密和双方连续性延伸到边界。因此获得每个闭包点的 Fₙ(x)→f(x)，包括边界顶点；没有将原 L² 代表的任意边界值用作节点值。此构造不假设目标 f 本身光滑，也不需要额外插值估计。

## 同单元局部原 Hessian、常数与量词

第11项令 K 为真实闭单纯形，hKS 仅要求 K⊆closure S。它从一个真实顶点推出 closure S 非空，从而取得 S 内点 a；没有额外添加 S 非空假设。第9项的同一全闭包序列随后限制到 K。每个坐标的强误差有真实 MemLp，因此限制测度的单调性及有限 eLpNorm 的实数转换合法，给 **K 上**的坐标强收敛。

Zᵥ 正是原 field₂ 中 Sym.cons(v₁,Sym.cons(v₀,nil)) 分量的 L² 零延拓。代码使用的 `derivativeComponent_zeroExtend` 已逐项核对：它只是 L² 类的分量投影与零延拓交换，不需要 H¹₀ 前提；其所在模块名没有把 Dirichlet 条件暗中加给本声明。

第10项利用 `derivativeComponent_ae` 和真实 Euclidean 纤维的坐标范数界，得到每个 ∫K|Zᵥ|²≤∫K‖zeroExtendLp(field₂ u)‖²。对全部 `Fin 2 → Fin d` 求和，其基数为 d²，因此

\[
\int_K|f-I_Kf|^2
\le16D^4C(d,2)^2d^2
\int_K\|\operatorname{zeroExtendLp}(\mathrm{field}_2u)\|^2.
\]

d² 是对有序坐标（包括混合方向重复）的安全上界，并非声称该坐标和恰等于原 Sym 纤维范数。C(d,2)=‖tensorReconstruction‖+1 是固定维数和阶数的映射常数；有限维连续性没有引入单元或网格依赖。最终常数不含 S 的直径/体积、a、核半径、状态或网格数；D⁴ 是目标单元直径上界的正确显式尺度。

右端积分从头到尾在同一个 K 上。由零延拓的真实 indicator a.e. 身份，它就是 K∩S 上的原弱 Hessian 能量；对于 K⊆closure S 的原开凸域，边界差为零测，符合原单元局部 L² 能量。已核对固定 mathlib 的 `Convex.addHaar_frontier` 及原零延拓身份以确认这一数学解释；本报告不把该解释冒充本批新增的另一条 Lean 声明。没有用整个 S 的能量代替，也没有漏掉边界顶点的连续代表极限。

第12项的完整量词是：对每个原 u，先选择一个 closure S 上连续且 a.e. 等于 value u 的 f，然后对 **全部** T、全部 D 及原直径上界给估计。同一个 f 可在所有单元的共同节点使用；不是每单元重新挑选不同边界值。其存在性由已验收 C134 内部供应，不再将连续代表或平滑序列作为最后结论的输入。

原 d=2、3 均被 d≤3 覆盖；空 S 的存在代表结论仍成立且无可容纳的非空单元，d=0 不引入除以 d 的步骤。此处不需要形状参数；本批仅给局部值界，不能由此推断梯度界或 H¹₀ 边界零值已经完成。

## 原文对应与范围

原 Step 2 对全部 D(A)⊆H² 状态使用同一个闭包连续代表定义节点插值，随后以单元权比较、ℓK≈hK 和全网格求和得到全域加权值/梯度估计。本批已将光滑局部值估计扩展到全部原弱 H²，且右端为同单元局部原二阶弱场，平方根给正确 D² 值误差尺度。

本批没有证明弱梯度误差、H¹₀ 连续代表的边界零值、完整 conforming 插值成员或全域允许权组装。闭包连续性已由前阶段供应，不应继续误称只完成内部代表；但也不能把本局部值界升级为完整 `eq:p1-interpolation`、P011 或 `prop:p1` 的 PAPER 完成。

## 固定依赖、构建和公理

五模块的 Carleman 导入闭包共175模块，新增恰为本批5模块，其余170模块与 base 逐字节不变。关键已验收版本闭包比较：C134 `WeakH2ClosureContinuous` 的134模块相对 base 不变；C132 `WeakH2Continuous` 的107模块相对 `fa02c379c6ee0f59172dadc1401b9a535e6d3c9c` 不变；C128 `SmoothH2NodalError` 的97模块相对 `c8377e5f743689641ab84d5049b4d0fb291d29f5` 不变；C130 `TensorCoordinateNorm` 的47模块相对 `a5c68e2aaa4da98efe42da31ed0c1da04ba99952` 不变。没有混用改变后的旧 declaration_version。

原稿、已读治理协议、工具链pin和CI工作流自 T116 不变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean固定4.35.0，mathlib pin及本机实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机mathlib工作树干净。root显式导入5模块，`tools/CheckAxioms.lean` 对12项均含完整类型及公理输出，并递归审计全部Carleman声明。

实际读取 `/tmp/carleman-weak-nodal-value-target.log` 的3352 jobs成功记录及 `-full.log` 的3865 jobs成功记录，后者末行为6678声明递归公理审计PASS。固定 `-local-axioms.txt` 为 **2,016,584 bytes**，SHA256 **`017de86f344bed6ac7a09e2887e32f46f2363e657c157dd5d93d8db38b88528e`**。12项完整展开类型逐一核对；全部2316条显式公理记录中2308非空、8无公理，均无 `propext`、`Classical.choice`、`Quot.sound` 之外的公理，无sorryAx。

## 实际同 SHA CI 和原始远端证据

本 Agent 自行经 GitHub connector 查询 [main CI 39204037128 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39204037128/attempts/1)。实际run为main/push、completed/success，head SHA精确匹配固定提交。三个job均completed/success：state-check **117902872392**、lean **117902872726**、dashboard / snapshot **117904022682**。

同run实际artifact为 `lean-ci-result` **12165351023**、`lean-declaration-evidence` **12164654378**，两份元数据的workflow_run.head_sha均精确匹配。本 Agent 自行通过 `gh run download 39204037128` 下载至 `/tmp/carleman-weak-nodal-value-main-ci` 与 `-main-axioms`。

实际 `-main-ci/result.json` 为PASS，`checked_sha=source_head_sha=6f051d6775dc64fbf1ccf1e93df232c43dee616f`，targets为Carleman，`finished_at=2026-10-19T05:23:16.828732+00:00`，ci_url与上述run/attempt一致；Lean提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

独立逐字节比较远端 `-main-axioms/axioms.txt` 与固定本机副本，完全一致：**2,016,584 bytes**，SHA256 **`017de86f344bed6ac7a09e2887e32f46f2363e657c157dd5d93d8db38b88528e`**。另逐名确认远端12/12完整类型，实际末行为 **6678项全声明递归审计PASS**。未使用其他SHA或未来工作区产物。

## 验收决定

**C135：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 12项声明未发现需要修复的数学缺陷。同一闭包代表先于全部单元、真实节点插值极限、明确 MemLp 与 Fatou、全部原弱 H² 数据内部供应、同单元原弱 Hessian 能量及仅依维数的常数均已独立核对；同SHA三项正式CI和自行下载的原始公理证据已核实。

梯度误差、H¹₀ 边界零值、完整 conforming 插值和全域允许权仍待，P011不提升，原文保持 **14/26**。本次仅新建本报告，未修改实现、台账、原稿或root导入，未commit/push。以上签发UTC固定，通知主Agent后不再变更报告或时间戳。
