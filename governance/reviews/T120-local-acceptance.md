# T120 / C136 独立本机验收

- `checked_sha`: `a26158d00376e85866c536aa366239af41c83f97`
- `base_commit`: `6f051d6775dc64fbf1ccf1e93df232c43dee616f`
- `reviewed_at`: `2026-10-19T05:32:00+00:00`
- `reviewer`: `/root/accept_spatial_lemma`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：有界开凸域上原全部弱 H² 状态、d≤3、同一个闭包连续代表在全部实际闭单纯形上的局部节点值与完整弱梯度误差；右端保持同单元原弱 Hessian 能量。H¹₀边界零值、全局 conforming 插值及允许权组合尚待，P011不提升，原文保持 **14/26**。

本 Agent 独立读取固定 git 对象的四个完整模块、9项实际展开类型、关键依赖及原稿 Section 6 P1 设置和 Step 2（`paper/main.tex:1462–1505,1523–1548`），并读取固定 T120 分析、MATH_SPEC、C136。已核实 AGENTS、运行/状态协议、里程碑、覆盖协议及原稿相对 T117 已读版本不变。执行者说明、既有报告和 CI 未替代实际语义核查；未来边界零值工作树增量及变化中的 `.ci` 文件均排除。

## 全部9项声明

以下省略公共前缀 `Carleman.`，模块位于 `Carleman/Spatial/`；清单与固定 C136、T120 和 `/tmp/carleman-weak-nodal-gradient-declarations.json` 逐项一致。

| # | 声明 | 固定模块及行 | 独立结论 |
|---|---|---|---|
| 1 | `l2_error_sub_constant_tendsto` | L2ConstantShiftLimit:12 | PASS；有限测度上真实强 L² 收敛减去收敛常数后仍成立，所有 MemLp 资格明确。 |
| 2 | `simplexNodal_affineDerivative_eq` | SimplexNodalDerivativeLimit:14 | PASS；实际仿射导数与真实节点导数线性映射由 Fréchet 导数唯一性识别。 |
| 3 | `simplexNodalDerivative_tendsto` | SimplexNodalDerivativeLimit:19 | PASS；真实全部顶点值收敛给同一节点插值导数的算子范数收敛。 |
| 4 | `firstDerivativeFiber_norm_sq` | SimplexNodalDerivativeLimit:28 | PASS；任意真实一次 DerivativeFiber 范数平方精确展开为全部 d 个坐标平方和。 |
| 5 | `firstDerivativeFiber_sub_norm_sq` | SimplexNodalDerivativeLimit:33 | PASS；完整弱梯度纤维与真实仿射梯度之差准确展开，无漏坐标。 |
| 6 | `simplexNodal_h2_gradient_integral_of_limit` | SimplexH2GradientLimit:14 | PASS；同一 C² 序列的节点、一阶、二阶强极限把显式光滑梯度界传到原极限坐标。 |
| 7 | `derivativeOneFiber_local_sub_integral_eq` | WeakH2NodalGradient:14 | PASS；真实局部 Lp 梯度残差积分与全部分量残差平方积分和严格相等。 |
| 8 | `WeakSobolevJet.simplex_nodal_gradient_integral` | WeakH2NodalGradient:35 | PASS；完整原弱 H² 自动供应同一闭域光滑序列，右端为同 K 上真实 field₂ 能量。 |
| 9 | `WeakSobolevJet.exists_nodal_h2_representative` | WeakH2NodalGradient:98 | PASS；内部先选一个闭包连续代表，再对所有单元同时给真实值与完整弱梯度估计。 |

## 真实节点导数及有限维连续性的用途

已读取 `SimplexNodalInterpolation` 与 `SimplexReferenceInverse`：T 是实际 d 维非退化单纯形，其 d+1 个顶点形成真实 AffineBasis；I_Tc=Σcᵢλᵢ 是真实重心坐标仿射多项式，保持每个顶点值。`simplexNodalDerivativeLinear T c` 定义为 ΣcᵢDλᵢ，并已通过逐项 Fréchet 求导证明它在每点都是 I_Tc 的真实导数。

第2项将该导数与 `affineScalarDerivative` 在0处用导数唯一性识别；两者均为同一实际仿射函数的导数，不是给任意矩阵赋予导数名称。第3项先以有限 Pi 拓扑得到完整节点向量收敛，再由真实节点导数线性映射的连续性取得 CLM 空间中的收敛，即算子范数拓扑中的导数收敛。

这里 T 在极限之前固定。`continuous_of_finiteDimensional` 只用于传极限，没有将该节点导数映射可能依赖 T 的范数当作统一常数。后续也不要求收敛速度对全部单元统一：对每个固定 T 传递带同一显式常数的不等式后，才取得全部 T 的结论。最终常数中没有任何此映射的范数或收敛速度。

## 减常数极限、全部梯度分量和真实积分

第1项对任意有限测度 ν 证明

\[
\|(F_n-c_n)-(f-b)\|_2
\le\|F_n-f\|_2+|c_n-b|\,\|1\|_2\longrightarrow0.
\]

常数函数1的 MemLp 由有限测度供应，常数倍和各个差的 MemLp 由真实 L² 运算供应；使用的是实际常数函数 L² 范数。它在固定 K 上的大小只用于证明乘趋零标量仍趋零，不进入最终统一误差系数。

第4项由 `EuclideanSpace.real_norm_sq_eq` 和 `Sym.oneEquiv` 的真实双射把全部一次多重指标重排为 Fin d。已读取 `FirstOrderSobolevJet.derivativeOneFiber`：它通过所有标准方向的 CLM 求值形成 Euclidean 一阶纤维。第5项于是给任意 w、A 的精确恒等式

\[
\|w-\mathrm{fiber}(A)\|^2
=\sum_{i=1}^{d}\bigl(w_i-Ae_i\bigr)^2.
\]

这是完整 Euclidean 梯度残差，不是单方向导数、最大坐标或 CLM 算子范数的替代。第7项对实际全空间 Lp 纤维 w 用 `derivativeComponent_ae`，将该点态身份转为限制在 K 的 a.e. 身份；有限个坐标通过 `ae_all_iff` 合并，没有不可数零测集交换。K紧给有限测度，每个真实分量减常数属于 L²，平方可积后才交换有限求和与积分。左侧亦是 L² 纤维减有限测度上的常量纤维，真实可积，未利用全定义积分的默认零值。

## 同一光滑序列的梯度估计取极限

第6项明确接受同一序列 Fₙ 的 C² 正则性、全部真实顶点值极限、全部一阶方向的强 L² 极限 Gᵢ，以及全部有序二阶坐标的强 L² 极限 Zᵥ。令 Aₙ=D(I_TFₙ)、B=D(I_Tf)。第3项给 Aₙ→B，连续求值给 Aₙeᵢ→Beᵢ；第1项再给 DᵢFₙ−Aₙeᵢ→Gᵢ−Beᵢ 的强 L² 收敛。

已读取 `StrongL2NormLimit`：真实 Lp 范数的反三角不等式将强误差趋零转为范数收敛，再平方得到真实平方积分收敛。因此左侧所有 d 个梯度残差积分之和实际收敛，不是仅有未清偿的弱收敛或下半连续性前提。

右侧调用 `hessian_coordinate_energy_tendsto`，对全部 v:Fin 2→Fin d 的强 L² 极限分别转为平方积分极限，再取有限和。`smooth_hessian_integral_le_coordinate_sum` 先对真实二阶 Fréchet 张量使用固定维数重构界，所有算子范数平方与坐标平方均在紧 K 上真实可积。证明没有假称算子范数 Hessian 能量恰等于原对称纤维范数。

已重新读取 C129 的 `simplexNodal_smooth_h2_gradient_integral`：真实内球、平均 Taylor 仿射多项式、局部仿射导数界、全梯度均值估计及正体积消去给显式系数

\[
Q(d,\kappa)=2^dd+128\kappa^2\|\mathrm{derivativeOneFiber}_d\|^2.
\]

第6项在每个 n 对该光滑不等式应用 Hessian 坐标界，再同时对左右两侧取极限，取得

\[
\sum_i\int_K(G_i-Be_i)^2
\le Q(d,\kappa)D^2C(d,2)^2\sum_v\int_KZ_v^2,
\qquad C(d,2)=\|\mathrm{tensorReconstruction}_{d,2}\|+1.
\]

所有积分仍在同一个真实闭单元 K 上。r>0、D≥0、ball(a,r)⊆K、D≤κr 和实际点对距离≤D 均在完整类型中保留；hshape与r>0、D≥0允许内部推出κ≥0。非负系数保证取界方向正确，D²是平方梯度误差的正确尺度。

## 全部原弱 H²、同单元能量与量词

第8项的 u 是原完整 `WeakSobolevJet d 2 (volume.restrict S) S`，没有光滑状态、有限维状态或 H¹₀ 条件。中间声明接收任意合法闭包连续代表 f；通过实际单纯形顶点及 K⊆closure S 推出 S 非空，内部选一个域内点调用已验收 `exists_smooth_h2_pointwise_approximation`。已读其证明：同一个真实向内卷积序列具有全部原弱字段的强极限，紧闭域上的一致极限与 f 通过闭包代表唯一性识别，因而所有边界顶点也取得真实点态极限。

Gᵢ取原 field₁ 的真实分量的 L² 零延拓，Zᵥ取原 field₂ 中 `Sym.cons (v 1) (Sym.cons (v 0) nil)` 的真实分量零延拓。完整一阶和二阶强收敛从 closure S 限制到 K：先证明大集合上的误差 MemLp，再使用限制测度单调性及有限 eLpNorm 的 toReal 单调性。没有把可能无限的 seminorm 转成实数后错误比较。

已读取 `derivativeComponent_zeroExtend` 的实际证明：对任意阶纤维、仅在 S 可测条件下，分量投影与真实 Lp 零延拓严格交换。虽位于 DirichletZeroExtension 模块，该声明没有 Dirichlet/H¹₀ 前提。随后第7项把坐标残差平方积分和精确识别为原全弱梯度减真实节点仿射导数的纤维积分。

对每个 Zᵥ，真实 Euclidean 坐标范数界给同 K 上的 ∫Zᵥ²≤∫‖zeroExtendLp(field₂u)‖²；全部有序对的数量是 d²。混合坐标重复已纳入该安全上界，未假称与 Sym 纤维范数精确相等。最终得到

\[
\int_K\|\widetilde{\nabla u}-\mathrm{fiber}(D I_Tf)\|^2
\le Q(d,\kappa)D^2C(d,2)^2d^2
\int_K\|\operatorname{zeroExtendLp}(\mathrm{field}_2u)\|^2.
\]

右侧从未改成整个 S 的能量。零延拓是实际 indicator 的 Lp 类，因此是 K∩S 上的原 Hessian 能量。对开凸 S，closure S 与 S 的差为零测；已独立读取 pinned mathlib 的 `Convex.addHaar_frontier` 及真实零延拓身份，确认这与原闭单元局部能量一致。这一解释不声称本批新增了另一条边界消去 Lean 声明，更不声称零延拓是任意 H² 状态的全空间弱 H² 延拓。

第9项先内部调用 `exists_closure_continuous_representative` 选择 f，然后才引入全部 T、内球中心、r、D、κ及其几何条件。它对该同一 f 同时调用原弱节点值界和第8项；两项使用完全相同的 I_Tf，值平方界为 16D⁴C(d,2)²d²乘同 K 原 Hessian 能量。中间声明所需的连续代表、平滑序列和全部强极限都在最终入口内部供应，未变成额外前提。

固定 d、κ 后显式常数先于 S、单元、尺度、状态及网格选择，不含 S 的体积或直径、核、逼近序列、节点导数映射范数或单元数量。S=∅ 时代表存在性由依赖的空域分支保证，无法容纳非空单纯形，后续全称命题为空范围；d=0、合法 D=0 无新增除法或排除条件。原 d=2、3、凸多面体及形状正则网格完全被此范围覆盖。

## 原文对应与未完成边界

本批确实完成原全部弱 H² 的局部节点值及完整梯度误差，取平方根分别是 D² 和 D 阶，且保留同单元原 Hessian 半范数；代表在所有单元之前统一选择，可用于同一网格的共享节点。闭包连续代表已由 C134 供应，不能再误称当前只对光滑状态或仅内部节点成立。

原 Step 2 还需 H¹₀ 状态的该代表在边界逐点取零、全网格拼接后属于真实 conforming 空间，以及原允许权、ℓK≈hK、求和与投影的组合。仅有边界点值合法与局部误差不等于这些义务已经完成。故 C136保持 AUXILIARY，P011及完整 `prop:p1` 不提升，原文保持14/26。

## 固定依赖、构建与公理

四模块 Carleman 导入闭包共180模块，新增4模块；其余176模块与 base 逐字节不变。进一步核对 C135 `WeakH2NodalValue` 的175模块闭包相对 base 不变，C134 `WeakH2ClosureContinuous` 的134模块闭包相对 `4e727b83c3fcb821432ba4089e6f9ea0c9e0a277` 不变，C129 `SmoothH2NodalGradient` 的101模块闭包相对 `9e1f7ef800794f6fb560151f827fc7df51f7b10a` 不变。依赖验收见 [T119](T119-local-acceptance.md)、[T118](T118-local-acceptance.md)、[T113](T113-local-acceptance.md)，本次另检查实际证明与调用。

原稿 SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean固定4.35.0；mathlib pin与本机实际HEAD均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机mathlib工作树干净。固定 root 导入全部4模块，新源码无 sorry、admit、额外 axiom 或 native_decide。

`tools/CheckAxioms.lean` 本次只增加9项完整类型及公理输出；递归审计器相对 base 不变，对全部 Carleman 常量及私有辅助声明 collectAxioms，仅允许 propext、Classical.choice、Quot.sound。逐名核对9项实际类型；全文件2317条非空公理记录、8条无公理记录（含重复，共2321个不同名字）均无不允许的公理。真实全环境递归审计为 **6688项 PASS**，和显式输出是不同计数。

独立读取固定 `/tmp/carleman-weak-nodal-gradient-target.log` 的 **3357 jobs** 成功，以及 `-full.log` 的 **3869 jobs** 成功和上述审计。固定 `-local-axioms.txt` 为 **2,027,715 bytes**，SHA256 **`c66d73205c28466b4c7943ff923ec4a234bbf5388e87c608f49f528fc6839107`**，未以变化中的 `.ci` 替代。

## 实际同 SHA CI 和原始产物

本 Agent 自行查询 [main CI 39204693650 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39204693650/attempts/1)：实际 main/push，head SHA精确匹配本报告 checked_sha，最终 completed/success，更新时间 `2026-10-19T05:31:08Z`。三项job均自行查询为 completed/success：state-check **117904875137**、lean **117904875367**、dashboard / snapshot **117905677260**；最后一项完成于 `2026-10-19T05:31:07Z`。

同run原始artifact为 `lean-ci-result` **12164444228**（归档492 bytes）、`lean-declaration-evidence` **12164643542**（归档185,919 bytes），元数据head_sha均匹配且未过期。本 Agent 自行执行两次 `gh run download 39204693650`，均exit 0，分别下载至 `/tmp/carleman-weak-nodal-gradient-main-ci` 和 `/tmp/carleman-weak-nodal-gradient-main-axioms`。

实际 result.json 为537 bytes，SHA256 `c98f2423cb56466203eea5a4aacd828c488a589a38bd0139e8ea67e18c51e2c4`。内容PASS，`checked_sha=source_head_sha=a26158d00376e85866c536aa366239af41c83f97`，target Carleman，`finished_at=2026-10-19T05:29:58.341631+00:00`，ci_url匹配同run/attempt；Lean4.35.0提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

独立逐字节比较远端 `-main-axioms/axioms.txt` 和固定本机副本：**完全一致，2,027,715 bytes，SHA256 `c66d73205c28466b4c7943ff923ec4a234bbf5388e87c608f49f528fc6839107`**。实际末行为6688项全声明递归审计PASS。原始产物PASS与全部job最终成功分别验证。

## 验收决定

**C136：PASS，可升级为 REVIEWED，scope保持 AUXILIARY。** 9项声明的真实节点导数、全部原弱梯度、同单元 Hessian 能量、维数/形状常数和统一代表量词均通过独立核查，未发现需要修复的数学缺陷。同SHA三项CI和自行下载的原始证据均已核实。

H¹₀边界零值、全局 conforming 插值及允许权组合尚待；P011不提升，原文保持 **14/26**。本次仅新建此报告，未修改实现、台账、root或原稿，未commit/push。以上签发UTC固定；通知主Agent后冻结报告，不再改动内容或时间戳。
