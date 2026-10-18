# T059 / C075 独立本机验收

- checked_sha: `daf0c9e455f04bf5d7eff4e4ecde1729e01f6a92`
- base_commit: `9b4962ef9d03bb7bce6cc906a508857d57398c8c`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result: `PASS`
- axiom_check: `PASS`
- reviewed_at: `2026-10-18T21:06:26+00:00`
- scope: `AUXILIARY`。真实经典导数控制下的单纯形局部节点误差；不等同于原一般 H² 节点插值定理或实际允许权的超逼近结论。原文完成数保持 **12/26**。

## 固定范围与检查方法

按仓库 `AGENTS.md`、`governance/PROJECT_OPERATIONS.md` 及 `state/README.md`，直接读取固定提交三模块的全部证明、13 项展开类型及递归公理输出、实际调用的依赖，以及 `paper/main.tex` Section 6 Step 2–3 和 `governance/analysis/T059-classical-nodal-errors.md`。没有用规格说明或编译成功代替数学核对；父 Agent 的后续工作树内容不在此范围。

新增模块为 `Carleman/Spatial/SimplexNodalRemainder.lean`（4 项）、`SimplexTaylorInterpolation.lean`（6 项）、`SimplexInterpolationIntegral.lean`（3 项）。固定 `Carleman.lean` 导入全部三模块；固定 C075、交付 `/tmp/carleman-taylor-nodal-declarations.json` 与实际声明清单顺序完全一致。项目递归 import 闭包有 75 个模块，其中 72 个既有模块与基线逐字节一致。

Lean pin 是 `leanprover/lean4:v4.35.0`，mathlib pin 是 `56a005855ea17e0b0958f73ec801ae140b0a1679`；本机实际 mathlib HEAD 相同、工作树干净。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未被本阶段改写。

## 全部 13 项声明

下列为完整名称；逐项实际数学核查均 PASS，假设和范围按说明保留。

| 声明 | 实际类型及证明核对 |
| --- | --- |
| `Carleman.affineScalarDerivative_inball_bound` | 对真实仿射 p、`r>0`、`R≥0` 及真实开球内 `|p|≤R`，推出实际 CLM 导数范数 `≤4R/r`。只用仿射线性部分的精确差商和合法正半径除法。 |
| `Carleman.simplexNodalInterpolant_sub_affine` | 全空间上精确 `I(f-p)=If-p`。节点插值是已有真实重心仿射多项式，证明使用完整仿射再现及有限和线性性，未把该等式新增为假设。 |
| `Carleman.simplexNodal_error_of_affine_approximation` | 闭单元上 `|f-p|≤R` 给每个单元点的 `|f-If|≤2R`。只要求实际点值函数；节点凸组合的绝对值界和两项三角不等式方向正确。 |
| `Carleman.simplexNodal_derivative_error_of_affine_approximation` | 实际内球、`r>0`、`R≥0`、闭单元余项界以及给定点 `‖fderiv f-Dp‖≤G`，推出 `‖fderiv f-DIf‖≤G+4R/r`。I−p 的导数通过两个实际 HasFDerivAt 的唯一性识别。此辅助项不另断言 f 在该点可微；最终 Taylor/积分项会明确提供这一条件。 |
| `Carleman.affineFirstOrder` | 由真实 `fderiv ℝ f a` 构造仿射映射 `f(a)-Df(a)a+Df(a)x`，不是任意拟合多项式或自定义导数。 |
| `Carleman.affineFirstOrder_apply` | 精确作用公式 `p_a(x)=f(a)+Df(a)(x-a)`，平移和符号无错位。 |
| `Carleman.affineFirstOrder_derivative` | 实际仿射导数恰为 `fderiv ℝ f a`。由常映射加真实 CLM 的 HasFDerivAt，再用唯一性证明；这并不单独断言原 f 可微。 |
| `Carleman.affineFirstOrder_remainder` | 凸 K 上处处 `DifferentiableAt f`、实际 Df 为 L-Lipschitz、锚点 a∈K、`h≥0` 且所有点距 a≤h，推出值余项 `≤Lh²` 与导数余项 `≤Lh`。真实凸集均值定理应用于同一固定线性映射 Df(a)。 |
| `Carleman.simplexNodal_error_of_lipschitz_derivative` | 选实际顶点 0 作锚点，全部点对距离≤h 的公开条件供应锚点距离界，得到真实节点误差 `≤2Lh²`。没有参考单元替换或隐藏形状常数。 |
| `Carleman.simplexNodal_gradient_error_of_lipschitz_derivative` | 再给真实内球及 `h≤κr`，由 `Lh+4Lh²/r` 得 `≤(1+4κ)Lh`。使用 `r>0` 和 `4Lh≥0`，不除以 h；h=0 仍允许。 |
| `Carleman.simplexNodal_error_sq_integral` | 真实闭单元 Lebesgue 平方积分 `∫(f-If)²≤(2Lh²)² vol(K)`。可微性给连续性，紧性给可积性；平方前确认非负上界，实际常数积分给体积因子。 |
| `Carleman.simplexNodal_gradient_error_sq_integral` | 对实际完整 Euclidean 一阶 fiber 的平方范数积分，给 `≤(‖derivativeOneFiber‖(1+4κ)Lh)² vol(K)`。连续性、可积性、CLM 算子范数及平方符号均内部证明；κ 的非负性由公开几何条件推出。 |
| `Carleman.derivative_lipschitzOn_of_second_derivative_bound` | 凸 K 上实际函数 `fderiv f` 处处可微，其真实导数算子范数≤L，则 Df 为 L-Lipschitz。直接使用凸集均值定理；二阶点态经典可微/有界条件显式保留，没有从弱 H² 自动推出。 |

## 内球、仿射再现和 Taylor 链条

`affineScalarDerivative` 展开为真实 ContinuousAffineMap 的 `contLinear`，已有 `affineScalar_hasFDerivAt` 在任意点证明这是实际 Fréchet 导数。内球界对每个范数为 1 的方向 x 取 `a+(r/2)x`，该点因 `r>0` 严格位于开球内。真实仿射差为 `(r/2)Dp(x)`，两端绝对值各至多 R，故差至多 2R，得到 `|Dp(x)|≤4R/r`。随后使用固定 mathlib 的 `ContinuousLinearMap.opNorm_le_of_unit_norm`；已直接检查该引理没有非平凡维数前提，在零空间也有效，而不是先选择一个不存在的单位向量。

节点插值的实际定义是 `Σ_i c_i λ_i`，其中 λ_i 是真实单纯形仿射基的重心坐标；单元内 λ_i 非负且和为 1，全空间再现每个仿射 p。因此 `I(f-p)` 的单元绝对值至多 R，而 `f-If=(f-p)-(If-p)` 给 2R。没有对一般 L² 类取顶点值。`simplexNodal_error_of_affine_approximation` 未额外写 R≥0 是合理的：单元非空且余项绝对值≤R 已强制该非负性；其证明本身也不需要非法除法或平方。

梯度辅助项以 `I-p` 这个真实仿射映射应用内球界，识别其导数为 `DI-Dp`，再用 CLM 范数三角不等式。该辅助项允许给定点 x 不在单元，只因其公开前提直接给该点的 `‖fderiv f(x)-Dp‖≤G`；它没有无条件把单元信息延伸为原 f 的外部导数界，也未声称原 f 在 x 必然可微。调用它的最终误差定理明确要求 x 在单元，且 f 在闭单元每一点真实可微。

`affineFirstOrder` 的前两个身份对任意 f 都可定义，这是 Lean 中 `fderiv` 的总函数用法；真正余项定理另有 `hf : ∀x∈K, DifferentiableAt ℝ f x`，从而调用时全部导数都是实际导数，不会用不可微处默认值逃避目标。Df 的真实 Lipschitz 界给 `‖Df(y)-Df(a)‖≤L dist(y,a)≤Lh`。固定 mathlib 的 `Convex.norm_image_sub_le_of_norm_fderiv_le'` 将同一固定 Df(a) 从 f 中减去，得 `|f(x)-f(a)-Df(a)(x-a)|≤Lh‖x-a‖≤Lh²`。这里是有效但不最优的常数 1，没有冒称 1/2。

取实际顶点 0 时 `Fin(d+1)` 永不为空，包含于凸包的证明直接成立。直径条件是单元内所有点对的实际距离≤h；可以取 h 为紧单元的 `Metric.diam`，所需距离界由已有真实紧性/直径定理供应。没有把 h 定义成名义网格参数并略去几何关系。梯度从 `Lh+4Lh²/r` 吸收为 `(1+4κ)Lh` 时，只将 `h≤κr` 乘以非负 `4Lh` 并除以正 r，没有要求 h>0。

## 真实积分、梯度及边界情形

积分测度确为 `volume.restrict (simplicialCell T.points)`，不是系数平方和、离散求积或人为定义误差。真实单元是有限顶点凸包，紧且可测，已有有限受限体积实例。因此 f−If 的平方由闭单元上的真实连续性可积；梯度误差场由 Df 的 Lipschitz 连续性、常仿射导数及真实有界线性 `derivativeOneFiber` 连续性可积。两次 `integral_mono_ae` 的双方可积性均已供应，且仅在真实单元 a.e. 取点态界；常数积分准确化为 `常数² × volume.real(K)`，没有丢体积或误用无穷体积。

`SpatialCoordinates d = EuclideanSpace ℝ (Fin d)`，`DerivativeFiber d 1 = EuclideanSpace ℝ (Sym (Fin d) 1)`。展开 `derivativeOneFiber` 后，其 α 分量就是 CLM 在 `basisFun (Sym.oneEquiv.symm α)` 上的值：所有一阶正交坐标各出现一次，使用的是 Euclidean 范数。由于本次最终定理的 f 在单元上可微、If 是真实仿射映射，`Df-DIf` 确为 f−If 的经典导数；该 fiber 是真实经典梯度。此处保留 `‖derivativeOneFiber‖` 这个只依赖 d 的固定有界线性映射范数，没有把它冒充任意代理能量或未经证明地设为 1。该局部积分结论本身没有声称已经装配全域弱 Sobolev jet、H¹₀ 误差或连续节点全局插值。

L 是 NNReal，故 L≥0 自动而非额外未写约束；允许 L=0。`h≥0` 允许 h=0；梯度平方上界需要 `κ≥0`，代码由 `0≤h≤κr` 与 `r>0` 实际推出。R=0、h=0 的证明不包含除以 R、h 或 L 的步骤。d=0 仍保留实际非退化 0-单纯形：方向空间及一阶 fiber 为零，范数结论正确，且没有假设空间单点体积为零；真实体积因子仍保留。

最后一个二阶引理只要求 Df 作为 CLM 值函数在凸 K 上真实可微并有真实 `fderiv (fderiv f)` 点态范数界。它本身给的是该 CLM 值函数的 Lipschitz 性，不会替 f 补出一阶可微性；与此前插值引理组合时，仍须另外满足此前的 hf。已直接检查其调用的 mathlib `Convex.lipschitzOnWith_of_nnnorm_fderiv_le` 确实作用于整个凸 K，包括单元边界，没有偷偷将闭单元换成开集或仅检查顶点。

## 原论文定位、统一性与未完成事项

原 Section 6 Step 2 的 `eq:p1-interpolation` / `eq:p1-interpolation-energy`（`paper/main.tex:1532` 起）是对一般 H² 状态、以真实 L² Hessian 范数控制的加权节点插值界；Step 3 对实际 `σ²z_h` 使用单元超逼近并最终得到 `9.26-eq10`、`9.26-eq11`。本阶段给这些工作的经典局部辅助估计，不能直接代替任一完整原结论：

- f 在闭单元上逐点经典可微、Df 为 L-Lipschitz 是明确且实质的强条件。可用二阶引理的点态经典 Hessian 上界供应 L，但一般 H² 弱 Hessian 的 L² 控制不等于这种上界。
- 当前状态是实际点值函数，尚未从一般 H² 类构造连续代表/合法节点取值，也未获得以局部 L² Hessian 范数为右端的原估计。
- 尚未针对原实际允许权的 `σ²z_h` 供应所有一/二阶经典导数及其统一 q 尺度界，未消去局部值/梯度上界并取得最终加权范数超逼近，未进行全网格装配。
- 常数 4、2 和 `1+4κ` 是显式几何常数；fiber 的附加范数只依赖 d。本阶段没有隐藏网格大小/单元位置依赖，但输入 L 可以依赖具体 f，不能将其误报为已得到对时间权、τ、qmax、全状态的原统一估计。

因此 C075 的 `extra_hypotheses=[]` 只能针对本辅助命题自身、连同完整声明中的经典假设理解，不表示相对原一般 H² 插值命题没有额外前提。范围必须保持 AUXILIARY，不能提升 P011 或其他完整原文覆盖，仍为 12/26。

## 实际依赖与构建证据

已直接检查实际使用的 `SimplexNodalInterpolation` 的重心定义、非负和为一、节点身份及仿射再现；`SimplexNodalLp` 的真实紧单元有限测度；`AffineWeakGradient` 的真实仿射 CLM 导数及 HasFDerivAt；`FirstOrderSobolevJet`、`SobolevJet` 中真实 Euclidean fiber 的定义；`SimplicialCells` 的凸、紧、可测及 `SimplicialDiameter` 的真实直径界。已有依赖验收可见 [T045 / C061](T045-local-acceptance.md)、[T048 / C064](T048-local-acceptance.md)，本次亦检查这些结果被实际正确调用，而非仅引用验收结论。相关既有依赖相对本基线未变。

对 mathlib，直接检查固定 pin 下的单位向量算子范数判据、凸集有固定线性项的均值定理及 CLM 值函数的有界导数 Lipschitz 定理；它们的域、可微性和符号要求与本次调用匹配。此阶段没有使用或假设逆向 H² 正则性、Sobolev 点值或原目标误差界。

`/tmp/carleman-taylor-nodal-full.log` 实际含 `Build completed successfully (3632 jobs)` 及全部 4913 个 Carleman 声明的递归公理审计 PASS。固定本机 `/tmp/carleman-taylor-nodal-local-axioms.txt` 实测 **1,403,358 bytes**，SHA256 **`43ca49e2f9227781288b29a59374cdcd7964feb8d601b24a4d86d88ef94fd091`**。已逐名读取本次 13 项完整展开类型并解析每项递归公理列表，均精确为 `propext`、`Classical.choice`、`Quot.sound`。固定 `CheckAxioms.lean` 逐项 #check/#print 后还递归检查整个项目 namespace，未只检查一个表面入口；没有 sorryAx 或额外数学公理。

已独立通过 GitHub API 读取实际 main/push [CI run 39166049483 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39166049483/attempts/1)：head SHA 是本次固定 SHA，运行整体 completed/success。三个 job 均绑定同一 SHA 且 completed/success：`state-check`（117789094427，完成于 `2026-10-18T21:02:50Z`）、`lean`（117789094315，完成于 `2026-10-18T21:05:16Z`）、`dashboard / snapshot`（117789703091，完成于 `2026-10-18T21:05:27Z`）。实际 artifact API 还确认 `lean-ci-result`（12150433683）与 `lean-declaration-evidence`（12150966232）来自此 run、同一 SHA，均未过期。

已直接读取 `/tmp/carleman-taylor-nodal-main-ci/result.json`：`status=PASS`、`checked_sha=source_head_sha=daf0c9e455f04bf5d7eff4e4ecde1729e01f6a92`、targets 为 `Carleman`、CI URL 精确匹配上述 run/attempt、`finished_at=2026-10-18T21:04:21.777212+00:00`。Lean 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 mathlib pin 正确。该结果生成时间与后续 job 上传收尾完成时间分开记录。

已独立逐字节比较 `/tmp/carleman-taylor-nodal-main-axioms/axioms.txt` 与固定本机副本：完全相同，均为 **1,403,358 bytes**，SHA256 均为 **`43ca49e2f9227781288b29a59374cdcd7964feb8d601b24a4d86d88ef94fd091`**。又从远端原始文本逐名解析本次 13 项公理列表，均精确为上述三项标准基础公理；末行实际确认全部 **4913** 声明审计 PASS。

## 验收决定

**T059 / C075：PASS，13 声明可升 `REVIEWED / AUXILIARY`。** 固定版本的实际类型、数学证明、依赖使用、退化边界情形、公理及同 SHA 三项远端检查未发现需修复缺陷。经典可微性和 Df Lipschitz/二阶点态界仍是显式前提；原一般 H² 插值、实际允许权超逼近及全网格原结论仍待，原文完成数保持 12/26。

本次仅写此报告，未修改证明源码、台账、root 导入或原稿，未 commit/push。
