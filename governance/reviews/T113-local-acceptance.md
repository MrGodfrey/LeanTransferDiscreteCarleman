# T113 / C129 独立本机验收

- `checked_sha`: `9e1f7ef800794f6fb560151f827fc7df51f7b10a`
- `base_commit`: `c8377e5f743689641ab84d5049b4d0fb291d29f5`
- `reviewed_at`: `2026-10-19T04:36:05+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：d≤3、全空间 C² 函数在真实单纯形上的局部节点梯度误差，右端为实际二阶 Fréchet 多线性导数算子范数的 L² 积分。全弱 H²、弱 jet Hessian 分量识别、边界资格及全局允许权逼近仍待；不提升 P011 或完整 `prop:p1`，原文保持 **14/26**。

本 Agent 独立读取固定 git 对象的完整模块、五项展开类型与关键依赖，对照原 `paper/main.tex` Section 6 的 P1 设置（1462–1505）及 Step 2 的 `eq:p1-interpolation`、`eq:p1-interpolation-energy`（1527–1548），并读取固定 T113 分析和 MATH_SPEC。执行者说明和 CI 未替代数学审查。未来 TensorCoordinateNorm、LocalHessianConvolution 等工作树增量及变化中的 `.ci` 文件均未纳入。

## 全部五项声明

以下名称省略公共前缀 `Carleman.`；固定位置均在 `Carleman/Spatial/SmoothH2NodalGradient.lean`。名单与交付 JSON 和固定 C129 台账逐项一致。

| # | 声明 | 行 | 独立结论 |
|---|---|---|---|
| 1 | `derivativeOneFiber_norm_sq` | 14 | PASS；真实 Euclidean 一阶纤维范数平方等于全部 d 个标准坐标方向值的平方和。 |
| 2 | `smooth_directional_gradient_bound` | 21 | PASS；实际 D(Df·e) 的算子范数由实际 iteratedFDeriv 二阶算子范数乘 ‖e‖ 控制。 |
| 3 | `averagedTaylorPolynomial_derivative` | 34 | PASS；同一个实际平均 Taylor 仿射多项式的导数精确为体积归一化的平均 Df。 |
| 4 | `averagedTaylorPolynomial_gradient_integral` | 40 | PASS；逐坐标真实均值 Poincare 给出 d·2^d/2 的完整梯度平方积分界。 |
| 5 | `simplexNodal_smooth_h2_gradient_integral` | 82 | PASS；真实节点、实际内球和形状界给出所述 2^d d+128κ²‖derivativeOneFiber‖² 系数，正体积精确消去。 |

## 真实梯度纤维与二阶导数

已读取 `FirstOrderSobolevJet.derivativeOneFiber` 的构造：通过所有标准基方向求值以及 PiLp 的真实 Euclidean 范数形成连续线性映射。第1项用 `Sym.oneEquiv` 对全部一次多重指标和 `Fin d` 作双射重排，配合 `EuclideanSpace.real_norm_sq_eq` 得到精确平方和。没有漏坐标、单方向替代或将 CLM 算子范数误作完整梯度纤维范数。

第2项由 `ContDiff ℝ 2 f` 得 Df 为 C¹，实际调用 `fderiv_clm_apply` 计算 D(Df·e)，常向量 e 的导数为零。随后对真实二阶导数的翻转 CLM 使用 `le_opNorm`、`opNorm_flip`，并由 `norm_iteratedFDeriv_one` 和 `norm_iteratedFDeriv_fderiv` 的等距柯里化身份识别

\[
\|D(Df)(x)\|=\|\operatorname{iteratedFDeriv}_2 f(x)\|.
\]

故对任意 x、e 都有 ‖D(Df·e)(x)‖≤‖D²f(x)‖‖e‖。这是实际 Fréchet 导数的范数估计，未假设候选 Hessian 矩阵为导数，也未把右端冒充弱 jet 的二阶分量范数。

## 同一个平均 Taylor 多项式及完整积分估计

已展开 `averagedTaylorPolynomial`：其线性部分为 V⁻¹∫K Df，常数部分为 V⁻¹∫K(f(y)−Df(y)y)，其中 V=volume.real K。第3项直接调用真实仿射多项式的导数身份；该代数声明对任意 K、f 成立，不自行声称 V>0 或任意函数均可积。在第4、5项的实际应用中，紧性、C² 正则性和正体积均已提供。

第4项对每个标准方向 eᵢ 令 gᵢ(x)=Df(x)eᵢ。Df 的连续性和 K 紧性给出 Bochner 可积性，`ContinuousLinearMap.integral_apply` 合法交换积分与方向求值，因此左端点态恰为

\[
\sum_{i=1}^d\left(g_i(x)-V^{-1}\int_Kg_i\right)^2.
\]

有限和与积分的交换逐项供应连续平方函数的可积性。已独立检查所调用的 `convex_smooth_mean_poincare`：真实线段 FTC、半区间换元及精确均值双积分身份给出 (2^d/2)D² 的常数，并以 V>0 消去体积。对各 gᵢ 使用该结果，再由第2项和 ‖eᵢ‖=1 控制其梯度，得到

\[
\int_K\|\mathrm{fiber}(Df-Dp)\|^2
\le d\frac{2^d}{2}D^2\int_K\|D^2f\|^2.
\]

此声明对一般 d 成立；没有把 d≤3 错用为均值 Poincare 的必要条件。每个积分比较都具有实际可积性证明，没有依赖 Lean 对不可积积分的默认值。

## 真实内球、所有顶点与体积消去

第5项中的 T 是 `Affine.Simplex ℝ (SpatialCoordinates d) d`，即 d 维真实非退化单纯形。K 是其闭凸包，正有限体积通过非空内部和紧性内部证明。原 `ball(a,r)⊆K`、r>0、D≥0、D≤κr 和所有点对 dist≤D 都在完整类型中明确保留；它们是局部形状和直径条件，不是一个抽象逆估计假设。

已读取前阶段 `SmoothAveragedTaylor`、`SmoothH2NodalError` 的真实 Taylor 积分和低维奇异核推导。d≤3 用于其可积核界，给同一 p 在全部闭 K（包括全部真实顶点）上的误差

\[
|f-p|\le R:=2D^2\sqrt{VH}/V,\qquad H:=\int_K\|D^2f\|^2.
\]

节点插值 I 使用 f(T.points i) 的真实点值。通过精确仿射再现，I−p 等于 f−p 的节点插值；闭单元非负重心坐标及和为1给 |I−p|≤R，继而在实际内球成立。这里 f 为全空间 C²，节点点值合法；没有对 L² 等价类直接取点值。

已检查 `affineScalarDerivative_inball_bound`：在 a 和 a+(r/2)e 比较仿射值，以 r>0 得 ‖D(I−p)‖≤4R/r。其导数确为实际 Fréchet 导数（`affineScalar_hasFDerivAt`），差的导数由唯一性识别。此处无任意矩阵、未验证的参考尺度或有限维自动连续性给出的网格常数。

设 F=‖derivativeOneFiber‖、B=F·4R/r。F 是固定维数空间之间固定映射的算子范数，仅依赖 d。范数中的差反向由 `norm_sub_rev` 合法处理；实际误差分解为 Df−DI=(Df−Dp)+(Dp−DI)。平方三角界及实际积分给出左端≤2∫K‖fiber(Df−Dp)‖²+2VB²。

证明以 V>0、r>0 和 H≥0 展开平方根，逐项建立精确等式

\[
VB^2=64F^2\frac{D^2}{r^2}D^2H
\le64F^2\kappa^2D^2H.
\]

因而体积完全消去，不需体积统一下界。结合前述梯度界及系数2，恰得

\[
\int_K\|\mathrm{fiber}(Df-DI)\|^2
\le(2^d d+128\kappa^2F^2)D^2\int_K\|D^2f\|^2.
\]

不存在随单元数、网格大小、体积或状态变化的隐藏常数。没有除以 Hessian 积分、D 或 κ；H=0 和合法的零维情形不会产生非法除法，原 d=2、3 均覆盖。

## 原文对应和范围边界

原 Step 2 对全部 v∈D(A)⊆H² 使用节点插值，随后与权比较、ℓK≈hK 和全网格求和结合，得到全域允许权下的值/梯度界。本批只证明其光滑局部梯度组成部分，和 C128 的光滑局部值界配套。取 D 为真实单元直径、κ 为固定形状参数后，平方根给原 hK 阶梯度尺度；但本批没有构造全弱 H² 连续代表、证明其节点值资格或完成平滑逼近极限。

右端仍是实际二阶多线性算子范数平方积分，和项目弱 jet Hessian 的全部二阶分量 L² 范数之间的衔接未在此声明中完成。全局允许权、零边界节点和完整 conforming 插值同样不是本批结论。故不能据此签发原 `eq:p1-interpolation-energy` 的完整全域版本、P011 或 PAPER。

## 固定依赖、构建与公理

导入闭包共101个 Carleman 模块，新增恰为本批单模块；其余100模块与 base 逐字节不变。再对照既有 `declaration_version`：C128 `SmoothH2NodalError` 的97模块闭包相对 base 不变；C088 `ConvexSmoothPoincare` 的58模块闭包相对 `36c57dbc4edf3d9671f7b00f8c0675230f6b4380` 不变；C075 `SimplexNodalRemainder` 的73模块闭包相对 `daf0c9e455f04bf5d7eff4e4ecde1729e01f6a92` 不变。不存在混用改变后的旧依赖版本。

原稿及已读治理协议自 T110 不变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。固定 Lean4.35.0，mathlib pin及本机实际HEAD均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机mathlib工作树干净。root显式导入此模块，`tools/CheckAxioms.lean` 有五项完整类型、公理输出及全声明递归审计。

实际读取固定 `/tmp/carleman-p1-h2-gradient-target.log`，内容为3273 jobs成功；`-full.log` 为3837 jobs成功及6582声明递归公理审计PASS。本机固定 `-local-axioms.txt` 为 **1,959,277 bytes**，SHA256 **`8973a261982beccfa39184d4fcf3d420b594ab5c9e1a1a184fcbcb913e8aff35`**。全部2240条显式公理记录中2232非空、8无公理，均无 `propext`、`Classical.choice`、`Quot.sound` 之外的公理，无sorryAx。五项完整展开类型逐一符合上文范围。

## 实际同 SHA CI 和原始远端产物

本 Agent 自行查询 [main CI 39199869405 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39199869405/attempts/1)，实际run为main/push、completed/success，head SHA精确为本报告固定提交。三个job均completed/success：lean **117890409559**、state-check **117890409942**、dashboard / snapshot **117891319870**。

同run两个原始artifact为 `lean-ci-result` **12163466722**、`lean-declaration-evidence` **12163172536**，两者元数据中的head_sha精确匹配。本 Agent 自行通过 `gh run download 39199869405` 下载至 `/tmp/carleman-p1-h2-gradient-main-ci` 和 `-main-axioms`。

实际 `-main-ci/result.json` 为PASS，`checked_sha=source_head_sha=9e1f7ef800794f6fb560151f827fc7df51f7b10a`，targets为Carleman，`finished_at=2026-10-19T04:33:34.759196+00:00`，ci_url与上述run/attempt一致；Lean提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

独立逐字节比较 `-main-axioms/axioms.txt` 与固定本机副本，完全一致：**1,959,277 bytes**，SHA256 **`8973a261982beccfa39184d4fcf3d420b594ab5c9e1a1a184fcbcb913e8aff35`**。因此远端五项完整类型及公理记录均与已核对文本一致，实际末行为 **6582项全声明递归审计PASS**。未使用未来源码或其他SHA的产物。

## 验收决定

**C129：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 五项声明未发现需要修复的数学缺陷；真实完整梯度、同一平均 Taylor 多项式、实际 Fréchet Hessian、真实节点和内球、积分可积性、128系数及正体积消去均已独立核对。同SHA正式三项CI与自行下载的原始公理证据已核实。

全弱 H²、弱 jet Hessian 分量识别、边界节点资格及全局允许权插值仍待，P011和完整 `prop:p1` 不提升，原文保持 **14/26**。本次仅新建本报告，未修改实现、台账、原稿或root导入，未commit/push。以上签发UTC固定；通知主Agent后不再变更报告或时间戳。
