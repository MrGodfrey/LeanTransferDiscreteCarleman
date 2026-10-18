# T072 / C088 独立本机验收

- `checked_sha`: `36c57dbc4edf3d9671f7b00f8c0675230f6b4380`
- `base_commit`: `d65579460032f15bcba3c77709ccfd3f1642b8fc`
- `semantic_checked_at`: `2026-10-18T22:39:19+00:00`
- `reviewed_at`: `2026-10-18T22:40:49+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。正体积紧凸单元上，全空间真实 C¹ 标量函数的均值 Poincaré 基础；未完成一般弱 H¹/H²、边界仿射逼近、P1/FD 的完整原文引理或 N3，完整原文覆盖保持 12/26。

本报告直接读取固定提交四模块的全部 11 项完整类型与证明，并核对实际相关依赖、原 `paper/main.tex` 及 `governance/analysis/T072-convex-poincare.md`。未以执行者报告、旧验收或 CI 替代语义检查；后续工作树增量不属于此次验收范围。

## 全部 11 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/Spatial/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `integral_sq_sub_const` | `MeanSquareDifference.lean:13` | PASS；有限测度下真实 L² 函数减任意常数的平方积分展开，每次拆分前供应可积性。 |
| 2 | `integral_pairwise_sq` | `MeanSquareDifference.lean:24` | PASS；真实迭代双积分等于 2m∫f²−2(∫f)²，内层和外层的多项式积分均合法。 |
| 3 | `mean_square_pairwise_identity` | `MeanSquareDifference.lean:43` | PASS；m>0 时，2m∫(f−mean f)² 精确等于两点差平方双积分，均值使用真实质量 m。 |
| 4 | `integral_comp_scalar_affine` | `ConvexSegmentIntegral.lean:12` | PASS；真实 x↦rx+b 换元的 Jacobian 是 r^d，积分前因子为其倒数，r>0。 |
| 5 | `integral_convex_segment_le` | `ConvexSegmentIntegral.lean:28` | PASS；凸性保证仿射像包含于 K，r∈[1/2,1] 给逆 Jacobian≤2^d，右侧是真实 K 上积分。 |
| 6 | `smooth_segment_ftc` | `SmoothSegmentSquare.lean:14` | PASS；真实 fderiv 的链式法则和线段 FTC，对任意实 t 成立。 |
| 7 | `smooth_segment_difference_sq` | `SmoothSegmentSquare.lean:28` | PASS；t≥0 时真实 L² Cauchy–Schwarz 给 t‖z‖²∫‖Df(x+sz)‖²，未用导数上确界替代。 |
| 8 | `convex_half_segment_integral_le` | `ConvexSmoothPoincare.lean:14` | PASS；紧乘积上可积后交换积分，真实半区间长度 1/2 给 2^d/2。 |
| 9 | `convex_smooth_midpoint_error` | `ConvexSmoothPoincare.lean:38` | PASS；结合 FTC 的 t=1/2 与半线段积分界，得到 (2^d/4)D²∫K‖Df‖²。 |
| 10 | `convex_smooth_pairwise_bound` | `ConvexSmoothPoincare.lean:75` | PASS；同一中点的双端点平方三角、乘积换序和实际积分，给 2^d·m·D²∫K‖Df‖²。 |
| 11 | `convex_smooth_mean_poincare` | `ConvexSmoothPoincare.lean:124` | PASS；由精确均值恒等式和 m>0 消去 2m，最终常数准确为 2^d/2。 |

## 原文定位及精确范围

原 Section 6 的 P1 Step 2（`paper/main.tex:1523` 起）涉及一般 H² 状态的局部仿射插值和加权逼近；Appendix B 的 `lem:fd-boundary-affine`（`paper/main.tex:2803`）要求一般 H²(B_K) 状态、指定物理面的零迹、尊重这些边界面的仿射多项式，以及 L²/H¹ 误差由 Hessian 的 L² 范数控制。其证明在 `paper/main.tex:2816` 调用 Bramble–Hilbert；后续 `lem:fd-weighted-approximation`（`paper/main.tex:2841`）还需局部矩重构和块的有界重叠。

本批完成其中可用于后续构造的光滑均值 Poincaré 基础，并非上述任一完整原文引理。最终类型明确保留 `ContDiff ℝ 1 f`，即 f 在整个 Euclidean 空间上 C¹；不能把它解释为原一般弱 H¹/H² 函数的结论。仍待局部光滑逼近与极限、二阶仿射逼近、物理面迹校正及相应网格组合，未供应完整 B1/B2、P1/FD 或 N3。

实际最终式为：令 m=volume.real K，

`∫K (f−(∫K f)/m)² ≤ (2^d/2) D² ∫K ‖fderiv ℝ f‖²`。

K 是任意紧凸集，m>0；D≥0 是所有实际两点距离的上界。右端导数为实际 Fréchet 连续线性映射的算子范数，无自由提供的梯度、导数界、Hessian 上确界或抽象能量。此处也未额外声称已完成该强导数与一般弱 Sobolev 梯度的识别。

常数显式为 2^d/2，只依赖 d，先于 K、f、D；没有形状正则、内球比、网格、参数或状态依赖。没有新增零边界要求。d 的类型为任意自然数，含 d=0；所有因子及证明在零维仍有意义。最终排除零体积集是归一化均值所需的显式假设，前序双差和半线段辅助式不要求正体积。t=0、D=0 和常函数均未被不必要的除法排除。

## 真实均值与双积分

`MeanSquareDifference` 在任意有限测度 ν 上工作。`MemLp f 2 ν` 内部给出 f∈L¹ 及 f² 可积；常函数、线性项和平方项的所有和差均先构造 `Integrable` 证明，再用 `integral_add/sub`。没有利用不可积 Bochner 积分的默认值产生伪恒等式。

两点公式先对每个 x 展开内层积分，再把内层识别为 x 的可积二次多项式，得到 `2m∫f²−2(∫f)²`；此处不需要无依据地调用 Fubini。均值采用 `(∫f)/m`，不是把未归一化测度错当概率测度。m>0 保证最后代数化简与消去均值分母合法。

最终紧集上的真实 L² 资格由 f 的连续性与 f² 在紧集的可积性内部供应；m 有限来自紧集的有限 Lebesgue 体积，m>0 来自最终假设。没有把这些资格转交为额外目标估计。

## 仿射 Jacobian 与半线段

直接核对既有 `AffineChangeVolume`：实际仿射同胚 x↦Ax+b 将 Lebesgue 测度推前为 `|det A|⁻¹ • volume`，限制测度通过同一映射变为像集上的限制测度；积分公式据此成立。新标量线性等价取 A=r·id，r>0，其行列式绝对值为 r^d，故新积分前因子确为 r^(-d)。方向正确，缩小像集时出现逆 Jacobian 放大。

`integral_convex_segment_le` 使用实际凸组合 rx+(1−r)y 的像集包含关系。非负性是 K 上 a.e. 非负，`IntegrableOn f K` 保证像集积分单调性合法；r∈[1/2,1] 给 r⁻¹≤2，进而 r^(-d)≤2^d。没有误用 r^d 或忽略限制像集。

在半线段中 x+s(y−x)=(1−s)x+sy，s∈[0,1/2]，故应用前一引理的 r=1−s∈[1/2,1]。被积函数 g(x+s(y−x)) 在 K×[0,1/2] 上连续，因此在真实限制乘积测度上可积。只有拿到该证据后才交换 x/s 的积分，最后积分常数乘以真实区间长度 1/2，得到 `2^d/2·∫K g`。

## FTC、Cauchy–Schwarz、平方三角及 Fubini

`smooth_segment_ftc` 对曲线 s↦x+sz 使用真实导数 z，再与实际 fderiv 组合。f 的 C¹ 正则性保证沿线导数连续及任意有限区间上的可积性；FTC 对任意实 t 的有向积分成立。

平方界先在 Ioc(0,t) 上为 `Df(x+sz)z` 构造真实 MemLp 2，再把常函数 1 与它代入既有 `integral_mul_sq_le`。已直接核对该依赖确实把真实 L² 积分识别为 L² 内积并用 Hilbert Cauchy–Schwarz，而非要求待证积分界。常数 1 的平方积分为 t；CLM 的真实算子范数不等式给 `|Df·z|²≤‖Df‖²‖z‖²`。两边可积性来自导数的连续性。t≥0 只用于无向积分及乘法单调性，没有除以 t。

中点步骤 t=1/2，Ioc 与 Icc 的端点差通过实际 Lebesgue 零测端点身份消除。D 控制真实 ‖y−x‖，其平方替换乘以非负导数平方积分。参数积分对 x 的连续性调用的是连续函数在固定紧参数集上的积分连续性；该实际 mathlib 定理的局部支配条件由局部紧性和紧参数集证明，没有偷偷要求全空间统一支配函数。

因此，中点误差系数为 `(1/2) × (2^d/2) = 2^d/4`。双差步骤令 R(x,y)=(f(x)−f((x+y)/2))²，逐点证明 `(f(x)−f(y))²≤2R(x,y)+2R(y,x)`。两端使用的确是同一中点，交换 x/y 后两个 R 的乘积积分相等；两项各系数 2，总因子为 4。对 y 积分中点界产生且只产生一个 m，故双差界为 `2^d m D²∫K‖Df‖²`。

R、交换后的 R、双差平方及其和分别在 K×K 上连续可积，`integral_prod_symm`、`integral_prod_swap`、`integral_prod` 和积分单调性均有相应实际可积性。最终用 `2m·variance=pairwise` 并除以正数 2m，精确得到 `2^d/2`。未遗漏半区间长度、平方三角的系数或体积因子。

## 固定版本、构建和递归公理

四个新模块的 Carleman 导入闭包共 58 个模块，其中 54 个既有模块相对 base 逐字节不变；root 明确导入四模块。AGENTS、流程规则、原论文、Lean/mathlib pin 和 CI workflow 均未在本批改变。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-convex-poincare-full.log` 实际包含 `Build completed successfully (3680 jobs).`。固定 `/tmp/carleman-convex-poincare-local-axioms.txt` 的 11 项完整类型已逐项核对，每项恰有一条完整类型和一条递归公理打印，均仅有 `propext`、`Classical.choice`、`Quot.sound`。全部 1488 条显式公理打印（1484 个不同声明）也已扫描，无白名单外公理；末行确认所有 5156 个 Carleman 声明（含内部生成声明）递归审计通过。

`tools/CheckAxioms.lean` 本批仅增加 11 项完整类型与公理打印；遍历所有 Carleman 声明并递归 `collectAxioms` 的审计程序未变。四新模块无 sorry、admit 或新增公理。固定本机产物为 1,527,567 bytes，SHA256 `1d862fbc8afc95f20d14be10f6f5318e4aa4b6bb840cd3b2e03de7798e8bbdd2`。Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据与签发状态

已独立读取真实 [main/push run 39172937739](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39172937739/attempts/1)，attempt 1，head SHA 精确匹配 checked SHA，顶层 completed/success。三个 jobs 均 completed/success：state-check `117809607221`、lean `117809607442`、dashboard / snapshot `117810352553`；未在 lean 缓存收尾或其他 job 仍运行时签发。

同次 artifact 元数据已独立读取：`lean-ci-result` id `12152583890`、`lean-declaration-evidence` id `12153485782` 均绑定该 run、main 和同一 head SHA。实际读取 `/tmp/carleman-convex-poincare-main-ci/result.json`，status=PASS，checked_sha/source_head_sha 均为 `36c57dbc4edf3d9671f7b00f8c0675230f6b4380`，ci_url 精确对应该 run/attempt，finished_at=`2026-10-18T22:38:25.492041+00:00`，target 为 `Carleman`。Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib pin 均匹配。

实际读取 `/tmp/carleman-convex-poincare-main-axioms/axioms.txt`，与固定本机产物逐字节完全相同：1,527,567 bytes，SHA256 `1d862fbc8afc95f20d14be10f6f5318e4aa4b6bb840cd3b2e03de7798e8bbdd2`。远端产物再次核对 11 项完整类型和递归公理，以及全部 1488 条公理打印，无白名单外项；末行确认所有 5156 项递归审计通过。

最终结论：**T072 / C088 PASS，可将 C088 升为 REVIEWED，保留 AUXILIARY。** 11 项及所声称的光滑均值 Poincaré 范围通过，未发现数学缺陷。不得据此提升一般弱 H¹/H²、原 Appendix B 完整引理或 P1/FD 覆盖；原文计数保持 12/26。本 Agent 仅写本报告，未修改实现、台账、root 或原稿，未 commit/push。
