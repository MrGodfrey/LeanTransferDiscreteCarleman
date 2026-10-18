# T074 / C090 独立本机验收

- `checked_sha`: `55dbf36858608cc7ff9300ef61430e18fa0bdadf`
- `base_commit`: `c99262c4a0d65a4d23f2efb57748bda490e971d7`
- `semantic_checked_at`: `2026-10-18T22:54:23+00:00`
- `reviewed_at`: `2026-10-18T22:56:52+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。有界开凸域全部真实弱 H² 状态的未校正仿射逼近。物理面零迹校正、完整 B1/B2/P1 和相关网格/权组合仍待，原文覆盖保持 12/26。

本报告直接读取固定提交五模块、全部 34 项完整类型和证明，以及相关实际依赖，对照原 `paper/main.tex`、`governance/MATH_SPEC.md` 和 `governance/analysis/T074-h2-affine.md`。未以执行者报告、旧验收或 CI 成功代替数学核查；后续工作树增量不属于本批。

## 全部 34 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/Spatial/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `scalarLp_norm_sq` | `BoundedAffineSobolev.lean:12` | PASS；真实 scalar L² 范数平方等于其 a.e. 代表的平方积分。 |
| 2 | `scalarConstantLp` | `BoundedAffineSobolev.lean:18` | PASS；有限测度上真实常函数的 L² 类。 |
| 3 | `scalarConstantLp_ae` | `BoundedAffineSobolev.lean:21` | PASS；该类的代表 a.e. 等于指定常数。 |
| 4 | `norm_sub_scalarConstantLp_sq` | `BoundedAffineSobolev.lean:24` | PASS；真实类的差范数平方等于实际 `(u−c)²` 积分。 |
| 5 | `boundedAffine_memLp` | `BoundedAffineSobolev.lean:36` | PASS；有界域上每个实际仿射函数属于 L²，由紧闭包连续平方积分得到。 |
| 6 | `boundedAffineLp` | `BoundedAffineSobolev.lean:42` | PASS；从上述可积性构造实际仿射 L² 类。 |
| 7 | `boundedAffineLp_ae` | `BoundedAffineSobolev.lean:45` | PASS；仿射类与原仿射函数 a.e. 相同。 |
| 8 | `boundedAffineLp_weak` | `BoundedAffineSobolev.lean:48` | PASS；全部真实测试下的弱导数等于该仿射函数实际常导数。 |
| 9 | `IsWeakSpatialDerivative.sub` | `BoundedAffineSobolev.lean:56` | PASS；原完整弱测试恒等式对 L² 类相减保持。 |
| 10 | `coordinateFirstFields` | `CoordinateFirstJet.lean:13` | PASS；零阶真实 scalar fiber 和完整一阶 Euclidean field 的构造。 |
| 11 | `coordinateFirstJet` | `CoordinateFirstJet.lean:19` | PASS；给定全部坐标的真实弱导数身份，构造完整弱 H¹ jet。 |
| 12 | `coordinateFirstJet_value` | `CoordinateFirstJet.lean:34` | PASS；组装后的 scalar value 精确等于原输入类。 |
| 13 | `coordinateFirstJet_gradient_norm_sq` | `CoordinateFirstJet.lean:39` | PASS；完整梯度 L² 范数平方精确等于各坐标 L² 范数平方和。 |
| 14 | `coordinateFunctional` | `MeanAffinePolynomial.lean:13` | PASS；由原 Euclidean 坐标和指定斜率构造真实 CLM。 |
| 15 | `coordinateFunctional_basis` | `MeanAffinePolynomial.lean:16` | PASS；该 CLM 在标准基上的作用确为相应斜率坐标。 |
| 16 | `meanAffinePolynomial` | `MeanAffinePolynomial.lean:21` | PASS；构造实际 affine map，常数项为 `(∫u−∫A)/volume(S)`。 |
| 17 | `meanAffinePolynomial_apply` | `MeanAffinePolynomial.lean:25` | PASS；实际逐点值等于上述常数加 A(x)。 |
| 18 | `meanAffinePolynomial_derivative` | `MeanAffinePolynomial.lean:30` | PASS；实际 Fréchet 仿射导数精确等于 A。 |
| 19 | `meanAffinePolynomial_residual_ae` | `MeanAffinePolynomial.lean:34` | PASS；真实 L² 残差 a.e. 等于 u−p。 |
| 20 | `meanAffinePolynomial_mean_residual` | `MeanAffinePolynomial.lean:42` | PASS；有界域和正体积保证可积性、合法分母及精确零均值。 |
| 21 | `weakGradientMean` | `H2MeanGradient.lean:14` | PASS；取实际一阶弱导数各分量的积分均值。 |
| 22 | `h2_gradient_mean_bound` | `H2MeanGradient.lean:17` | PASS；全部一阶坐标分别应用弱 Poincaré，再用真实二阶分量收缩给 P D²d²‖field₂u‖²。 |
| 23 | `h2MeanAffine` | `ConvexH2AffineApproximation.lean:16` | PASS；明确选择斜率为上述均值梯度的同一实际仿射 p。 |
| 24 | `h2AffineResidualCoordinates` | `ConvexH2AffineApproximation.lean:20` | PASS；坐标残差为原弱梯度坐标减对应均值常函数类。 |
| 25 | `h2AffineResidual_weak` | `ConvexH2AffineApproximation.lean:25` | PASS；原状态和实际仿射函数的弱导数相减，得到真实残差弱身份。 |
| 26 | `h2AffineResidual` | `ConvexH2AffineApproximation.lean:34` | PASS；由这些已证明的弱身份组装真实弱 H¹ 残差 r。 |
| 27 | `h2AffineResidual_value` | `ConvexH2AffineApproximation.lean:40` | PASS；r 的 scalar 类精确等于原 u 减同一 p 的 L² 类。 |
| 28 | `h2AffineResidual_value_ae` | `ConvexH2AffineApproximation.lean:45` | PASS；同一 r 的代表 a.e. 等于实际 u−p。 |
| 29 | `h2AffineResidual_gradient_component` | `ConvexH2AffineApproximation.lean:52` | PASS；每个真实梯度分量等于原弱梯度减同一 p 的实际方向导数。 |
| 30 | `h2AffineResidual_mean` | `ConvexH2AffineApproximation.lean:61` | PASS；同一 r 的真实积分为零。 |
| 31 | `h2AffineResidual_gradient_bound` | `ConvexH2AffineApproximation.lean:68` | PASS；坐标平方和与完整梯度范数身份将第 22 项传给同一 r。 |
| 32 | `h2AffineResidual_value_bound` | `ConvexH2AffineApproximation.lean:77` | PASS；零均值 r 的第二次 Poincaré 给 P²D⁴d²‖field₂u‖²。 |
| 33 | `h2AffineResidual_homogeneous_bound` | `ConvexH2AffineApproximation.lean:91` | PASS；非负平方取根并相加给 d(2^d+1)D²，未除以 d、D 或状态范数。 |
| 34 | `exists_convex_h2_affine_approximation` | `ConvexH2AffineApproximation.lean:117` | PASS；全部原弱 H² 状态上供应上述实际 p/r，并由有界性内部构造有限测度实例。 |

## 原文定位与未清偿范围

原 `paper/main.tex:304` 约定 D^j 为全部 j 阶空间导数的 Euclidean 分量范数。此批 RHS 为原真实二阶导数字段的 L² 范数，不是完整 H² 范数、点态 Hessian 上确界或重新定义的误差能量。

Appendix B 的 `lem:fd-boundary-affine`（`paper/main.tex:2803`）要求 v∈H²(B_K)、指定物理面上零迹，以及仿射 p 在这些面上同样为零。其证明第一步（`paper/main.tex:2816`）取得未校正的仿射逼近，随后还使用真实迹定理与有限维面限制核校正。T074 清偿前一类未校正逼近，对任意有界开凸域及全部弱 H² 状态适用；并未清偿后两项，更不能把 `h2MeanAffine` 直接当成已满足物理边界面的 p_K。

当前量纲为真实直径上界 D：`‖r‖+D‖∇r‖≤d(2^d+1)D²‖field₂u‖`。应用于原网格块的 h 形式，还需把实际块的 D 与 h 比较及相应几何实例结合。原 B2（`paper/main.tex:2841`）还需矩重构、有限重叠和权比较；Section 6 P1 Step 2（`paper/main.tex:1523` 起）还涉及一般 H² 节点插值及其合法性。本批不能代替这些结论。AUXILIARY 和原文 12/26 的边界正确。

## 全部原弱 H² 状态与实际残差

直接核对 `WeakDerivative` / `SobolevJet`：`SpatialTest S` 是所有全空间 C∞、紧支且支撑位于 S 的测试函数，`IsWeakSpatialDerivative` 对这些全部测试规定真实 L² 配对/积分分部身份。`WeakSobolevJet d 2 (volume.restrict S) S` 的零、一、二阶字段都是原域上的真实 L² 类，各阶、各对称多重指标及全部坐标方向满足该身份。因此本批输入覆盖原分布意义的整个弱 H² 状态，不是光滑子类、某个节点空间或额外闭包子类。

`BoundedAffineSobolev` 先证明实际 p 的平方在紧闭包可积，再限制回 S；不存在把未证明的仿射 L² 资格当作参数。实际仿射导数来自 affine map 的连续线性部分及 `HasFDerivAt`，全局 Lipschitz 性由其真实 CLM 范数证明。`weakSpatialDerivative_of_lipschitz` 对任意 SpatialTest 使用真实积分分部，再利用测试及其导数在 S 外为零识别限制积分；没有把全域或边界项漏掉。

从 u 的一阶弱均值 g_i 构造 `A=∑ᵢgᵢ·projᵢ`；标准基作用身份确保 A(e_i)=g_i。p(x)=c+A(x)，其中 `c=(∫S u−∫S A)/m`，m=volume.real S。所有被积函数在当前有界域可积，m>0 用于归一化。代码证明实际 p 的导数恰为 A，并证明残差真实积分为零，而非只声明一个形式上的均值条件。

实际 r 的 scalar 类定义为 value(u)−boundedAffineLp(p)，坐标类定义为 ∂ᵢu−g_i。用原 u 的全部弱身份减去 p 的真实弱身份，内部供应每个坐标的弱导数资格，再组装完整 H¹ jet。`h2AffineResidual_value`、`value_ae` 和 `gradient_component` 分别在类、a.e. 代表及实际梯度坐标层面识别同一 r 和同一 p，没有为不同估计更换残差。

`coordinateFirstJet_gradient_norm_sq` 通过真实 firstGradientAssembly、各坐标投影以及 `Sym.oneEquiv`，精确得到完整一阶 L² 字段范数平方等于 d 个坐标范数平方和。它没有引入额外 √d，也没有将不同阶的 fiber 混用。最终存在式虽只显式附带 scalar 的 a.e. 身份和估计，其构造就是上述 p/r；r 的实际弱 H¹ 类型及开放域上的弱导数唯一性也排除了自由选择无关梯度的解释。

## 两次弱 Poincaré 与 Hessian 因子

已直接检查当前 `ConvexWeakPoincare`、`InteriorWeakPoincare`、`MollifiedGradientEnergy`、`DomainConvolution`、`PairwiseL2Limit` 和紧凸穷竭依赖的实际类型及证明。原域 L² 零延拓只被用作全空间 L² 数据；它保留的弱测试域仍为 S，不是声称任意 H¹ 状态具有全空间零延拓弱导数。卷积只有在反射核的完整支撑留在 S 时才把实际 fderiv 与原弱坐标卷积识别。紧内子域上该条件由核半径趋零内部供应，再用真实卷积收缩、a.e. 极限/Fatou 和紧凸穷竭传到整个 S。

因此 T073 的 `convex_weak_mean_poincare` 对任意真实 L² 标量 u 和全部已证明的弱坐标 v 给 `∫(u−mean u)²≤P D²∑ᵢ‖v_i‖²`，P=2^d/2；它没有要求额外光滑代表、零迹、全空间弱延拓或目标 Poincaré 界作为前提。T074 两次调用均满足这一原始弱接口。

第一次对每个 U_i=∂ᵢu 应用它，其弱导数为 `W_ij=component(Sym.cons j (Sym.cons i nil), field₂u)`，资格直接来自二阶 jet 的 k=1 弱身份。每个真实 L² 分量满足 `‖W_ij‖≤‖field₂u‖`：先使用分量 a.e. 身份、Euclidean 坐标收缩，再使用 L² 范数单调性。

对固定 i 的 j 求和得到 `∑j‖W_ij‖²≤d‖field₂u‖²`；再对 i 求和得到宽松但正确的 d² 因子。二阶 fiber 由对称多重指标索引，混合项不因交换 i/j 变成两个独立 fiber 坐标；证明没有把双重和误写成它的精确范数平方，而是明确使用 d² 上界。因此得 `‖∇r‖²≤P D²d²H²`，H=‖field₂u‖。

第二次对同一零均值 r 应用完整弱 jet 的 Poincaré，精确使用 scalarLp_norm_sq 及其零均值身份，得到 `‖r‖²≤P D²‖∇r‖²≤P²D⁴d²H²`。这是真实 Hessian 齐次控制，未混入零阶或一阶状态范数。

## 取根、统一量词与退化情形

从值平方界得到 `‖r‖≤P d D²H`，双方非负资格明确供应。梯度界使用 `P≤(P+1)²` 得 `‖∇r‖≤(P+1)dDH`，同样先确认双方非负。再乘以 D≥0 并相加，得到 `(2P+1)dD²H=(2^d+1)dD²H`。这一常数较最优值宽松，但正是所声明的统一维数常数，没有漏掉取根、D 的幂次或第二次 Poincaré。

最终入口对任意 d、原有界开凸 S、全部弱 H² 状态 u 和任意非负距离上界 D 成立，常数显式仅依赖 d，在任何域、状态、直径、网格、权或时间参数之前已确定。内部 [IsFiniteMeasure] 条件从有界性自动构造，最终类型没有额外可积性、光滑性、零迹、仿射逼近、弱 Poincaré 或 Hessian bound 前提。

证明只除以正体积 m，不除以 d、D、H 或任何误差范数。d=0 时坐标和为空，完整正阶 fiber 为零；有正体积的零维域上的状态由其均值常函数表示，结论与构造一致。D=0 不被额外排除；正维正体积开集不可能满足该距离界，零维情形仍合法。H=0 时同一推导直接给零残差，体现仿射核，而非通过除以 H 规避。

## 固定版本、构建与公理

五新模块的 Carleman 导入闭包共 130 个模块，其中 125 个既有模块相对 base 逐字节不变；root 明确导入五模块。AGENTS、治理流程、原论文、Lean/mathlib pin 及两个 CI workflows 均未改。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-h2-affine-full.log` 实际包含 `Build completed successfully (3690 jobs).` 和 5303 项审计通过。固定 `/tmp/carleman-h2-affine-local-axioms.txt` 的 34 项完整展开类型全部逐项与固定源码核对；每项恰有一条完整类型和一条递归公理打印，均只依赖 `propext`、`Classical.choice`、`Quot.sound`。全部 1543 条显式公理打印（1539 个不同声明）亦已扫描，无白名单外公理；末行确认所有 5303 个 Carleman 声明（含生成声明）递归审计通过。

`tools/CheckAxioms.lean` 本批只增加 34 项完整类型和公理打印，遍历全部 Carleman 声明、递归收集公理并拒绝白名单外项的程序未变。五新模块无 sorry/admit 或新增公理。固定本机产物为 1,558,361 bytes，SHA256 `af9e1333b23878c8b4bab7e34e1061af47274b6c79bb8d23afedbb2c19622138`。Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据与签发状态

已独立读取真实 [main/push run 39174132190](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39174132190/attempts/1)，attempt 1，head SHA 精确匹配 checked SHA，顶层 completed/success。三个 jobs 均 completed/success：lean `117813180359`、state-check `117813180602`、dashboard / snapshot `117813799051`。未在任何 job 仍运行时签发。

同次 artifact 元数据已独立读取：`lean-ci-result` id `12153891371`、`lean-declaration-evidence` id `12153906407` 均绑定该 run、main 和同一 head SHA。实际读取 `/tmp/carleman-h2-affine-main-ci/result.json`，status=PASS，checked_sha/source_head_sha 均为 `55dbf36858608cc7ff9300ef61430e18fa0bdadf`，ci_url 精确对应该 run/attempt，finished_at=`2026-10-18T22:54:47.239010+00:00`，target 为 `Carleman`。Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib pin 均匹配。

实际读取 `/tmp/carleman-h2-affine-main-axioms/axioms.txt`，与固定本机产物逐字节完全相同：1,558,361 bytes，SHA256 `af9e1333b23878c8b4bab7e34e1061af47274b6c79bb8d23afedbb2c19622138`。远端产物再次核对 34 项完整类型和递归公理，全部 1543 条显式公理打印无白名单外项；末行确认所有 5303 项递归审计通过。

最终结论：**T074 / C090 PASS，可将 C090 升为 REVIEWED，保留 AUXILIARY。** 34 项及所声明的全部弱 H² 状态未校正仿射逼近范围通过，未发现数学缺陷。完整 B1 的物理面零迹校正、B2/P1 等仍待，原文计数保持 12/26。本 Agent 仅写本报告，未修改实现、台账、root 或原稿，未 commit/push。
