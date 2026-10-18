# T062 / C078 独立本机验收

- `checked_sha`: `699fd4292136039b671d27e09f6e5758a1083f2a`
- `base_commit`: `05aadb86ef406e8e1f843a74ddace902041d79e9`
- `reviewed_at`: `2026-10-18T21:29:10+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原Section 6 Step 3中实际σ²p节点插值残差的单元加权值／导数积分估计。全域完整V_h识别、真实弱梯度和全网格求和尚待，本批不完成原eq:testsuper或完整prop:p1，原文计数保持 **12/26**。

独立读取固定提交四模块的全部证明、10项实际展开类型、相关真实依赖和T062规格，对照原 `paper/main.tex` Section 6 Step 3。执行者说明、定理名称及CI不替代数学审查；后续工作区草稿不属于本报告。

## 全部10项声明

完整名称均以前缀 `Carleman.` 开始。顺序与固定C078、T062及交付JSON完全一致。

| # | 声明（省略 Carleman.） | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `affineNodalBound` | `Spatial/AffineNodalBound.lean:15` | PASS；P由实际仿射函数在真实顶点的平方和平方根定义，非任意上界参数。 |
| 2 | `affineNodalBound_abs` | `Spatial/AffineNodalBound.lean:19` | PASS；各节点平方≤总和，实际重心插值的非负性及仿射再现给整个闭单元上的绝对值界。 |
| 3 | `affineNodalBound_sq_mass` | `Spatial/AffineNodalBound.lean:33` | PASS；真实质量积分下界给P²\|K\|≤(d+1)(d+2)∫p²，未除以单元体积或状态范数。 |
| 4 | `affineNodalBound_energy` | `Spatial/AffineNodalBound.lean:48` | PASS；实际恒定仿射导数、完整一阶fiber范数反向比较及平方和不等式给所需两项能量，常数只依d。 |
| 5 | `norm_sq_div_integral_le` | `Spatial/WeightedCellError.lean:13` | PASS；正连续权、真实连续误差和紧单元保证可积性，逐点合法除以w后积分给E b B²\|K\|。 |
| 6 | `affineNodalBound_weighted_energy` | `Spatial/WeightedCellError.lean:37` | PASS；b≤Ew分别乘p²与完整梯度平方并作实际积分比较，得到真实加权能量。 |
| 7 | `weighted_cell_error_transfer` | `Spatial/WeightedCellError.lean:85` | PASS；内部消去P与单元体积，保留C E² A²和q⁴／q²两项，无目标积分界前提。 |
| 8 | `allowedSquaredWeight_local_integral_errors` | `Weights/SquaredCellIntegral.lean:13` | PASS；真实σ²、真实节点插值及域内乘积导数字段给h⁴／h²加权积分界，C先于所有状态和单元参数选取。 |
| 9 | `squaredNodalResidual_fderiv_ae` | `Weights/SquaredCellGradient.lean:13` | PASS；真实单元内部将域内乘积／差法则提升为HasFDerivAt，零测边界给整个闭单元上的a.e.实际fderiv身份。 |
| 10 | `allowedSquaredWeight_local_residual_integrals` | `Weights/SquaredCellGradient.lean:30` | PASS；用该a.e.身份替换实际积分，输出同一个真实残差的值与完整实际导数估计，常数不变。 |

## 实际节点值、质量与两种导数范数

T为真实非退化全维仿射单纯形，K为其顶点凸包，p是任意实际仿射标量函数。P=(Σ_i p(v_i)²)^(1/2)使用真实函数值；单项平方界、非负重心系数及仿射再现给|p(x)|≤P，对所有x∈闭K成立。没有对Lp任意代表作节点求值，也没有假设待证的点态界。

所用质量下界来自已经实际积分的单纯形质量矩阵：∫_K p²≥|K|Σ_i p(v_i)²/((d+1)(d+2))。乘正数D=(d+1)(d+2)即得P²|K|≤D∫p²；因此估计中的原体积与真实质量相配，既不需要|K|的统一正下界，也不产生最小单元体积或节点数因子。这里有限个d+1节点只进入固定维数常数。

`affineScalarDerivative p`是实际fderiv，且在全空间恒定。`derivativeOneFiber`逐个实际正交基向量读取CLM，形成全部一阶Euclidean坐标；其注入性由全部基向量上的值决定线性映射证明，有限维范数比较给R>0及‖Dp‖≤R‖derivativeOneFiber(Dp)‖。R在任何单元、p、q之前选取。恒定导数的真实积分等于该fiber范数平方乘|K|，再用(a+b)²≤2a²+2b²得到

\[
(q^2P+2q\|Dp\|)^2|K|
\le (2D+8R^2)\left(q^4\int_Kp^2+q^2\int_K|\nabla p|^2\right).
\]

后续将导数残差的CLM点态界转为fiber界时，另用连续线性映射的正向算子范数 `‖derivativeOneFiber‖`。两个方向都实际证明并调用，没有把CLM算子范数与Euclidean坐标范数直接等同。p=0、Dp=0以及d=0均不除以相应量；零维空间中的fiber为空、实际导数为零，证明仍成立。能量引理允许任意实q，因为这里仅使用q²／q⁴与平方和估计；后续误差转换明确要求q≥0，以保证J=q²P+2q‖Dp‖非负。

## 正权、真实可积性及积分转换

基础积分引理对任意NormedAddCommGroup值误差e成立。w、e在紧单元上连续，w逐点严格为正，所以‖e‖²/w连续且真实Lebesgue可积。由b>0、B≥0、‖e‖≤Bb和b≤Ew，逐点得到‖e‖²≤bB²Ew，再合法除以正w并积分，得到E b B²|K|。证明没有用Lean对不可积积分的默认值取得虚假估计；所需连续性和紧性明确供给integrableOn。首个引理虽未单列E≥0，但不需要乘以未知符号的E，所有不等式乘数为bB²≥0；后续转换明确保留E≥0。

加权能量引理把b≤Ew分别乘p²和真实梯度平方，以实际可积函数的积分单调性得到b∫p²≤E∫wp²及相应梯度不等式。于是bJ²|K|≤C E(q⁴∫wp²+q²∫w|∇p|²)。实际误差满足|e|≤A b J时，上一引理取B=A J，给E A²(bJ²|K|)，两式相接准确产生E²而非E或E³。C仍只依d，早于T、p、q、w、e、b、E、A。

## 实际σ²p残差、统一常数与原文对应

最终权w确实是 `(q^τ exp(qηρ))²=σ²`；原允许权乘子平方的实际身份已在固定依赖中证明。q≥1、任意实τ及|η|=1使w严格正。I为真实节点值w(v_i)p(v_i)的仿射插值，e=wp−I；不是另设一个满足误差条件的替代函数。分母为w=σ²，因此左侧正是σ⁻¹e及σ⁻¹∇e的平方积分。

固定数据为维数d、开凸S、紧闭包、在闭包上实际C²的ρ和非负形状参数κ。定理先取C>0，之后才全称量化实际T⊆closure S、q、τ、η、h、内球中心a／半径r以及任意p。几何前提是所有单元点距离≤h、hq≤1、r>0、ball(a,r)⊆K和h≤κr。h≥0由同一顶点的自距离内部推出；没有额外非零网格或非零状态假设。

真实C¹ profile在固定紧凸闭包上提供D₁≥1和Lipschitz界。取E=exp(2D₁)，同一单元的真实权比较给锚点值b=w(v₀)>0及b≤Ew(x)；它不依赖τ，也不依赖q的绝对大小。T061的真实域内导数和节点误差给值误差≤2C₁bJh²及CLM导数误差≤(1+4κ)C₁bJh，其中J=q²P+2q‖Dp‖；新代码内部用实际affineNodalBound清偿P前提。

值积分转换取A=2C₁h²；导数转换取A=F C₁h，F=‖derivativeOneFiber‖(1+4κ)。域内字段G=w Dp+p fderivWithin w在闭单元上连续，因为开凸域闭包的UniqueDiffOn与真实C²正则性保证fderivWithin的连续性。应用转换得到两个估计，统一采用

\[
C=C_0E^2C_1^2(4+F^2)>0,
\quad \mathcal E_K=q^4\int_K\sigma^2p^2+q^2\int_K\sigma^2|\nabla p|^2,
\]
\[
\int_K\frac{|\sigma^2p-I_K(\sigma^2p)|^2}{\sigma^2}
\le Ch^4\mathcal E_K,\qquad
\int_K\frac{|\nabla(\sigma^2p-I_K(\sigma^2p))|^2}{\sigma^2}
\le Ch^2\mathcal E_K.
\]

C仅依固定域、profile、d和κ。两项q⁴与q²、乘积导数中的系数2及h的四次／二次幂均保留。没有混入单元数、最小体积、状态、q、τ、η或时间区间T。把q取为任意时刻q(t)可直接应用同一个常数；本批不另证明时间性质，也不扩大主定理的允许权族。空域不可能容纳真实非空单元，相关全称蕴含合法空缺；d=0、零状态／零梯度无异常除法。

这些平方局部界与原文Step 3的|D²(σ²p)|≤Cσ²(q|∇p|+q²|p|)及单元插值尺度一致。当前采用真实域内Taylor／Lipschitz导数字段证明局部误差，无需调用尚未完成的一般H²插值命题。原9.26-eq10、9.26-eq11还需完整V_h状态和全域节点残差的识别、弱梯度及单元求和；原eq:testsuper还需投影／逆估计组装，本批未声称这些结论。

## 域内字段到实际fderiv

独立复核 `squaredNodalResidual_fderiv_ae`：真实单元边界Lebesgue零测给restrict K=restrict(interior K)。对x∈interior K，从ρ在外部集合K₀上的实际C²取得w的HasFDerivWithinAt，沿真实包含K⊆K₀限制到单元。乘积法则给wp的域内导数G；因为单元此时是x的邻域，转为HasFDerivAt，再减去真实仿射I的导数，准确识别实际fderiv e=G−DI。

该证明只在内部作邻域提升，没有把一般边界的fderivWithin当成全空间导数，也没有假设ρ在域外C²。零测边界只用于积分a.e.替换，未用来推出边界处逐点可微。最后以integral_congr_ae替换完整fiber平方／正权分母，得到上面的真实导数积分结论；它仍是局部经典导数的a.e.积分结论，并未冒充全域弱梯度。

## 固定依赖、构建与公理

四新模块的Carleman导入闭包共111模块，其中107旧模块与base逐字节一致，新增恰为本批四模块。另独立比较实际质量积分依赖闭包100模块与已验收C070版本 `cbea02af04b947ec6f1b1c6e3cfb0da5bd65e5a7`，全部不变；实际点态乘积误差依赖闭包81模块与已验收C077版本 `05aadb86ef406e8e1f843a74ddace902041d79e9` 全部不变。已直接读取实际导数字段、范数比较、质量、域内Taylor、内球梯度估计、权比较及零测边界等关键依赖。

原稿、治理协议、工具链pin及CI工作流与base一致。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean pin为4.35.0，本机实际mathlib HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且其工作树干净。root显式导入全部四模块；CheckAxioms包含本批10项的完整 `#check @...` 和 `#print axioms ...`。

固定本地全部10项完整展开类型已逐一核对，清单与固定C078/T062及交付JSON相同，每项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。全部1392条显式公理记录也只有这三种正常基础公理，无sorryAx。全局检查器通过privateToUserName覆盖Carleman声明，递归collectAxioms，并仅许可上述三项，不仅检查公开导出或本批10项。

`/tmp/carleman-weighted-local-errors-full.log` 实际包含 `Build completed successfully (3641 jobs).` 和 `Axiom audit passed for all 4951 Carleman declarations.`。固定本地 `/tmp/carleman-weighted-local-errors-local-axioms.txt` 为 **1,435,107 bytes**，SHA256 **`bde1a6a8e42f9da75df6d4002f6e163e0d878f6ae653b576848f26a5dbb1cf52`**。

已独立通过GitHub connector读取 [main CI 39167621125 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39167621125/attempts/1) 及jobs：main/push，head SHA精确匹配固定版本，run为completed/success；lean（117793770572）、state-check（117793770745）、dashboard / snapshot（117794598975）三项均completed/success。实际构建、checked source记录、两份证据上传及快照步骤均success。同run的lean-ci-result artifact（12151556066）和lean-declaration-evidence artifact（12151187035）绑定固定SHA。

已实际读取原始 `/tmp/carleman-weighted-local-errors-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=699fd4292136039b671d27e09f6e5758a1083f2a`，targets为Carleman，`finished_at=2026-10-18T21:26:04.696468+00:00`，ci_url与上述run/attempt一致。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-weighted-local-errors-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,435,107 bytes**，SHA256 **`bde1a6a8e42f9da75df6d4002f6e163e0d878f6ae653b576848f26a5dbb1cf52`**。另逐名复核远端10/10完整展开类型及正常基础公理集合，1392条显式记录无其他公理；末行实际为 **`Axiom audit passed for all 4951 Carleman declarations.`**。无sorryAx，未混用其他SHA、运行或后续工作区产物。

## 验收决定

**C078：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定版本10项未发现需要修复的实际节点值、质量积分、正权除法、完整梯度范数、真实残差、单元尺度或统一常数量词缺陷。实际展开类型、递归公理及同SHA正式main CI均已独立核实。

本批完成局部加权残差积分桥。完整V_h上的全域残差、弱梯度和网格求和，以及一般H²插值和最终超逼近尚待；不能因此提升P011/P014/P015或其他完整原文结果，原文仍12/26。

本次仅写本报告，没有修改证明、台账、覆盖表、原稿或root导入，没有commit/push。
