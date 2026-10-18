# T019 — Section 3 完整原命题闭合

基线 main `cfd7d038d322779b1e9bc1cdd076af65e0e829d1`，PR21 已独立验收合并；main CI39086197036 三项32步实际PASS，35项目目标（含24新模块与root）重编，3408jobs/2697递归声明审计，仅标准基础公理。T018记MERGED，C036记REVIEWED/AUXILIARY，同SHA绑定。工具链Lean4.35.0、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`保持固定，无lake update/worktree。

## 数学目标和完成边界

本阶段组合原Lemma3.1、Lemma3.3、Lemma3.4、Theorem3.5的**完整结论**，不是把已证估计继续孤立登记为辅助结果。原Lemma3.2/P005已验收。P004/P006/P007/P008在实际完整构建后记BUILT/PAPER，等待父监督者独立验收；只有REVIEWED才增加原文完成数。Section4、原Theorem2.1及全部26项结果仍未完成。

## 真正非冻结的连续图

`ShiftedGraphRemainder`直接使用`shifted_periodic_graph_sq`和真实μ(t)=(Lq(t))^(2m)。L^(2m)≥4mβ给三项平方图界；没有步长、节点、冻结乘子或δ条件。真实时间对数导数由`logDerivative_spacetime_le`控制，L先于T/q/τ取大使其≤μ图项的1/24。`exists_weighted_graph`给实际加权弱图代表，`weighted_evolution_identity`给真实载荷、空间交换子和时间导数余项。推出30倍带真实交换子余项的图界。

原域已证hI和正向A1给交换子小量1/60；逐t下界Hq^(2m)≤(Lq)^(2m)只需L的统一阈值。真实交换子吸收后是60倍算子图估计。`InterpolatedShiftSobolev`先证原a.e.域代表的jet MemLp，再逐真实导数字段提升到Bochner L²并求和，得到完整R₂ₘ；`LipschitzShiftSobolev`内部从已证原域插值供应hI。没有反向椭圆界、导数域保持、核限制、零迹或额外的逐时刻D(A)正规性。

`periodCarrier T hT`仅为既有连续Sobolev库装载区间的内部编码，period=T、timeMeasure=volume.restrict(Ioo 0 T)均证明。`Conclusions.primitive_on_interval`只量化T>0；它的μ仍是每时刻实际q(t)，没有冻结或网格条件。周期载体的steps=1不参与任何节点或延拓运算，不是把连续问题冻结成一格。

## 原假设显式接入

`OriginalForm`把原V≤H^m、V在H^m闭、H中稠密、真实H^m Hilbert范数上的有界对称强制型双线性形式打包。`conformingHilbert_completeSpace`供应完备性。`valueEquiv`是全部原V与Hilbert实现的线性等价；`scalarForm_value`和`operator_test`识别原标量形式与算子测试身份。`ofBilinear`从原双线性映射及显式H^m有界性构造连续形式，并证明全部V状态上scalarForm等于原a；连续映射表示不是新增分析假设。

`associated_iff`双向识别**完整原变分定义**；`identify_operator`和`section3_original_operator`实际调用`IsAssociated.domain_eq/operator_eq`。后者以原D、原A、原D上的正向椭圆正则性为输入，输出D等于完整模型域以及A逐状态作用相同，并经此等式转移全部结论。没有仅在稠密core或核上识别算子。

`TimeWeight.ofInterval`从原闭区间q和上下界给一个全实线有界代表；原区间逐点不变，区间外值只是钳制延拓。`ofInterval_regularity`从原C²及一阶导数界、周期端点给所需正则性，对任意同周期编码成立。原q''界与导数端点匹配未被使用，故不增加原假设。`exists_profile_of_smooth`从原有界域紧闭包和内禀SmoothOnClosure给真实空间profile的有界性及可测性。原ρ负性不是这些辅助结论所必需，故允许更大输入范围。

`AllowedFamily`只有原A2的域/V保持、原交换子界，以及A3的上下界；没有插值或结论字段。Bool显式选择±ρ，τ在对称区间内；`signed_neg`和`AllowedFamily.inverse`同时取反ρ与τ，给实际逆权。全部常数在这两个profile、T/q/grid/τ/载荷/状态之前由max/min共同选定。

## 完整结论与常数量词

`EulerEstimate`包含每个H节点载荷的全D(A)周期序列存在唯一性，以及所有满足方程的序列的实际加权差分+节点R₂ₘ界。`euler_solved_uniform`将原残差精确替换为载荷，不把构造解的估计当任意解的估计。

`ContinuousEstimate`包含每个Bochner L²载荷的完整周期图存在唯一性、实际空间jet MemLp和加权H弱时间导数+连续R₂ₘ界。`PeriodicGraph`和`PeriodicWeakTrajectory`双向桥保持闭区间H迹及a.e.导数/域/算子。新增`graph_equation_iff`证明任意原弱代表的a.e.方程与其图类方程严格等价，域代表只需a.e.。

`TemporalEstimate`量化任意离散解u和任意连续图解p，使用与Euler方向相同的真实cell extension，载荷为真实bar g。`temporal_arbitrary_uniform`用两侧唯一性识别T018构造解，保留真实U−bar u的L²界及实际弱误差jet的MemLp/N_m界。共同常数起点为max(2160,sqrt(466560/c))，误差率分别δt、sqrt(δt)。冻结图的方程方向与延拓方向仍独立量化。

`profile_uniform`和`signed_uniform`取各证明阈值的max、正δ的min及常数max。δ进一步≤1，故dt*qmax²≤δ亦保证dt≤1。`complete_uniform`在选择K之后取L₀(B)=max(Lc,max(1,C+B))：Lc已经包括连续、Euler、冻结和误差的两profile阈值。于是L₀(1)确实支配冻结阈值，Euler可取L₁=L₀(1)，冻结可取δ_time(L)=统一正δ，图常数独立L。没有声称任意事先更小的L₀同样有效。

Lemma3.1的form上界为Cform(L)=C+L^(2m)>0；下界保留**任意B>0的B‖qσv‖²**，不是错误的B‖q^mσv‖²。`Conclusions`同时装配无网格primitive、形式上下界、Euler/frozen和实际时间误差。`OriginalForm.section3`以及原D/A入口供应这整个结构，不假设该结构。

## 余额和下一阶段

B1任意载荷存在、真正H弱导数和周期迹已清偿；B2/B5复用已证结果，Γ仍是普通函数；规范B3和B4的finite/order/shift条款仍复用。B4时间分析现在覆盖完整原允许权族、一般m、全部状态；剩下Section4/N1–N5的实际空间比较及a_E+η_A、a_0+a_E²+η_A系数，随后才能实例化完整transfer并清偿原Theorem2.1。未增加最终离散估计前提，也未将其宣称完成。

本轮编译路线中，限制测度和conformingHilbert的大定义展开触发过默认elaboration预算；改为显式中间类型及局部预算后继续，数学结论未变。临时类型/命名错误均在正式build与审计前修正，不保留sorry或额外公理。

## 下一阶段可复用检查点

Section4先建立真正的N1/N3/N4重构与权测试接口：已有Reconstruction的R/J/Q/G和质量伴随、周期配对可以直接复用，不能假设Q²=Q或G=Id。原eq:thetaEuler应由两个实际Euler方程相减得到；加权时间恒等式需要把既有sum_weighted_increment的标量μ推广为随节点变化的自伴正测试算子T_n。原N4时间导数经真实cell比较给其差分项界，以Lemma3.1任意B余量吸收。再保留真实testsuper和stiffnessdefect，得到a_E+η_A的能量误差。L²必须使用原完整eq:completeidentity以及σ逆Euler图，分别产生a_0、a_E(a_E+η_A)、η_A，最后用a_E≤1得到a_0+a_E²+η_A。Theorem4.2沿真实U−bar u+bar(u−R u_h)分解与已证节点/延拓比较组合，不能用几个未经匹配的标量代替这些对象。
