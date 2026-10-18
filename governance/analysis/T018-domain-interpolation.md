# T018：原域参数插值与一般阶时间闭合

基线是父监督者已验收的PR20/main `f90a891faf5c2a421f863a9f6a687cc7bd800912`。main CI39082351052实际3 jobs/32 steps PASS；10新模块及root重编，3384 jobs/2592声明递归审计；三个artifact ZIP按API SHA256核实，声明字节与PR20已验收产物相同。固定Lean4.35.0、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，未lake update、未建worktree。实际任务 `01a1498c-c483-77a5-8b91-14b593452001`；分支 `proof/t018-domain-interpolation`。

## 已完成的分析路线

1. `LocalLipschitzGraphChart`采用通常局部柱形坐标：仅水平球上的Lipschitz性、图过边界中心、局部上图等式。McShane实值扩张和物理球缩小得到T017使用的global graph接口。反向通过边界闭包/连续性推出图过中心，再以逆坐标算子界选柱形半径。因此`boundedLipschitz_iff_global_graph_charts`是真的双向桥，不把新图表谓词静默当原假设满足。
2. `zeroExtendLp`只构造L²等距，限制回原域a.e.等于原类。局部分布弱恒等式转移时测试仍紧支撑于原域；没有跨边界零延拓的Sobolev断言或零迹要求。`reflectedWithin`提供真实κ(x−y)测试，直接证明局部弱卷积交换及真实Fréchet导数。
3. 初始闭球在patch∩Ω内时，整个内锥线段上同半径闭球仍在Ω。由此对真实平滑卷积用FTC。实际产品测度的Cauchy–Schwarz/Fubini证明L²平均界，得到方向链u→v→w的局部卷积插值 `‖κ*v‖ ≤ 2/t ‖u‖ + t ‖w‖`，常数不依赖平滑半径。
4. 用闭增厚补集构造可测内缩区域；它们随bump半径趋零穷尽开集。明确归一bump的a.e.卷积收敛、指示函数和Fatou将估计传回原L²弱类。得到真实原域局部弱插值，没有假定密度或弱FTC。
5. 实际方向a和a+e_i均在内锥内，二者导数差恢复坐标导数。任意方向弱导数由原坐标弱恒等式和正交基展开构造；二阶方向导数是实际Lp分量的二重线性组合。有限patch覆盖的限制L²范数和控制全域范数。固定域后先得δ,K，再对全部阶数、全部弱jet、所有0<t≤δ成立邻阶估计。
6. 对真实Sym分量最大值应用有限最大值原理。其正权为L^(j(2n−j))，L依赖几何δ,K；两邻项缩放后系数至多1/4。取实际尺度t/r，r≥1保证留在允许高度内；得到全部r≥1的统一分量界，最后由Euclidean分量平方和返回完整导数字段范数之和。

结论为任意n及全部真实弱Hⁿ(Ω) jet：
`∃ C≥1, ∀ r≥1, ∀ u, Σ_j r^(n−j)‖D^j u‖L² ≤ C(‖u‖jet+rⁿ‖u‖L²)`。
C在r和u之前选定。既有四个分量最大值声明从full-space推广到任意限制测度/S，旧全空间结论原样保留。

`boundedLipschitz_domain_parameter_interpolation`将此结果用于任意D⊂Hⁿ的唯一真实jet，真正清偿T017的hI。`boundedLipschitz_operator_parameter_graph`再仅用A1正向椭圆界，直接得到原`eq:parametergraph`的Au版本。未使用A1反向界，也未要求D在坐标微分下保持。

## 加权实际后果

- `lipschitz_weighted_euler_sobolev_uniform`：一般m>0、所有周期D(A)节点状态、两方向；完整R₂ₘ为每阶真实加权字段ℓ²范数之和。hI内部由域几何证明。
- `interpolated_weighted_frozen_sobolev_uniform`给一般测度分析提升；其原域入口`lipschitz_weighted_frozen_sobolev_uniform`不保留hI。完整连续R₂ₘ为每阶真实Bochner L²范数之和，先证明实际jet MemLp；时间方向与冻结延拓方向独立。常数可取60+60(2m+1)K，来自已证算子图60和空间参数图。
- `lipschitz_weighted_temporal_error_uniform`：任意实际载荷的Euler解和构造的连续周期弱解，真实加权L²率2160δt、真实N_m率sqrt(466560/c)sqrt(δt)，含实际弱误差jet的MemLp。正、逆权及原form/operator测试恒等式明示。

各阈值在T/grid/q/τ/方向/状态/载荷前选定；权q^τ exp(qρ)、ρ的内禀SmoothOnClosure、A2真实0..2m−1阶交换子和A3保留。连续轨迹仍只有a.e.D(A)、真实H弱导数及周期H迹，未加强为每时刻D(A)。原文不修改。

## 路线调整与剩余工作

先尝试以单侧核高阶缩放导数建立全部局部平滑估计；在已有弱平移界后，改为二阶方向链、有限cover及有限最大值。该路线避免高阶核逐项缩放和任何Sobolev扩张，但保留原域/任意阶/全部弱状态/同一参数常数。旧反射与零延拓高阶扩张方案仍不采用；没有通过添加边界条件绕过缺口。

本阶段C036记AUXILIARY，不新增完整原文结果计数（仍1/26）。原T017 C034的历史已验收版本继续CONDITIONAL，新原域入口消去其hI。B1弱存在/迹、B2、规范B3和B5继续复用；B4时间两率已一般阶闭合。尚未清偿：Section4基于N1–N5的真实空间误差a_E+η_A及a_0+a_E²+η_A、它们与时间误差的统一权族组合、最终TransferBridges实例及原Theorem2.1。还需原连续非冻结图/shifted form的完整原文声明整体验收，不能把组成部分直接算Lemma3.1完成。

同一draft PR交付，不合并；页面由独立任务维护同一private Sites，不另部署，不新建调度。完整SHA、真实CI与自有Lean统计见逐声明核对及任务台账。
