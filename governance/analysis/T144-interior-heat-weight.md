# T144：连续热算子所用实际高斯权及空间矩阵

本阶段对应原稿 Proposition `prop:continuousCE` 证明的权函数选择、矩阵计算和法向符号步骤。它不声称整个连续 Carleman 估计：点态热算子恒等式、实际面上的 Green 积分、时间端点通量、低阶项吸收以及最终密度/时间反射仍未完成。申请 AUXILIARY 验收，不提升 P024。

实际函数为 ψ(x)=−‖x−c‖²、φ(x)=exp(l ψ(x))、ρ=φ−2。三个函数均全空间 C∞。一阶导数、ρ 的双方向二阶导数和 ψ 的梯度均由 Lean/mathlib 的真实 Fréchet 导数和 Riesz 梯度证明；没有把导数值作为未证明字段。二阶导数为 4l²φ⟨x−c,u⟩⟨x−c,v⟩−2lφ⟨v,u⟩。l≥0 时 0<φ≤1 且 −2<ρ≤−1；实际 SpatialProfile 在任意测度上都取原 ρ 值，全局 bound=2，并构造原 SmoothOnClosure。

空间矩阵从原来的导数定义：冻结任意 q，ℓ=qρ，实际 `spatialLaplacian` 为正交坐标二阶 Fréchet 导数的迹，Ψ=−Δℓ−8qlφ；`interiorHeatMatrix(u,v)=2D²ℓ(u,v)−(Δℓ+Ψ)⟨v,u⟩`。证明其恰为 4qlφ⟨v,u⟩+2ql²φ⟨∇ψ,u⟩⟨∇ψ,v⟩，与原文的 c 矩阵一致。这里没有把点态恒等式里矩阵项外面的系数 2 混入 c。所有 u、v 和 q 的全空间量词保留。q≥0 时二次型至少为 4qlφ‖u‖²，固定有界空间范围与 l>0 后获得 K>0，且 K 先于所有 q、x、u。

原书公式的定位已实际核对：Fu–Lü–Zhang, *Carleman Estimates for Second Order Partial Differential Operators and Applications*, 2019, DOI 10.1007/978-3-030-29530-1，标准 bib 键 `fu2019carleman`，Corollary 3.1，印刷第60页（PDF第69页）。本地原 PDF `/Users/wangyu/Documents/math/article/fu2019carleman-Carleman estimates for second order partial differential operators and applications.pdf` 已提取并渲染阅读。p=Id、Φ=0 的 (3.5) 正是上述 2Hℓ−(Δℓ+Ψ)Id。本批未直接宣称形式化该书完整 (3.3) 恒等式。

梯度的精确范数平方为 4‖x−c‖²。任意 r>0 与原吸收系数 C，内部选择 l=max(1,C/(2r²))，使球外 l‖∇ψ‖²≥2C。任意支持面法向 n 满足对全部 y∈S 的 ⟨y−x,n⟩≤0，且 c∈S，则真实 ∂nφ≤0，故原通量标量 2q∂nφ a²≤0。此定理明确使用真实支持面几何条件，并不假装已经证明 Green 公式或法向迹的存在。

最终 `exists_interior_heat_weight` 从有界 S 和非空开观测集 W⊆S 内部选 c、r、l、κ、K，闭球包含于 W，ρ 为原负光滑权，φ 在 S 有严格正下界 κ，球外梯度阈值、所有 q≥0 的真实矩阵一致强制性及全部支持面通量符号同时成立。这些选择先于时间、周期、q 和任意状态。原非空开且紧包含的观测域满足此处较弱几何前提；不添加均匀网格、紧支撑状态或任何时间限制。

依赖 C030 的原闭包光滑/Profile 接口及 C149 的真实 Laplacian 定义；原稿未修改。32个显式声明，三模块；全库3976 jobs，递归公理审计仅允许既定基础公理。固定提交、实际 CI 和独立验收另记唯一台账。
