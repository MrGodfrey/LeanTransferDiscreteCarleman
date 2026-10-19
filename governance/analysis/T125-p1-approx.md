# T125：原全部弱 H²∩H¹₀ 的真实 L² 投影误差与 N3

本阶段把已经证明的全域允许权节点插值、全部原 conforming P1 空间上的加权 L² 投影稳定性，以及真实加权逆估计组合为原 P1 Step 2 的 h² 值误差和 h 能量误差，进而清偿原 N3 接口。

`MaxDiameterWeight` 证明真实上尺度比较 ℓ_K≤B diam(K) 导致任意网格幂乘子范数≤(B h)^p 倍原权范数，使用实际最大直径和逐单元乘子，不引入单元数量常数。零维、空索引或h=0无需相除。

`WeakH2ProjectionApproximation` 固定域/profile/d/形状/上下尺度与原 grading γ<Γ_d 后，先选统一δ>0、δ≤1和C>0，再量化全部实际网格与全部原弱 H²∩H¹₀ 状态。取前阶段同一真实 e=u−I_hu，令p为Π_h(value e)的实际H¹₀弱jet。投影恒等式给 E=p−e 的值恰为 Π_h(value u)−value u；E在全部时间权、τ/t和符号之前选定，且属于原H¹₀。原完整P1空间、真实正交投影及其全部弱梯度没有替换。

σ与ℓ⁻¹σ的真实投影稳定性及逆估计控制p；原节点界和上尺度比较给σe≤CE B²h²‖σHess u‖与σ∇e+ℓ⁻¹σe≤CE B h‖σHess u‖。hq(t)≤1把qσe降为一阶h，得到σE≤C h²‖σHess u‖及Nσ(E)≤C h‖σHess u‖。两个常数由固定Cp/CI/CE/B代数合并，独立于全部网格、状态、时间、T和实幂。原下尺度cD≤ℓ内部转换为D≤c⁻¹ℓ，不新增未清偿近似前提。

`FullP1ApproximationInterface` 对任意原域子空间D⊆H²、D⊆H¹₀，将原domainSobolevJet v输入上述全弱结论。误差−E经value唯一性恰为实际conforming重构的v−R_hJ_hv的唯一弱jet，符号由真实范数偶性处理。实际Hessian项≤原parameterNorm Rσ(v)，因此得到Section4.WeightedApproximation，aE=C h、a0=C h²，对全部原周期内时刻和D状态成立。D⊆H²是原N3/A1接口条件，不把具体Dirichlet算子H²正则性宣称已证。

三模块3显式声明，定向3711 jobs、全库3887 jobs通过；6743声明递归公理审计PASS。固定产物 `/tmp/carleman-p1-approx-local-axioms.txt` 为 2070769 bytes，SHA256 `dc0904cf0618ed061e9f64ee2a0f8fc6109195e6b03eb858a85a87eb51a31d9d`。

AUXILIARY，原文14/26。真实P1投影误差与N3现已清偿；仍须与完整原L²(ω)控制、N1/N2/N4/N5数值接口组装，且具体连续H²正则性与连续CE仍属独立目标。P011不提前提升，原稿未修改。
