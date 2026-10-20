# T189 — 原差分状态方程的完整时空弱恒等式

对应 `paper/main.tex:2385–2400`：以 `dt φ_h^(n−1)` 测试原后向 Euler 方程，求和分部，并通过实际空间和时间重构表达每一项。数学基线为 T188 的 `32711e6669f223eba5851b43e9ec886a40c45b6e`。本批保持 AUXILIARY；尚不把有限网格恒等式称为极限 PDE，覆盖仍为17/26。

`Physical.physical_summation_by_parts` 对任意完整状态和测试序列证明

`Σ ⟨y^(i+1)−y^i,φ^i⟩ = ⟨y^N,φ^N⟩−⟨y^0,φ^0⟩−Σ⟨y^(i+1),φ^(i+1)−φ^i⟩`。

没有周期化或丢弃端点，通用形式也允许 N=0。`Physical.forward_equation_weak_identity` 直接使用原 `ForwardEquation`，测试不要求满足伴随方程；dt≠0 用于消去实际离散导数中的倒数。原时间网格 dt>0 自动给该条件。恒等式不需要 CFL、小势、状态预算、正性或算子对称性。

`timeCellReconstruction_difference_inner` 将实际物理内积中的差分测试和写成真实 Bochner L² 内积：时间单元体积 dt 与测试差商中的 dt⁻¹ 精确抵消。固定时间版本只沿 period=T 运输测度。整个推导使用先前真实指示函数重构的内积身份，不以形式上的求和符号代替 Bochner 对象。

`cartesianPhysicalLaplacian_gradient_pairing` 对两份任意原节点状态给精确双线性刚度身份，右侧为实际 Kuhn 弱梯度的全空间 L² 内积。`cartesian_forward_reconstructed_weak_identity` 因此在原全部有限差分状态空间得到

`−⟨E y⁺,E D_t φ⟩_time + ⟨∇R y⁺,∇R φ⁻⟩_time + ⟨P(E y⁺),E φ⁻⟩_time`

`= ⟨E y⁰,E φ⁰⟩ + ⟨K u,E φ⁻⟩_time − ⟨E yᴺ,E φᴺ⟩`。

这里 E 是实际对偶单元等距重构；G=∇R 来自实际 Kuhn jet 的全部一阶字段；K=E B 是原控制节点零延拓再重构；P 是原 b 的实际时间—对偶单元平均值在空间胞元上的乘子。测试取前一时间层，状态、势和控制取本步，与原隐式方程完全一致。所有内积为真正的物理空间或 Bochner L² 内积，可按既有 L2.inner_def 展开为积分。允许任意维数和空内部节点/控制集，没有固定长宽比、网格嵌套或时间—空间耦合。

`cartesian_fixed_forward_reconstructed_weak_identity` 将同一恒等式放入固定盒 lo/hi 和固定时间 T，使用实际 E、Kuhn jet、K 及平均势的等式运输。`cartesianBoxReconstructedPotential_commute` 另外公开真实固定盒乘子交换身份；不会把任意乘子当作原平均势。两个 `...multiplier_inner` 定理用原实乘子的自伴性将势从状态移到测试，供后续弱—强配对使用；它们不声称跨网格强收敛。

剩余工作明确包括：光滑测试及差商的时空强一致性；势乘积的产品测度/Bochner 空间连接；沿状态与控制共同子列传递各项；原终态衰减；V′ 时间导数和连续端点。既有 T188 负责状态弱子列，本批提供与该弱子列处于同一实际空间的有限网格方程，但不把未证测试逼近或极限识别隐藏为完成结论。
