# T124：原全部弱 H²∩H¹₀ 的全域允许权节点插值估计

本阶段完成原 P1 Step 2 的两个节点插值估计 `eq:p1-interpolation` 和 `eq:p1-interpolation-energy` 的真实弱函数版本。常数在所有网格、全部原弱 H²∩H¹₀ 状态、所有时间、实幂和两种权符号之前选择。对每个原状态，选定同一个 f 和真实 H¹₀ 误差 e，然后同时适用于全部允许权。

`WeightedIntegralTransfer` 在任意测度和实际标量/向量 L² 类上，从无权平方积分界转到局部可比权。真实正锚 s 两侧比较给 W s 与 W/s 的范数界，平方后 s 精确消去，损失 W⁴。函数 MemLp 接口通过其真实 toLp 的 a.e. 身份传回积分；没有把不合法函数的默认积分当能量。

`CellwiseScaledWeight` 定义实际有限网格单元乘子 c_K σ（复用 inverseWeight 的双逆，c=0也合法），给真实单元 a.e. 取值、任意向量 L² 的精确平方积分求和，以及统一的 |c_K|≤B 全域范数上界。闭单元公共面以已证原分割的零测交集消除，不产生依赖单元数的重叠常数。`WeightedCellAssembly` 将真实局部加权界求和到 ℓ²σH 或 ℓσH 的实际全域范数；逆尺度值误差使用同一精确恒等式 (ℓ⁻¹)²ℓ⁴=ℓ²。

`WeakH2WeightedNodal` 从 T123 的同一 f/e 和全部单元估计出发。假设真实形状 D_K≤κ r_K 与 D_K≤Bℓ_K，局部权比较 W，在保持同一单元 Hessian 能量的同时，将 D_K⁴/² 转为 B⁴/²ℓ_K⁴/²。C=1+sqrt(A0)+sqrt(A1)>0，其中 A0=W⁴16 C(d,2)²d²B⁴，A1=W⁴(2^d d+128κ²‖derivativeOneFiber‖²)C(d,2)²d²B²。于是 σ值误差≤C‖ℓ²σH‖，σ梯度误差+ℓ⁻¹σ值误差≤C‖ℓσH‖。C仅依赖固定d/κ/B/W，f/e先于所有w选择，完整原状态范围不缩小。

`WeakH2AllowedNodal` 从原固定C¹空间profile在有界开凸域的真实Lipschitz界内部取得 W=exp L，再由 h q(t)≤1 和每个真实顶点锚取得局部权比较。结论覆盖所有TimeWeight、所有τ,t、|η|=1，包含σ及σ⁻¹；没有固定状态或时刻依赖常数，没有向结论添加目标估计假设。原下尺度比较 cD_K≤ℓ_K与本批 D_K≤Bℓ_K 等价（B=1/c>0）；上尺度比较仅在后续全局 h²/h 估计中使用。

五模块10显式声明，定向3400 jobs、全库3884 jobs通过；6740声明递归公理审计PASS。固定产物 `/tmp/carleman-weak-weighted-local-axioms.txt` 为 2061805 bytes，SHA256 `96d63e0cd091e26aa0e452ab5323ef969447a8f055fbe6d03f6430bb400b5b4b`。

AUXILIARY，原文14/26。原全域节点插值的两个允许权估计完成；下一步仍须接原L²投影、h²/h误差界、P1数值接口，P011不提前提升。原稿未修改。
