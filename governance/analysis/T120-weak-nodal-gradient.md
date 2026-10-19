# T120：原全部弱 H² 的真实局部节点梯度误差

本阶段把 T113 的光滑局部梯度估计传到原全部弱 H² jet，保持同一个实际节点插值、完整弱梯度与同单元原弱 Hessian 能量。范围对应原 P1 Step 2 局部标准插值估计，尚不包括全局权和 H¹₀ 边界资格。

`L2ConstantShiftLimit` 在有限测度上证明强 L² 收敛在减去收敛的常数后保持，常数函数的真实 L² 范数与全部 MemLp 条件显式供应。`SimplexNodalDerivativeLimit` 将实际 affineScalarDerivative 与真实有限节点导数线性映射严格识别，证明全部节点值收敛给真实导数的算子范数收敛，并把完整一阶 DerivativeFiber 平方范数严格展开为 d 个坐标平方和。固定单纯形上的有限维连续性只用来传极限，不用来选择统一估计常数。

`SimplexH2GradientLimit` 对同一个 C² 序列，利用实际节点导数极限以及全部一阶强 L² 极限，得到真实梯度残差的各坐标平方积分收敛。随后对 T113 的光滑梯度估计和 T119 的完整 Hessian 坐标能量界取极限。内球半径 r>0、直径上界 D、D≤κr 与实际单元直径条件保留；常数完全沿用显式维数/形状公式。

`WeakH2NodalGradient` 对 T119 同一个实际闭域光滑序列限制到 K⊆closure S，以限制测度单调性证明全一阶、二阶误差仍强收敛。通过 L² 零延拓与 derivativeComponent 的严格相容性，将各坐标残差平方积分之和识别为

∫K ‖zeroExtendLp(field₁ u)−derivativeOneFiber(D I_K f)‖²。

最终上界为 (2^d d+128 κ² ‖derivativeOneFiber‖²) D² C(d,2)² d²乘同一 K 上原 field₂ 的平方积分。所有二阶有序坐标均保留，d² 是对真实完整弱 Hessian 的安全维数常数。没有将单元能量换成全域能量，没有使用只针对光滑状态的替代空间。

最终 `exists_nodal_h2_representative` 对每个原弱 H² 状态自动选择一个闭包连续代表 f，再对所有实际单纯形、内球、直径和形状参数同时给值误差与梯度误差。值界为 16 D⁴ C(d,2)² d²，梯度界为上述常数；代表先于所有单元选择，能用于同一真实网格的全部节点。

四模块9显式声明，定向3357 jobs、全库3869 jobs通过；6688声明递归公理审计PASS。固定产物 `/tmp/carleman-weak-nodal-gradient-local-axioms.txt` 为2027715 bytes，SHA256 `c66d73205c28466b4c7943ff923ec4a234bbf5388e87c608f49f528fc6839107`。

AUXILIARY，原文14/26。全弱局部值/梯度节点误差已完成。H¹₀连续代表边界零值、实际 conforming 插值资格、全局允许权及完整P1仍待，P011不提升。原论文未修改。
