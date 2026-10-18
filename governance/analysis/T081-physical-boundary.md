# T081：原 Lemma B.1 的物理尺度边界仿射逼近

六模块15声明。本批目标为原 `paper/main.tex` 2796–2838 的完整 Lemma B.1（`lem:fd-boundary-affine`），包括证明末尾两非平行物理面消去仿射核的结论。提交后须按 PAPER 目标独立验收；此前计数仍为12/26。

最终声明 `Carleman.OriginalForm.boundary_affine_lemma` 的量词是

`∀d, ∀κ≥1, ∃C>0, ∀a,b,h>0, h/κ≤bᵢ−aᵢ≤κh, ∀J, ∀u∈H²(B),`

`[原真实面迹 Tr_F u=0 对全部 F∈J] ⇒ ∃p affine, ∃r∈H¹(B),`

`p|_F=0 对全部所选整个闭面，r=u−p a.e.，||r||+h||∇r||≤Ch²||D²u||`。

B 为任意正侧长开坐标盒 `openCoordinateBox a b`，环境维数 n=d+1≥1。任意 J 是全部2n个上下坐标面中的任意子集，因而覆盖原 B_K 的全部物理边界面配置，包含内部盒、单面和角点。不需要假设 J 恰来自某个特定区域；这个更一般的结论可直接用于原 F_K。h 与各侧长的两侧可比性明确表达原稿的 grid-step comparability，C 在位置、侧长、h、J 和 u 之前选取。

输入为原完整 `WeakSobolevJet n 2`：真实 L² 值、全部弱梯度、原对称多指标 Hessian 字段和全部紧支撑光滑测试的分布身份。没有连续代表、光滑性、H¹₀、预设逼近或延拓假设。零迹是 T077 的真正 L² 面迹作用于原一阶截断；输出真实 H¹ 残差的全部弱导数通过原 jet 差构造，值类 a.e. 等于 u−p，故左端确为实际差的 L² 与全梯度范数。

## 等价证明路线与常数

原文把全部 H² 状态拉回单位立方体。本实现采用 T080 已说明的等价路线：T074 的凸域全弱 H² 均值逼近直接用于物理域，仅拉回有限维仿射校正。原状态与残差始终留在物理域。最终结论及量词不变，原稿文件未修改。

`PhysicalBoxTraceBounds` 从实际 `2/ℓᵢ, 2ℓᵢ` 平方迹界证明

`√ℓᵢ ||Trᵢ w|| ≤ 2(||w||+ℓᵢ||∇w||) ≤ 2κ(||w||+h||∇w||)`。

T080 的面雅可比给 `√Jvol||Tr_ref p̂||=√ℓᵢ||Tr_phys p||`。真实迹线性与原 w 零迹给 `Tr_phys p=−Tr_phys(w−p)`。对所选面的有限乘积 max 范数统一取上界，不增加依赖面集合的常数，得到

`√Jvol ||selectedTrace_ref p̂|| ≤ 2κ E_h(w−p)`。

`PhysicalBoxBoundaryCorrection` 使用 T078 对全部面集合统一的参考域常数 K，拉回 p、校正为 q̂，再通过真正的仿射线性等价逆映回 q。闭面处处零严格保留，T080 给

`E_h(p−q) ≤ κ√Jvol K||selectedTrace_ref p̂|| ≤ 2κ²K E_h(w−p)`。

真实 jet 的线性性和加权三角不等式给 `E_h(w−q)≤A E_h(w−p)`，其中 `A=1+2κ²K` 仅依赖 n、κ。

`PhysicalBoxH2Affine` 从真正盒图和欧氏范数给直径 D=nκh；κ≥1、n≥1 保证 h≤D。将真实盒子的开放、凸、有界和正体积内部供应给 T074，得到

`E_h(u−p)≤B h²||field₂u||`，`B=(2^n+1)n(nκ)²`。

`PhysicalBoxBoundaryAffine` 先选 A 和 B，再取 C=AB；其后才量化全部盒、h、面集合和原状态，得到物理 h² 结论与实际仿射/残差接口。`BoundaryAffineLemma` 用 ℓ=b−a 精确改写为任意端点 a,b 的原文接口。不存在依赖某个盒子后才选的 C，也没有用全 H² 范数替代齐次 Hessian 半范数。

## 角点及边界模式

`AffineCornerKernel` 对实际单位闭面的两个顶点比较，证明消失仿射多项式的所有切向导数为零。若另有不同坐标法向的第二面，剩余法向导数也为零，继而常数项为零。通过实际仿射拉回等价得到物理盒上两非平行面的仿射核为零。`physicalBox_h2_corner_bound` 将 J 取为这两面，严格将最终 q 化为0，得到原函数本身的 `||u||+h||∇u||≤Ch²||D²u||`。两面可分别为任意上下侧；一维下不存在不同法向，基础 B.1 仍覆盖一维。

本批不声称 B.2、原矩重构全局加权逼近、H¹₀ 到局部物理面零迹接口或 Proposition 6.2 已完成。这些是后续应用义务，不是 B.1 本身显式零迹假设之外新增的前提。
