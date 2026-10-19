# T114：原弱 Hessian 的真实局部卷积与节点误差界

本阶段把 T112/T113 的光滑局部节点估计接到原全部弱 H² jet 的实际光滑化。对应原 P1 Step 2 的局部插值分析；尚未定义原弱状态本身的连续节点代表，也未完成边界极限或全局允许权逼近。

`tensorCoordinateBound d k` 是实际固定张量坐标重构连续线性映射的范数加一。对任意实际 k 阶 Fréchet 张量，算子范数平方不超过该常数平方乘全部有序坐标分量的平方和。常数仅依赖 d、k，和网格、单元、状态及卷积核无关；不使用随网格改变的有限维范数等价。

`SpatialTest.directionalKernel` 是实际 Dκ·e，证明其光滑、紧支撑，且支撑包含于原 κ 支撑。两个局部弱导数身份 u→v→z 通过真实局部分部积分，识别 `D(D(u*κ)·e₁)·e₀ = z*κ`。实际 Fréchet 导数求值和二阶张量身份进一步给 `iteratedFDeriv ℝ 2 (u*κ) x ![e₀,e₁] = z*κ x`。要求反射核整个支撑保持在原 S；不把零延拓跨边界后的分布导数当作原弱导数。

`mollified_hessian_energy_le` 在任意可测 K 上同时证明实际 Hessian 算子范数平方的可积性和积分界。实际坐标身份、有限求和、原非负单位质量核的 L² 收缩给

`∫K ‖D²(u*κ)‖² ≤ C(d,2)² ∑(i,j) ‖zᵢⱼ‖²`。

`WeakSobolevJet.mollified_hessian_energy_le` 直接输入原 `WeakSobolevJet d 2 (volume.restrict S) S`，取真实标量值、第一和第二弱分量的 L² 零延拓。全部局部弱链由原 jet 自动供应，零延拓范数严格保持；每个对称 Hessian 分量由真实 field₂ 范数控制，有序坐标总数 d²。因此上界为 `C(d,2)² d² ‖field₂ u‖²`。未假定状态具有点态二阶导数，也未增加全空间 Sobolev 延拓假设。

最后两项声明对所有这种实际光滑化在真实闭单纯形上给节点值平方误差 `≤16 C(d,2)² d² D⁴ ‖field₂u‖²`，以及实际完整梯度平方误差 `≤(2^d d+128γ²‖derivativeOneFiber‖²) C(d,2)² d² D² ‖field₂u‖²`。梯度界保持真实内球和 D≤γr，d≤3，核非负、单位积分与实际支撑可容纳条件。常数对核及其半径统一；此支撑条件只说明本批为内部光滑化步骤，不宣称已处理接触原边界的单元。

四模块11显式声明，定向3287 jobs、全库3841 jobs通过，6601项递归公理审计通过。固定原始产物 `/tmp/carleman-weak-hessian-local-axioms.txt` 为1968611 bytes，SHA256 `685940ff51ac8f8723fd3181bc33f3eede6e7373933c7394bb07f007d26cb16e`。AUXILIARY，原文14/26；P011仍待全弱状态的节点代表、边界适配及全局加权组合，原论文未修改。
