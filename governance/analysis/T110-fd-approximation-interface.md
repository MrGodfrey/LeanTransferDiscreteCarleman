# T110：原 B.2 逼近接口与真实 FD 数值数据组装

本阶段将已独立验收的原全 H²∩H¹₀、全允许权 B.2 估计接到同一实际 Reconstruction 的 N3 接口，误差尺度保持 a_E=Ch、a₀=Ch²。

`cartesian_heat_error_from_b2` 是实际弱 H¹/H² jet 上的范数推导：由 `‖σe‖+h‖σ∇e‖≤Ch²‖σD²u‖` 和 hq≤1，先以原 parameterNorm 控制完整加权 H¹ 范数，再将不等式乘 h，利用 hq‖σe‖≤‖σe‖ 得到 Nσ(e)≤Ch Rσ(u)。最高阶加权 Hessian 范数是原 H² parameterNorm 的一个真实非负分量，因此值误差也满足 Ch² Rσ(u)。没有把 H¹ 范数替换成单独零阶界，没有丢掉原 q 因子。

`cartesian_weightedApproximation_interface` 固定正维数、原开凸紧闭包域、轮廓 C¹ 和 κ≥1 后先选统一 C，再量化全部正可比矩形网格、h、任意 D≤H² 且 D≤H¹₀ 的原 L² 子空间、时间网格/周期、允许权、τ 和两符号。唯一小量条件 hq_max≤1 供应全部时刻的 hq(t)≤1。

证明对每个 v∈D 使用真实 domainSobolevJet，T097 的实际 Q_h 误差 jet 经弱导数唯一性严格等于接口中的 inclusion(v)−R_hJ_hv 的域 jet；此前 `cartesianReconstruction_QH` 确认正是同一实际 Q_h。随后将范数推导分别装入 `WeightedApproximation.energy` 和 `.l2`，得到原尺度。

D 的包含前提在结论中保持显式：这是一个对任意 H² Dirichlet 子空间都成立的数值逼近定理。用于真正 Dirichlet 算子定义域时，必须代入原 A1 的 D(A)≤H² 和已构造原闭形式的 D(A)≤V。本阶段不声称已经独立证明具体算子的 H² 正则性；也没有把这一前提隐藏在无解释的数值稳定性假设中。

`cartesianErrorScales` 精确取 a_E=Capp h、a₀=Capp h²、η_A=0，并内部证明三者非负。`cartesian_numericalData` 在同一个原 Dirichlet 闭形式、真实物理 Laplacian、重构、载荷和控制 Hilbert 伴随上构造 `Section5.NumericalData`，所有数值字段均由此前实际证明供应，不以数值稳定性或目标误差界作输入。原 A1 的 D(A)≤H² 作为唯一连续定义域正则性前提显式保留。

先于全部网格、时间网格、周期和允许时间权统一选取 ε、Ctime、Csuper、Capp、Cnum。ε 取测试阈值与观察空间阈值的较小者；q≥1 和 hq_max≤ε 内部推出观察所需 h≤h₀ 及全部时刻 hq(t)≤1。原两符号通过 scaled 轮廓与 signed 轮廓的精确身份进入 test 和 approximation。Cnum=Cmass+Cobs² 同时支配重构双向平方界、实际 lift 界与观察平方界，所有乘方和扩大常数使用真实非负量。

该数据对象中的 A、R/J、Γ/lift、B*、状态/载荷/控制 seminorm 都在结论类型中明确指定为同一原实际构造；刚度缺陷严格为零。测试字段使用已证同一实际测试对象的存在定理作选择，不添加待证测试假设。原 N1/N4 额外的自伴、非负、严格正和范数等价已在 T107/T109 单独证明；当前精简 NumericalData 仅存储转移估计实际使用的字段，不能据此忽略原命题其他要求。

两模块4项声明，定向3781 jobs、全库3832 jobs通过，6554项递归公理审计通过。固定产物 `/tmp/carleman-fd-approximation-interface-local-axioms.txt` 为1943313 bytes，SHA256 `945d9f7e41bd4661019239c792278154555daca6022e6308ffe5f619308a995c`。

范围 AUXILIARY，原文保持14/26。数值数据已在原 A1 定义域包含前提下统一组装；具体 Dirichlet 算子 H² 正则性及完整 PAPER FD 的完成边界继续单独记录，P012不提前提升。固定提交独立验收与远端证据另记台账。
