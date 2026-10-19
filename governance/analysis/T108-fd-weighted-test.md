# T108：同一原物理 Hilbert 测试的完整 WeightedTest 接口

本阶段将 T101/T102/T104 的同一原平方权对角算子和估计接入 Section 4 实际使用的 `WeightedTest`，保留真实物理 Hilbert 范数、原 R_h 和全部离散状态。

`PhysicalFiniteSpace.multiplierFamily` 是从有限节点系数到实际物理 Hilbert 连续算子的连续线性映射。逐坐标导数经此映射给出真实算子范数导数。有限维连续性只证明对象资格，并未用于网格一致常数估计。

`cartesianPhysicalTest` 逐节点乘原允许权的平方，其导数逐节点乘原 `2σ²(τ q'/q+ηρ q')`。两者节点值与此前真实对角算子严格一致；真实算子导数再给原物理二次配对的时间导数。原 q 的端点匹配传给实际算子，真实内积中对称性、非负性和精确加权能量身份均证明。

`cartesian_weightedTest_interface` 先固定原开凸有界域 S、C² 轮廓、步长可比常数 κ、时间正则常数 β 和指数上界 τStar，再选正 ε≤1、Ctime、Csuper。之后才量化全部正步长和完整矩形网格（物理域恰为 S）、h、周期/时间网格、允许时间权、时间正则性、|τ|≤τStar、两符号和 h q_max≤ε。

所得对象为原 `Section4.WeightedTest`，并在结论中明确给出 op 和 derivative 等于上述实际算子的恒等式。时间界使用已验收 T102 的同一统一常数；h q_max≤ε 内部供应全部时刻的条件。超逼近使用 T104 的真实残差，并由原弱 jet 的值单射性证明其等于接口中 R_h(T_h z)−σ²R_hz 的同一 H¹ 弱 jet；原重构 jet 同样识别为域 Sobolev jet。逆权通过 `scaled (-η)=(scaled η).neg` 精确识别，残差方向、幂次及原 Csuper h q_max 系数不变。没有增加正则状态、节点代表或待证几何条件。

三模块14项显式声明，定向3751 jobs、全库3827 jobs通过；6513项递归公理审计通过。固定产物 `/tmp/carleman-fd-weighted-test-local-axioms.txt` 为1925576 bytes，SHA256 `29f62e38b53d318302863184a77f5478cd4895ecf8756ca9cef8189e3ce66229`。

本阶段仅完成原测试接口，范围 AUXILIARY，原文覆盖仍14/26。FD/P012 仍需同一物理刚度、逼近、质量/载荷和观察数据的统一装配；不提前提升。固定 SHA 独立验收和远端证据另记台账。
