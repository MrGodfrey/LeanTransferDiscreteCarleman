# T143：真实有限半空间边界图册、盒域解析数据及完整辅助估计

本阶段将已验收的实际盒域全局 H² 正则性与此前已验收的原 Dirichlet 允许权估计连接，构造真实边界 Lipschitz 图册，并将全部原 Section 3 辅助估计用于实际盒域。仍申请 AUXILIARY 验收，因为原 Corollary A.2 还包括一般凸多面体，未把盒子子情形标作整个 P023。

`box_dirichlet_graph_estimate` 对实际原形式算子的全部域元素，证明原 canonical `domainSobolevJet` 的完整 H² 范数受实际算子值的 L² 范数控制。常数在所有域状态之前严格为正，取 max(1,K)。证明从实际算子图得到原 H¹₀ 弱解，将 T141 的同一解 H² 提升通过真实弱导数唯一性识别为该 canonical jet；没有任意选择替代域状态或算子值。

`box_analytic_data_uniform` 联合实际 H² 图范数界与完整 `Section3.AllowedFamily`。hD 由真实盒域定理内部给定；形式和算子正是 `boundedDirichletOriginalForm`，原 H¹₀ 测试闭包、真实梯度形式、完整原变分算子域保持。Creg、C、Ccomm 在所有 TimeWeight 和任意 τStar 之前选定，AllowedFamily 包括所有允许指数与两种空间权符号的原域保持、反权域保持、原交换子界、原形式上下界。没有留下 H² 嵌入、正则估计、交换子或加权强制性的输入。

`box_analytic_realization` 直接接受原光滑空间函数 f，利用固定盒的紧闭包内部构造真实有界可测 SpatialProfile，明确其 value=f。它保留全部原对象、统一常数和完整允许权族。形式的闭性、稠密性、对称有界强制性来自既有真实构造；本批未把它们换成抽象未构造的假设。最终结论不需要时间周期、网格或状态约束，故原时间统一性保留。

`DirectionalCoordinates` 从任意非零真实 Euclidean 向量内部选择非零坐标，构造可逆线性剪切，使该方向成为图册竖直单位方向。其变换和逆变换是实际公式，不是假设存在的图册。`FiniteHalfspaceCharts` 对有限严格线性不等式定义的开域和真实严格内点，构造每个边界点的完整 Lipschitz 图册：闭包上的每个不等式仍非严格成立，至少一个活跃面；从边界指向内点的方向使全部活跃面内积严格为正。图函数为活跃面线性函数的实际有限最大值，Lipschitz 常数由有限算子范数上界给出。非活跃面在实际开邻域保持严格，故得到真实局部集合等价，含任意多个面交会的棱和角点。只在有限半空间和严格内点的明确几何假设下使用该结论，不把它冒充凸域 H² 正则性。

`BoxLipschitzDomain` 用每坐标上下两条实际线性不等式及真实中点，将任意正边长盒接到上述图册构造。最终 `openCoordinateBox_bounded_lipschitz` 不接受外部图册或光滑边界前提。`BoxAuxiliaryEstimates.box_section3` 用这些实际几何、canonical H² 正则和真实允许权数据，返回完整 Section 3 的 Conclusions 与全部所需 AllowedFamily，二者在同一原形式算子上。所有常数和阈值先于原任意网格、周期、两种时间方向、空间权符号和状态；原 primitive、Euler、frozen、temporal 估计及形式上下界保持。Conclusions 中引用的 AllowedFamily 由同时返回的全体权族供应，不留给调用者证明。

五模块11声明，最终定向3580 jobs、全库3972 jobs、7310声明递归公理审计通过。固定raw为2235148bytes，SHA256 `cf8df18c5505c03754f5f85457e249b9ba50b770ed654766f054c7afb21fd02a`。依赖T141/C157、T071/C087的实际 `DirichletAllowedData`（声明版本 `d65579460032f15bcba3c77709ccfd3f1642b8fc`）及此前完整 Section 3 和真实图册接口；原稿未修改。P023的一般凸多面体 H² 和 P024 连续CE仍未完成。本批不把第3节辅助连续估计称为第A节连续Carleman估计。
