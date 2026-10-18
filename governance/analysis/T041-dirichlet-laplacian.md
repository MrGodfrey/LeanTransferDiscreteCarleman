# T041：Dirichlet 形式算子的实际负 Laplacian

四模块20声明，AUXILIARY，服务于原 Section6 的 Dirichlet Laplacian 实现。原稿不变，不提升原文12/26覆盖。

## 梯度配对与实际二阶字段

`GradientPairing` 证明真实 Euclidean L² 字段内积等于全部 Sym 分量的 L² 内积之和，积分和有限求和的交换由每个 L² 配对可积证明。一阶通过 Sym.oneEquiv 精确转为每个 Fin d 坐标出现一次。weakGradientPairing 是实际 field 1 的 L² 内积所构造的连续双线性映射。

`WeakLaplacian` 以实际二阶弱 Sobolev jet 的各纯二阶分量定义 `negativeLaplacian u = -Σi Dii u`，是实际连续线性映射。完整 jet 的 k=1 分布身份给 `⟨Di u,Di φ⟩=-⟨Dii u,φ⟩`；对所有坐标求和得到准确 Green 恒等式。φ 的实际一阶字段已精确识别，未将目标积分分部作为假设。

两边均为 H¹ jet 中测试变量的连续线性配对；测试 span 中每个元素都是实际紧支光滑测试，闭包最小性因此把 Green 恒等式传到全部真实 H¹₀ jet。不假设额外边界光滑性、H² 正则性结论或有限元测试族。

## H²∩H¹₀ 进入实际算子域

`DirichletLaplacian` 对实际 H² jet 且 value 属于真实 dirichletSubspace 的 u，用准确的一阶截断构造原 DirichletEnergy 中的元素。其 value 不变，梯度也是同一个实际一阶字段。Green 恒等式供应完整变分配对，因此通过原 model.domainElement 构造真实形式算子域元素；value 精确等于原 u，operator 精确等于上面实际纯二阶和的负值。

最终得到标量子空间包含 `H²(S)∩H¹₀(S) ≤ D(A)`。S 是任意正维有界开集，形式是此前实际构造的 boundedDirichletOriginalForm，不是额外给定满足目标配对的任意算子。反向 H² 正则性及域等式不在结论中。

## 完整分布图的等价刻画

`DirichletDistribution` 定义 IsWeakNegativeLaplacian u f 为对全部原 SpatialTest S 的实际梯度配对等式，即真实分布意义的 `-div(∇u)=f`。测试空间没有缩小。证明该条件与对所有 H¹₀ 测试的等式等价：正向用连续闭包，反向使用每个紧支光滑测试的已证闭包成员。

`dirichlet_operator_graph_iff` 在任意标量 L² 的 x、f 上双向刻画原完整形式算子图：存在实际域元素 z 其 value=x 且 A z=f，当且仅当存在真实 H¹₀ jet u，value=x，且上述完整分布测试身份成立。由原 operator_isAssociated 和实际 jet/energy 互换证明两向，未额外施加 H²、有限维、谱截断或边界正规性条件。H² 情形内部证明其 f 就是实际 -ΣDii。

## 剩余义务

这实现了全变分算子的分布意义，并证明 H²∩H¹₀ 的一个方向；不能据此宣称一般有界开集的域等于 H²∩H¹₀。原凸多面体的反向 H² 椭圆正则性及其统一估计仍待。节点 H¹₀ 逼近、H² 连续代表、具体网格/局部数值估计和连续热 CE 同样未完成，完整 Proposition 6.1 及观测控制覆盖不升级。
