# T043：实际节点内缩的强 H¹ 收敛

四模块18声明，AUXILIARY；对应原 Section6 的真实 conforming 节点函数进入 H¹₀ 闭包的准备。这里只清偿内缩 H¹ 极限；光滑卷积 H¹ 极限及最终 H¹₀ 成员仍待，原文12/26。

## 强 L² 极限和真实图拓扑

`LpDominatedLimit` 对任意 normed additive group 值的实际 Lp E 2，证明差范数平方等于实际代表差的平方积分。使用真实 Lp 范数定义、有限指数积分公式、sqrt 和 a.e. 代表相减身份，不依赖目标空间另有内积结构，因此适用于真实 fderiv 的 CLM 值空间。

由实际平方差的积分支配收敛推出强 L² 收敛，再给共同有限测度支撑、统一范数界的具体版本。支配函数是 K 的 indicator 乘 (2B)²，可积性由 K 可测且有限测度证明。a.e. 点态极限、各函数和极限的共同支撑／范数界是这个通用引理的公开输入。

`CompactLipschitzLimit` 用实际 scalarZeroFiber 和 derivativeOneFiber 的连续 Lp 映射证明 firstOrderFields 的收敛。对真实紧支 Lipschitz f_n 和 g，若支撑共同位于紧 K、函数和 Lipschitz 常数统一有界、f_n 逐点趋于 g、真实 fderiv 几乎处处趋于真实 fderiv g，则分别构造标量和 CLM 值强 L² 极限，进入真实 H¹ jet 的乘积图拓扑。所有 n 的代表等式在同一个 a.e. 集上使用。没有用仅标量 L² 收敛冒充 H¹。

## 实际内缩序列与局部仿射导数

`ContractionSequence` 取明确 r_n=(1+n)/(2+n)，证明 0<r_n<1、r_n≥1/2、r_n⁻¹≤2、r_n→1。实际逆同胚点 a+r_n⁻¹(x−a)→x；连续原函数因此逐点回到自身。

若原函数在 x 邻域内具有同一个实际 Fréchet 导数 A，逆像点最终在该邻域内，真实内缩链式导数精确为 r_n⁻¹ A，故导数趋于原 fderiv。节点函数在每个真实单纯形内部是同一个仿射函数，在 closure S 外局部为零。全部有限单元的 frontier 为零测，故这两种情形覆盖 volume-a.e. x，得实际内缩 fderiv 的 a.e. 收敛；没有从一般 Lipschitz 的可微性推断导数连续。

## 实际节点 H¹ 极限

`NodalContractionLimit` 先由有限真实单元覆盖给 closure S 紧性。既有 compactLipschitzSobolevJet 和原 nodalGlobalSobolevJet 的标量 value 相同，完整弱导数唯一性给两个实际 jet 精确相等。

最后对开凸 S、真实有限分区的 FaceMatching/BoundaryFitted、边界顶点值零和 a∈S，内缩支撑均在 closure S 内；原连续紧支节点函数给全局标量界 B，所有复合保留 B。Lipschitz 常数是 C r_n⁻¹≤2C，其中 C 为该实际节点函数已有的有限局部导数和。它可依赖网格和节点值，只用于成员／极限，不是原数值估计的统一逆界。

通用强 H¹ 极限定理的全部前提由上述真实几何、函数与导数结果内部供应，最终 `nodal_inward_tendsto_H1` 的结论是实际 `nodalContractedSobolevJet` 在完整弱 H¹ 图拓扑中趋于原实际 `nodalGlobalSobolevJet`。没有输入目标 H¹ 极限或 H¹₀ 成员。a∈S 的非空前提仅用于当前内缩路线；最终全域成员仍需单独处理空域零函数。

尚需把每个紧含于 S 的内缩函数用真正 C_c∞(S) 在 H¹ 中逼近，再用 H¹₀ 闭性传回原函数。H² 正则性、点值代表、具体数值误差和连续热 CE 也仍待，不提升完整原文覆盖。
