# T176 / C192：原时空平均势与同一 L∞ 界

三个模块二十五声明，对照原 eq:conv-data-fe、eq:conv-data-fd 的真正平均，而非对 L∞ 类作节点取值。BoundedMultiplierAverage 在有限测度上证明真实积分可积；限制测度保留同一个 bound；对乘积测度的第一个变量作归一化 Bochner 积分，以 Fubini 的 a.e. 切片界和真实测度质量证明平均仍有同一个界。完整的代表无关性从乘积 a.e. 等式推出，不要求所有截面逐点有界。

TimeCellAverage 定义原后向 Euler 的 (t_i,t_i+dt]，证明它在 (0,T] 内且真实长度为 dt。由原时空 BoundedMultiplier 限制到该时间单元后取平均，得到实际空间 BoundedMultiplier；其值正是 dt⁻¹∫ b(t,x)dt，bound 原样保留。实际有限空间测度上的 Fubini 换序得到单元积分与原时间/空间双积分的精确关系。

CartesianAveragedPotential 用原内部对偶单元的真实 Lebesgue 积分，得到 (dt∏δ)⁻¹∫time∫Di b。通过真实包含消去域限制；精确单元体积与时间长度已证明，故每个节点的绝对值≤同一个 b.bound。构造实际计数空间 BoundedMultiplier，并证明对应原物理质量 Hilbert 空间的乘法算子范数≤b.bound且对称。任意几乎处处相同的原时空代表给所有离散系数完全相同；不增加连续势、网格相关界、节点采样或额外一致性假设。

若原 b.bound≤M，则所有离散势保持原 M；各结论包含 M=0 和空内部节点情形。AUXILIARY，原文覆盖17/26；尚不声称平均强收敛、控制支持或极限 PDE。

定向3522 jobs、根目标4115 jobs及8229声明递归公理审计成功。二十五声明根导入，完整类型与公理显式打印；同SHA正式CI和独立验收另行记录。
