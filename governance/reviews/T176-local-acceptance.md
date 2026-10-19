# T176 / C192 独立本机验收：原时空平均势与同一 L∞ 界

- checked_sha / source_sha: `ef4e3f83320e3a2d4cc7a074a1df996c13bd9d52`
- mathematical_base: `7c2ceacf62d42b168879106b8c6d6fc246c45794`
- reviewed_at: `2026-10-19T14:24:10+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_section3`
- result / axiom_check: **PASS / PASS**；全部 **25/25** 显式声明通过。
- scope: **AUXILIARY**；C192 可登记 REVIEWED，原文覆盖保持 **17/26**。不声称平均强收敛、控制支持、控制收敛或极限 PDE 已完成。

## 固定版本与原文

独立读取固定 Git 对象的三个新模块全部实际证明、25 项完整展开类型及公理、T176 分析和 MATH_SPEC，并核对实际积分、时间网格、对偶单元及原物理乘子依赖。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES/PAPER_COVERAGE 及 pin/CI 脚本与基线逐字节相同，沿用已读协议。后续时间重构、紧性模块及动态根导入/公理输出未纳入本次验收。

原文对照 `paper/main.tex:2292–2314` 的原实值 `b∈L∞(Q)`、`eq:conv-data-fe` 时间平均、`eq:conv-dual-cells` 对偶开盒及 `eq:conv-data-fd` 时空平均。时间重构和控制支持见紧随后续段落，完整收敛命题见 2345 行起，均不属于本次结论。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

签发前实际读取已冻结 [T175 报告](T175-local-acceptance.md)：checked SHA 为本次数学基线，report commit=`8a921065b09fe7082c4ef5d1163e9925f3f98709`，reviewed_at=`2026-10-19T14:17:27+00:00`，21/21 PASS。其真实对偶单元/质量身份是本次实际依赖；没有把主执行者口头 PASS 当作正式前置验收。

## 25 项声明清单

顺序与固定 manifest、C192 一致。A=`Spatial/BoundedMultiplierAverage.lean`，T=`Control/TimeCellAverage.lean`，C=`Control/CartesianAveragedPotential.lean`；文件均位于 Carleman 下，raw 行指固定完整类型的起始行。共 6 个定义、1 个实例、18 个定理。

| 序号 | 完整声明 | 源码 / raw 行 | 实际内容与判定 |
| --- | --- | --- | --- |
| 1 | `Carleman.BoundedMultiplier.ofMeasureLE` | A:14 / 33932 | 真实测度支配下保持值、a.e. 可测与同一界。PASS。 |
| 2 | `Carleman.BoundedMultiplier.ofMeasureLE_bound` | A:22 / 33937 | 限制后 bound 原样相等。PASS。 |
| 3 | `Carleman.BoundedMultiplier.integrable` | A:25 / 33941 | 有限测度上的原 a.e. 有界实函数真正 Bochner 可积。PASS。 |
| 4 | `Carleman.BoundedMultiplier.averageFirst` | A:29 / 33944 | 实际归一化第一变量积分，有限 μ、SFinite ν、正真实质量。PASS。 |
| 5 | `Carleman.BoundedMultiplier.averageFirst_bound` | A:47 / 33955 | 平均的 bound 与原 bound 相等。PASS。 |
| 6 | `Carleman.BoundedMultiplier.averageFirst_congr` | A:51 / 33961 | 乘积 a.e. 相等推出平均后 ν-a.e. 相等。PASS。 |
| 7 | `Carleman.BoundedMultiplier.setAverage_bound` | A:59 / 33967 | 真实集合平均绝对值不超过原界，正确消去正质量。PASS。 |
| 8 | `Carleman.BoundedMultiplier.averageFirst_setIntegral` | A:72 / 33971 | 有限乘积测度上的实际 Fubini 换序和归一化公式。PASS。 |
| 9 | `Carleman.TimeGrid.physicalTimeCell` | T:14 / 33977 | 原后向 Euler 的 `(t_i,t_i+dt]`。PASS。 |
| 10 | `Carleman.TimeGrid.physicalTimeCell_finite` | T:17 / 33979 | 实际时间单元限制测度有限。PASS。 |
| 11 | `Carleman.TimeGrid.physicalTimeCell_subset` | T:22 / 33982 | 每单元真实包含于 `(0,T]`，含最后单元。PASS。 |
| 12 | `Carleman.TimeGrid.physicalTimeCell_volume` | T:29 / 33985 | 实际 Lebesgue 长度恰为 dt。PASS。 |
| 13 | `Carleman.TimeGrid.physicalTimeCell_restrict_le` | T:34 / 33988 | 单元限制测度小于原时间区间限制测度。PASS。 |
| 14 | `Carleman.timeCellPotential` | T:42 / 33991 | 对原时空势限制并作真实时间平均，输出空间乘子。PASS。 |
| 15 | `Carleman.timeCellPotential_value` | T:49 / 33999 | 所选代表值精确等于 `dt⁻¹∫cell b(t,x)dt`。PASS。 |
| 16 | `Carleman.timeCellPotential_bound` | T:53 / 34004 | 同一时间平均界。PASS。 |
| 17 | `Carleman.timeCellPotential_congr` | T:59 / 34009 | 原时空代表改变只改变空间零测集上的平均值。PASS。 |
| 18 | `Carleman.timeCellPotential_setIntegral` | T:66 / 34015 | 时间平均的空间集合积分等于原时空双积分。PASS。 |
| 19 | `Carleman.cartesianAveragedPotential` | C:16 / 34022 | 真实内部对偶单元的空间平均。PASS。 |
| 20 | `Carleman.cartesianAveragedPotential_formula` | C:20 / 34031 | 精确 `(dt*∏δ)⁻¹∫time∫D b`，真实消去域限制。PASS。 |
| 21 | `Carleman.cartesianAveragedPotential_bound` | C:30 / 34044 | 每一实际节点的绝对值≤同一个 b.bound。PASS。 |
| 22 | `Carleman.cartesianAveragedPotentialMultiplier` | C:37 / 34054 | 实际计数测度上的节点乘子，bound 未扩大。PASS。 |
| 23 | `Carleman.cartesianAveragedPotential_congr` | C:42 / 34064 | 原时空 a.e. 等式给每时段、每节点系数严格相等。PASS。 |
| 24 | `Carleman.cartesianAveragedPotential_operator_norm` | C:50 / 34075 | 原物理质量 Hilbert 空间中实际乘法算子范数≤b.bound。PASS。 |
| 25 | `Carleman.cartesianAveragedPotential_operator_symmetric` | C:56 / 34084 | 同一真实实值节点乘子的物理内积对称性。PASS。 |

## 实际积分、代表和归一化

BoundedMultiplier 存储实值代表、AEStronglyMeasurable、非负 bound 和 a.e. 绝对值界；不要求连续或处处有界。它表达原 L∞ 数据的代表及界，congr 定理负责代表无关性。`ofMeasureLE` 沿真实测度不等式同时传递可测性与 a.e. 界，而非直接将不同测度的 a.e. 前提混用。

在有限 μ 上，integrable 用可积常数 bound 和真实 a.e. 可测性证明 b 可积。averageFirst 的 μ 有限、ν 为 SFinite；利用保测 swap 和 `ae_ae_of_ae_prod` 得到 ν-a.e. 的 μ-a.e. 切片界。实际积分范数≤bound·μ.real(univ)，用 hvol 和 mass>0 除回去，故保留完全相同的界。没有假定每个切片都可测/有界；时间平均值公式是选定代表的 Bochner 积分定义，平均的有效空间对象及其界都是 a.e. 陈述。异常切片不被当作原 L∞ 类的节点取值。

平均的 a.e. 可测性来自实际 `AEStronglyMeasurable.integral_prod_right'`。独立读取固定 mathlib 中该引理、`norm_integral_le_of_norm_le_const` 和 `integral_integral_swap` 的真实类型与实现；没有以一个名字替代 Fubini 的可积性前提。换序定理明确增加 ν 有限：此时 b 在 μ×ν 上可积，限制 ν 到 K 后仍可积，再应用真正的 Bochner Fubini。一般 averageFirst 仅需 ν SFinite；没有错误声称无限空间测度上 b 必然全局可积。

`averageFirst_congr` 先对原乘积 a.e. 等式换序，得到 a.e. 切片的积分相等；时间单元 congr 先使用真实限制测度不等式。Cartesian congr 再在每个对偶单元限制这个空间 a.e. 等式并取积分，因而得到所有实际节点的严格系数相等。并未把时间平均的 a.e. 相等升级为逐空间点相等。即便两个输入携带不同合法 bound，只要代表 a.e. 相同，实际离散系数仍相同。

## 原时间单元、对偶单元和物理算子

实际 nodeTime i=i·dt、T=steps·dt；physicalTimeCell i 为 `(i·dt,(i+1)·dt]`，论文 n=i+1。最后单元终点是 T，不是周期 next 对应的 0。dt>0 来自 TimeGrid；包含与长度证明使用 i<steps 和真实 Lebesgue Ioc 公式。输入测度 `(volume|(0,T])×ν` 与原开柱在时间端点上仅差零测集。没有要求势 b 周期、光滑或在 t=0/T 取相同值；所有原 N≥2 时间网格都包含，N=1 也合法。

Cartesian 平均先在 `ν=volume|Ω` 下取时间平均，再在真实 `D_a` 上积分。已重新读取 T175 的实际开盒定义、包含与体积证明：每个内部对偶单元完全在原 Ω 内，Lebesgue 体积精确等于 `mass=∏δ_j>0`。因此 `restrict_restrict` 和 `D_a∩Ω=D_a` 合法地消去域限制，得到原文双积分公式；时间长度 dt 与物理质量 mass 的倒数方向正确。没有假定这些内部单元覆盖整个 Ω，也没有用边界条带上的数据补齐平均。

`setAverage_bound` 对该真实质量给每节点系数绝对值≤b.bound。若原数据界 b.bound≤M，则平均后的空间界和所有节点界均≤同一 M；全过程不除以 M，故 M=0 无遗漏。所有常数均为 1，没有 T、dt、维数、网格基数或长宽比因子。空内部节点时点态结论真空成立、零维物理空间算子界合法；d=0 时，空间空积质量为 1，与同一测度/物理空间定义一致，不需要额外排除。

最后两项使用真实 `PhysicalFiniteSpace` 的内积 `mass*Σ_a f_a g_a`，mass 正是 ∏δ_j。其 multiplier 逐值为 b_a f_a；对称性由实数乘法和原质量内积直接证明。算子范数界通过此前的精确 `sqrt(mass)` 计数 L² 等距及点态界得到，不把默认 sup 范数或任意有限维范数等价冒充物理范数。cartesianAveragedPotentialMultiplier 存储的也是同一节点平均，并非另选的有界代理函数。

本批清偿原 FE 时间平均和 FD 时空平均势的数据公式及同一界。强收敛、活动区控制支持、重构控制弱紧性、终态极限和连续弱方程仍需后续证明；单纯的平均界不被当作这些结论。

## 依赖、构建与递归公理

从三模块解析实际 Carleman 导入闭包，共 331 个模块；328 个旧模块与数学基线逐文件相同。额外比较已接受版本整个闭包：CartesianCellReconstruction/C191 的 326 个模块与 `7c2ceacf62d42b168879106b8c6d6fc246c45794` 相同；PhysicalFiniteWeights/C184 的 44 个模块与 [T168](T168-local-acceptance.md) 的 `30a03e32af45ef82baacbbfe6917cd7ceff234f3` 相同。BoundedMultiplier、时间网格和实际物理乘子定义已独立读取，未仅依赖旧报告结论。

固定根导入含全部三个新模块，25 个声明逐项有 #check 和 #print axioms，顺序与 manifest 一致。末尾审计实际遍历全部 Carleman 常量（含 privateToUserName 还原后的私有声明）并 collectAxioms；raw 末行为 `Axiom audit passed for all 8229 Carleman declarations.`。独立解析 3133 项显式公理记录和 9 项无公理记录，无白名单外依赖；全部 25 项只依赖 `propext, Classical.choice, Quot.sound`。新增源码无 sorry/admit/axiom/native_decide。

实际成功定向日志为 `/tmp/carleman-t176-cartesian-averages-target8.log`，3522 jobs；固定 `-build.log` 为根目标 4115 jobs。较早失败的草稿日志不作为当前证据，最终固定源码和远端根构建均成功。`-axioms.log` 是空 stderr，审计结论来自完整 raw。Lean pin v4.35.0，CI compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 及本机干净依赖 HEAD=`56a005855ea17e0b0958f73ec801ae140b0a1679`。固定 CI 使用精确 github.sha、根构建及全声明递归审计。

## 独立远端 CI 与原始工件

本 Agent 自行访问 GitHub run/jobs/artifacts API，并分别执行两次 gh run download，均 exit 0；没有使用主执行者的 root 下载副本代替独立证据。

- run: [39267989909 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39267989909/attempts/1)，event=push，branch=main，head_sha 为本报告精确 SHA；最终 completed/success，updated_at=`2026-10-19T14:23:27Z`。
- 三个实际 jobs：state-check **118112506643**、lean **118112507064**、dashboard / snapshot **118114167012**；全部 completed/success。Lean proof build、结果记录和两次上传均 success。
- `lean-ci-result` artifact **12194460239**，ZIP 493 bytes，API digest `sha256:0f13cc78ffcdada9e9f38af0ce7e5ca973a3649c4c52cf8f8e586ee66249ad5b`。
- `lean-declaration-evidence` artifact **12194385406**，ZIP 240890 bytes，API digest `sha256:510d1ac27fa8b96cf9e4020af1a37d7fe3b8e265ab59206ad0213874e3824443`。

两工件的 workflow_run 均绑定上述 main、精确 SHA 和同次 run。独立下载目录是 `/tmp/carleman-t176-averaged-potentials-main-ci` 和 `/tmp/carleman-t176-averaged-potentials-main-axioms`。实际 result.json 为 537 bytes，SHA256 `c9bea77f4260bdf53522add1c3d778b389534db9f2fe3bf5ee5e161b12815ecd`，status=PASS、checked_sha=source_head_sha=`ef4e3f83320e3a2d4cc7a074a1df996c13bd9d52`、targets=[Carleman]、finished_at=`2026-10-19T14:22:07.653916+00:00`，ci_url、工具链与上述记录一致。

解包 axioms.txt 与固定 `/tmp/carleman-t176-averaged-potentials-local-axioms.txt` 独立逐字节比较完全相同：**2609955 bytes**，SHA256 **`3b48978b3750e4d968d4e97de3ea4400558e92a2c7424cfd829a22d5d6d2b2ec`**。完整类型、公理集合及最终 8229 项成功记录均实际读取；ZIP digest 和 raw digest 分别记录。

## 最终结论

**25/25 PASS，未发现阻断缺陷。** 原时间平均、实际时空对偶单元平均、代表无关性、同一 L∞ 界及真实物理乘子范数/对称性已经证明。C192 可登记 REVIEWED/AUXILIARY，原文覆盖保持 **17/26**。本报告单文件提交，不 push、不改数学、原稿或台账；通知后正文及 reviewed_at 冻结。
