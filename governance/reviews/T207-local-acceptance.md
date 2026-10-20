# T207 / C223 独立本机验收

- checked_sha: `fefa061545a3eaad908531f9a9b322fbab55707c`
- base_commit: `7b47cb8efa47015a5e2e62f6e2573204bd5c7418`
- reviewed_at: `2026-10-20T04:05:55+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 6/6 显式声明（1 def、5 theorem），无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，P021 不提升**
- evidence_source: **local**；不查询或声称远端 CI 成功。

直接读取固定 Git 对象中的两个新模块、全部展开类型与证明、T207 分析及 MATH_SPEC，并对照原稿 `paper/main.tex:2366–2385` 的状态能量步骤，以及原 ForwardEquation、consistent L² 质量和重构定义。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未变。

## 逐声明核对

以下声明均在 `Carleman` 命名空间；前四项位于 `Control/ConformingDirichletState.lean`，后两项位于 `Control/ConformingStateTimeEnergy.lean`。

| 实际声明 | 结论与核对 |
| --- | --- |
| `Carleman.dirichletGalerkinState` | **PASS**。以实际 `boundedDirichletOriginalForm` 的 `conformingEnergyLift` 构造 X→L H¹₀；X 是原 L² 的任意有限维子空间，唯一空间成员前提为 X≤原 Dirichlet 值子空间。 |
| `Carleman.dirichletGalerkinState_value` | **PASS**。提升的零阶 L² 值恰为同一个 x∈X 的原包含像，没有替换状态或引入独立梯度。 |
| `Carleman.dirichletGalerkinState_stiffness` | **PASS**。对独立 x、y，实际 Galerkin 刚度配对等于两提升的真实弱梯度内积；与原 consistent-mass 刚度一致。 |
| `Carleman.dirichletGalerkinState_norm_sq` | **PASS**。完整 H¹₀ 图范数平方准确等于原 L² 范数平方加刚度二次型，没有丢失零阶或任一梯度分量。 |
| `Carleman.conforming_state_node_uniform` | **PASS**。由原 ForwardEquation、实际势算子界与区域控制收缩，内部推出全部 N+1 个物理节点的范数界 `energyConstant T M·(Y+U)`。 |
| `Carleman.conforming_state_dirichlet_time_uniform` | **PASS**。同一个方程内部供应节点界，再由真实离散能量恒等式与逐节点完整范数身份，得到原后层分片常数重构的实际 L²(0,T;H¹₀) 预算。 |

清单与固定源码、根导入及 `#check @...` / `#print axioms` 一一对应。raw 展开类型分别起于第 38664、38672、38677、38684、38690、38712 行；六项均无隐藏的目标状态界或额外空间正则性输入。

## 数学与量词

**真实空间与刚度。** `OriginalForm.valueEquiv` 由实际弱 Sobolev 值映射的单射、全值域构造；`conformingEnergyLift` 是其逆与 X 包含映射的复合。有限维性只保证这个真实线性提升连续，其可能依赖 X 的算子范数从未进入定量预算。`boundedDirichletOriginalForm` 的 V 就是原 `dirichletSubspace S`，能量空间是原 H¹₀ 闭包的 Sobolev Hilbert 实现，形式是实际一阶弱场的 L² 内积。其 Poincaré 强制性在内部证明；本批没有输入 H² 正则性或任意目标形式识别。真实 `dirichletEnergy_norm_sq` 包含零阶和完整一阶字段，因而刚度身份与完整范数身份均是精确等式。

**原方程、势与控制。** `ForwardEquation` 是对 i∈Fin N 的 `dt⁻¹(y^{i+1}−y^i)+(A+V_i)y^{i+1}=Bu_i`，y 定义在全部 Fin(N+1)，不带周期端点条件。`conformingPotential X b_i` 是乘以原有界实势后正交投影至 X；实际范数≤b_i.bound≤M。`conformingRegionControl X ω` 是原 L²(ω∩S) 控制零延拓后正交投影，其范数≤1由真实零延拓等距与正交投影收缩得到。未把控制范数换成投影后的较小范数；空或零测区域同样合法。

由刚度非负性和势界得到 `〈(A+V_i)x,x〉≥−M‖x‖²`，实际 `forward_energy` 给所有节点的界。该依赖的标量递推使用原物理 N 步控制范数 `sqrt(dt∑‖u_i‖²)`，其常数为 `exp(2MT)(1+sqrt T)`，与空间、网格、算子范数无关。显式保留原 `dt·M≤1/2` 条件；不添加空间网格、逆估计、形状、分级或 h/dt 耦合条件。时间 T 通过 `g.period=T` 固定且自动为正，并未声称此预算对 T 独立。

记 `B=energyConstant T M·(Y+U)`。旧实际能量增量把方程与 `y^{i+1}` 配对，逐步累加得到初终能量差、非负节点增量和 `2dt∑〈Ay^{i+1},y^{i+1}〉`。控制与势的实际 Young 估计给
`2dt∑〈Ay^{i+1},y^{i+1}〉≤Y²+U²+(1+2M)T B²`。
本批调用该恒等式时，所需全部节点界由同一个原方程刚刚推出，没有把该界留作新增假设。另一方面值重构平方范数≤T B²，真实时间胞元内积公式与完整提升范数等式给
`‖Y_h‖²_L²(H¹₀)=dt∑‖y^{i+1}‖²+dt∑〈Ay^{i+1},y^{i+1}〉`。
刚度非负允许把第二项放宽到上述整个右端，故报告中的 `stateTimeEnergyBound` 正是 `sqrt(T B²+Y²+U²+(1+2M)T B²)`。安全放宽只改变数值常数，不改变原所需统一预算。

时间重构是互不相交真实胞元 `(t_i,t_{i+1}]` 上的 Lp 指示函数有限和，测度恰 dt；没有使用任意 Lp 代表的端点值。固定 T 的运输只把同一时间测度域识别为 `(0,T]`，后层 `i.succ` 覆盖原 n=1,…,N。H¹₀ 完备性由原闭包内部供应，得到真实 Bochner L² 元素。

S 开、有界且 d>0 是这里实际 Dirichlet 形式构造的明确前提，原 P1 区域满足这些条件；没有另要求凸性或盒域。X 可取原完整 conforming P1 空间，结论适用于其所有状态。Y、U 只是原初值与控制费用预算；时间定理的非负性条件与其用途一致。结果右侧显式仅含 T、M、Y、U，因此即使 X、S 写在类型参数之前，也不引入隐藏的离散依赖。仅借用 `CartesianStateTimeEnergy` 文件中的通用预算定义，不带入该文件其他定理的 Cartesian 假设。实际控制选择、P1 弱极限方程及整体 P021 不在本批结论内。

## 依赖边界与本地验证

新模块递归 Carleman 源闭包共 **533** 文件，其中 **531** 个旧文件的 Git blob 全部与基线相同。直接重读本批实际调用的 Galerkin 提升/刚度、Dirichlet 形式与范数、区域控制/势、物理能量增量及累积预算、时间重构。另核对以下已接受固定版本的完整源闭包未变：GalerkinStiffness 的 283 模块（`1cf3071913d460625411022e4ea16c8336399bf8`）、ConformingRegionControl 的 54 模块（`31d5e165a595849bc1c882523838aad69576b594`）、DirichletTimeWeakCompactness 的 59 模块（`32711e6669f223eba5851b43e9ec886a40c45b6e`）及 PhysicalStiffnessEnergy 的 7 模块（`69cee61bd440c386c2ac20af6104f72e98b3563c`）。未重审无关历史结果。

独立读取 `/tmp/carleman-t207-local-evidence.json`：`source=local`、`status=PASS`，`checked_sha=source_head_sha` 均为本报告 proof，完成时间 `2026-10-20T04:03:11.240824+00:00`，实际全库构建及公理命令均 exit 0。这里核验实际执行记录与固定源码关联，没有声称审核者重新运行全库。

| 固定本地证据 | 核验结果 |
| --- | --- |
| `/tmp/carleman-t207-target-build.log` | 两目标完成，3753 jobs；185 bytes，SHA256 `0a1df2f47d7610282324837b6ace03a41b8d6618e3844a6aade4517b94f7c47c`。 |
| `/tmp/carleman-t207-build.log` | 根目标完成，4213 jobs；80 bytes，SHA256 `6241236af9a03b1deaf48e22f0245315725ab91aff31eccbf88ed4b8ac32820e`。 |
| `/tmp/carleman-t207-axioms.log` | 0 bytes，stderr 为空。 |
| `/tmp/carleman-t207-conforming-energy-local-axioms.txt` | 2,965,636 bytes，SHA256 `1873b8038d10274721a8fd0f9f6fb60758bc7edfcb5aa9b533fb7b617db2d174`；末行 **8963** 项递归审计 PASS。 |
| `/tmp/carleman-t207-local-source-manifest.txt` | 106,054 bytes，SHA256 `20f7076c660eea8dd82c4187dea9772e40e09bd13def1e56bf93935046787c13`。全部 tracked Lean 与三项工具链配置共 **978** 文件，独立枚举集合精确、无重复，每个字节摘要均匹配 proof Git blob。 |

六项只依赖 `propext`、`Classical.choice`、`Quot.sound`；raw 全部 3501 条显式公理列表及 9 条无公理输出无白名单外项。固定全命名空间审计使用 `privateToUserName` 和 `collectAxioms`，覆盖私有及生成声明。Lean 4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定配置一致；治理协议未变。

**签发：C223 在上述 AUXILIARY 范围 PASS，无修复项。** 冻结正文和时间，仅单独提交本报告，不修改数学、台账或原稿，不 push。
