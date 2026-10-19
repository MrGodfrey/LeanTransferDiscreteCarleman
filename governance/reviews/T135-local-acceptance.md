# T135 / C151 / P019 独立 PAPER 验收

- `checked_sha`: `7ad1a9dd94d3abfe384564b1f24f351f5c60fe21`
- `base_commit`: `3d418d76a4959a094dcd26d2d157c213f297531d`
- `reviewed_at`: `2026-10-19T07:49:25+00:00`
- `reviewer`: `/root/accept_spatial_lemma`
- `result`: **PASS**；`axiom_check`: **PASS**。
- `scope`: **PAPER**，完整原 Proposition 7.7 / `prop:filter-p1` / P019。
- 验收决定：C151、P019 可登记为 **REVIEWED / PAPER**；完成数可由14/26增至15/26，仅增加P019。P011、P023及其他未完成项不随之提升。

本 Agent 直接读取固定 Git 对象中的三模块全部证明、八项实际完整类型、原 Proposition 7.7 及其 Section6/7 对象定义、分析/MATH_SPEC/台账和关键依赖，并独立查询同 SHA 三项正式 CI、自行下载原始结果与公理产物。执行者说明、辅助结果标签或 CI 均未替代原命题忠实性审查。后续工作树及动态 `.ci/axioms.txt` 不作为本批依据。

## 全部八项声明

名称省略公共前缀 `Carleman.`，固定路径以 `Carleman/` 为根。列表与 `/tmp/carleman-t135-filter-p1-declarations.json`、modules JSON及固定 C151/T135/P019 精确对应，包含一个实际定义。

| # | 声明 | 固定源码位置 | 独立结论 |
|---|---|---|---|
| 1 | `SimplicialPartition.maxDiameter_pos` | `Spatial/ConformingUniformInverse.lean:13` | PASS；非空域、正维和实际非退化单纯形给真实最大单元直径严格正，不把尺度正性作为最终前提。 |
| 2 | `SimplicialPartition.inverseWeight_const_bound` | `Spatial/ConformingUniformInverse.lean:28` | PASS；真实 a.e. 分区使常尺度逆乘子等于 H⁻¹，从而乘法范数≤H⁻¹‖u‖，没有单元数因子。 |
| 3 | `conforming_uniform_inverse` | `Spatial/ConformingUniformInverse.lean:45` | PASS；所有完整 conforming P1 弱 H¹ 状态的梯度逆估计，由实际内球形状界与粗网格准一致界内部导出，常数仅依赖 d、κ、Q。 |
| 4 | `Physical.filterRayleigh_le_of_energy_bound` | `Control/FilterRayleighBound.lean:11` | PASS；真实 Rayleigh 商的 supremum 由实际能量界控制；非零空间和零空间分别处理。 |
| 5 | `Physical.nestedConformingFilter` | `Control/ConformingFilterRayleigh.lean:15` | PASS；定义为粗空间到细空间的原包含映射实际 range，未替换成任意候选子空间。 |
| 6 | `Physical.dirichlet_galerkin_energy` | `Control/ConformingFilterRayleigh.lean:18` | PASS；实际 Galerkin 刚度与原 L² 质量下的能量严格等于同一状态的真实全梯度平方。 |
| 7 | `Physical.nested_p1_filter_rayleigh` | `Control/ConformingFilterRayleigh.lean:28` | PASS；任意有限维真实 H¹₀ 细子空间包含完整粗 P1 空间时，内部供应全保留状态能量界并取 supremum，得到 C/Hc²。 |
| 8 | `Physical.p1_coarse_filter_rayleigh` | `Control/ConformingFilterRayleigh.lean:60` | PASS；将细空间具体设为完整细 conforming P1 空间，有限维性和 H¹₀ 包含内部供应，完全覆盖原 Proposition7.7。 |

## 与原命题逐项对应

固定 `paper/main.tex:2224–2236` 要求：V_h 为 Proposition6.1 的一致质量 P1 空间；粗网格 conforming、shape-regular、quasi-uniform，最大直径 Hc，且 V_Hc⊆V_h；F=V_Hc；结论 Λ_F≤C Hc⁻²，C 只依赖粗网格规则性界和维数。

原对象在1469–1485行明确为 d=2,3、固定有界凸多面体 Ω、V=H¹₀(Ω)、a(v,w)=∫∇v·∇w，V_h 是**全部** H¹₀ 且逐单元为 P1 的函数，质量为原 L² 内积，A_h 由 (A_hz,w)=a(z,w) 定义。2146–2158行定义实际 Rayleigh supremum、零子空间取0，并明确不要求 A_h 或势保持 F。最终 Lean 声明逐项使用同一对象。

| 原文内容 | 实际形式化对应 | 审查结论 |
|---|---|---|
| 原 Ω 与维数 | S 开、有界、凸、非空，d>0 | 覆盖原非空 d=2,3 凸多面体；证明适用于更广维数，不收窄原域。 |
| 完整粗细 P1 空间 | M/Mh.conformingSpace (dirichletSubspace S) | 成员双向刻画正是原 H¹₀ 与逐单元仿射条件；无节点子空间替换。 |
| 粗形状规则性 | 正 r_i、ball(a_i,r_i)⊆K_i、diam(K_i)≤κr_i | 真实几何内球形式的原形状界；未输入逆估计。 |
| 粗准一致性与 Hc | Hc=max_i Metric.diam(K_i)，Hc≤Q diam(K_i) | 使用实际最大直径及原准一致比，不以任意尺度参数替代。 |
| 嵌套与 F=V_Hc | hcoarse: V_Hc≤V_h，range(Submodule.inclusion hcoarse) | 同一 L² 状态的真实包含，保留完整粗空间。 |
| 一致质量和原刚度 | L² 子空间继承内积，真实 Dirichlet galerkinStiffness | 精确得到 (A_hx,x)=‖∇x‖²。 |
| Rayleigh 与最终结论 | 原 filterRayleigh，≤C/M.maxDiameter² | 系数、幂次、零空间约定均与原文一致。 |
| 常数依赖 | 先固定 d、κ、Q，再∃C>0，后量化域及两网格 | 无细网格、域尺寸、状态、网格数或算子范数依赖。 |

最终声明显式保留 `[IsFiniteMeasure (volume.restrict S)]` 类型类。它并非新的数学限制：在此实际有限维 Euclidean 空间，原输入 hb:Bornology.IsBounded S 已通过 pinned mathlib 的 `Bornology.IsBounded.measure_lt_top` 给 volume S<∞，再由 `isFiniteMeasure_restrict` 得到该实例。本验收实际读取这两条定理；不把该实例误称为最终证明体内部自动构造。原 Ω 非空来自原 domain/control-region 设置，正维来自 d=2,3；κ、Q 的正性就是原网格规则性参数，允许扩大这些固定界。

细网格的分级和形状条件未被额外使用或加强：本结论只需要细空间包含完整粗空间，因此最终定理覆盖原 Proposition6.1 中所有符合条件的细网格。没有要求细网格也准一致，没有引入 h/Hc 比界。P011 中尚待完成的其他数值接口、H² 正则性或连续 CE 不是这个静态 Rayleigh 命题的必要证明前提。

## 完整原空间和真实弱梯度

`SimplicialPartition` 使用真实非退化 d 单纯形的凸包，给出 closure S 内含、S 的覆盖、不同单元内部不交。有限覆盖和实际边界零测给 a.e. 唯一分区。该结构本身未声称面匹配，但原 conforming triangulation 必然满足这些更弱的几何条件；证明针对该更广类有效，无遗漏原网格。

`dirichletJetSpace` 是所有原紧支 C∞ SpatialTest 的 jet 张成空间在真实弱 H¹ 图拓扑中的闭包；`dirichletSubspace` 是其真实 L² 值像。它不是任意命名子空间，也没有用新点态边界假设替代原 H¹₀。

`mem_conformingSpace_iff` 是双向定理：实际 L² 类属于该空间，当且仅当属于上述原 H¹₀ 且每个单元上 a.e. 等于 c₀+Σ_j c_{j+1}x_j。实际有限维性由有限分片仿射空间的构造内部证明，不由调用者提供，也不假定状态已有共同节点表示。

已直接读取 `conforming_local_polynomial`、`gradient_on_cell` 的证明。它们由完整原弱 H¹ 状态的值在单元上等于仿射多项式，限制到实际开单元内部，以弱梯度唯一性证明全部原梯度等于真实多项式导数；然后利用单纯形边界零测延伸到闭单元的限制测度。开凸域保证单元内部实际位于 S，真实积分求和不会加入域外能量或重计公共边界。

因此本批逆估计及 Galerkin 能量中的梯度，是同一原状态的全弱梯度。没有将任意 L² 类作节点点值，没有额外光滑代表、连续代表、目标梯度公式或零迹前提。

## 实际最大直径与统一粗空间逆估计

第1项先从非空 S 的实际覆盖取得一个单元；d>0 提供两个不同顶点，非退化仿射无关性保证顶点不相等，紧凸包有界。因此该单元 Metric.diam>0；真实有限最大值至少为此值，给 Hc>0。最终两项定理内部调用它，未要求调用者再输入 Hc>0。非空物理域排除了空粗网格，但**未排除粗 P1 空间为零**。

第2项不是直接采用 `inverseScale.bound=Σ_i|H⁻¹|` 的粗糙界。它使用真实 a.e. 唯一分区和每个单元的逆乘子公式，在几乎所有 x∈S 上得到 inverseWeight(H,1)(x)=H⁻¹，因而乘法范数≤H⁻¹‖u‖。单元数量、公共边界的重数和网格大小均未进入最终常数。

第3项调用已验收 C065 的 `conforming_weighted_inverse d (Q*κ) 1`，使用实际常权1、归一化参数 s_i=1，并将每个单元的局部尺度设为同一个 Hc。由原形状和准一致条件，内部得到

\[
H_c\le Q\operatorname{diam}(K_i)\le Q\kappa r_i.
\]

C065 的常数先于域、单元、局部尺度和状态，源自固定维数参考单纯形与实际仿射变换的局部逆估计；本次读取相应关键依赖确认常数不依赖物理单元。全域加权估计使用真实局部多项式梯度和无重叠 a.e. 分区求和。常权比较在证明内部以等式成立，不是调用者的额外输入。

利用第2项消去逆乘子后，得到对所有完整粗状态 u 的

\[
\|\operatorname{field}_1u\|_{L^2}
\le \frac{C_{\mathrm{inv}}(d,\kappa,Q)}{H_c}
\|\operatorname{value}u\|_{L^2}.
\]

固定 C_inv>0 的选择发生在全部 S、M、a_i、r_i、V 和 u 之前。它不是由每张网格的有限维范数等价临时选择；没有隐藏的网格数或最小细单元直径。

## 一致质量、实际刚度和粗空间包含像

`galerkinStiffness` 在有限维真实 L² 子空间 X 上，通过继承的 L² Riesz 同构和实际原形式构造。`galerkinStiffness_form` 给任意独立 x,y 的 (A_hx,y)=a(x,y)，而 `galerkinStiffness_unique` 证明该形式身份唯一确定算子。因此它就是原1485行定义的 A_h，不是另一个满足目标 Rayleigh 界的代替算子。

本次直接核对 `boundedDirichletOriginalForm`：其 V 是原 dirichletSubspace，form 是真实 L² 梯度配对；对称性由真实内积证明，coercivity 由已证明的 H¹₀ Poincaré 界构造。这里没有输入 D(A)=H²∩H¹₀、椭圆正则估计或 CE。虽然该形式的构造会选择域相关 coercivity 常数，本批最终界只使用其**精确梯度形式身份**，不使用该常数估计 Rayleigh 商。

第6项通过 `galerkinStiffness_form` 和 `dirichlet_scalarForm_canonical` 得到

\[
\langle A_hx,x\rangle_{X_h}
=\langle\nabla u,\nabla u\rangle_{L^2}
=\|\nabla u\|_{L^2}^2,
\]

其中 u=`domainSobolevJet ... (inclusion x)`。该定义由原 Sobolev 值同构恢复同一 L² 状态的唯一 H¹ jet，只使用 n=1 的已有 H¹ 资格；没有调用文件中其他涉及椭圆估计的定理。严格值等式和弱值单射保证这是原梯度。X_h 作为 L² 子空间的范数就是原质量范数，没有矩阵质量近似、质量集总或带网格常数的范数替换。

第5项的 F 是 Y→X 包含线性映射的 range。第7项对任意 x∈F 实际提取 y∈完整粗空间且 inclusion y=x，以同一 L² 值等式证明上述 u 的 value 属于粗空间，再直接应用第3项。它没有要求 A_hx∈F，也未对 A_h 在 F 上限制成另一个算子；原细方程与细刚度均未改变。

## 真正 Rayleigh supremum 与原最终结论

已读取实际 `rayleigh` 定义为 inner(Ax,x)/‖x‖²，以及 `filterRayleigh` 为所有非零保留向量的这些实数商的 supremum，F=⊥时明确为0。第4项在非零空间内由 `F.ne_bot_iff` 提供集合非空性；每个 x≠0 保证 ‖x‖²>0，因此可以合法除法，将实际能量上界变成商的上界，再以 `csSup_le` 控制 supremum。F=⊥ 分支由 C≥0直接处理，没有除以零或以空集合 supremum 代替原约定。

第7项取 C=C_inv²>0。对任意保留 x，原质量和梯度身份给

\[
\langle A_hx,x\rangle
\le C_{\mathrm{inv}}^2 H_c^{-2}\|x\|^2,
\]

再由第4项得到 Λ_F≤C/Hc²。第8项把一般 X 专门设为 Mh 的完整 conforming P1 空间；实际有限维实例和 X≤原 H¹₀由既有空间定义内部供应，唯一嵌套输入正是原 V_Hc⊆V_h。

最终 ∃C>0 位于所有粗细索引类型、域 S、两张网格、内球数据和 hcoarse 之前。允许依赖仅 d、κ、Q；证明中不含细尺度 h、细形状界、细分级常数、T、δt、势、控制区域、dim X_h、‖A_h‖或状态。时间和权参数根本不参与这一更强的静态结论。由此完整覆盖原 P019 的结论、物理对象与常数量词，非辅助标量命题。

## 固定依赖、构建及公理

三模块 Carleman 导入闭包共 **339** 模块，**336** 个既有模块与 base 逐字节不变。逐一检查所要求的已验收版本闭包：C065 `ConformingWeightedInverse` 的87模块与 `99694c20834ac8d3b712f5e2d071a4e4ccfc308b` 一致；C048 `GalerkinStiffness` 的283模块与 `1cf3071913d460625411022e4ea16c8336399bf8` 一致；C086 `DirichletScalarForm` 的86模块与 `c5e99b4f0aa241a24dcf27262fced6bc147a60d8` 一致；C041 `FilterReverse` 的11模块与 `12d18c9c6548cc70165ad9e4c01314f4438dc5f1` 一致。读取对应旧验收报告并直接复核本次实际调用的关键证明；未将旧 PASS 套到修改后的依赖。

具体读取包括 `ConformingWeightedInverse`、`CellwiseInverseWeight`、`SimplicialDiameter`、`SimplicialPartition`、`ConformingLocalPolynomial`、`SimplicialLocalGradient`、`SimplicialIntegrals`、`SimplexWeightedInverse`、`SimplexReferenceMap`、`PiecewiseAffinePartition`、`DirichletSpace`、`DirichletForm`、`DirichletScalarForm`、`SobolevGraph`、`GalerkinStiffness`、`FilterReverse` 和实际 rayleigh 定义。C048 中其他物理控制定理的条件范围没有被传入本批刚度构造；C065 的常权和尺度前提在本批证明内部清偿。

治理协议及工具链 pin 与此前已读版本不变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。固定 Lean4.35.0；mathlib manifest pin 与本机实际干净 checkout 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。三个新模块均由固定 root 导入，八项均在固定 CheckAxioms 中有实际展开类型和公理打印。

实际读取 `/tmp/carleman-t135-filter-p1-target.log` 和 `-full.log`，分别为 **3544 jobs**、**3932 jobs** 构建成功。本验收核对这些固定日志，未声称再次运行全库。固定本机 raw 为 **2,147,555 bytes**，SHA256 **`690b28457d73c9b0f025ae6c29901636d674ef65961194ac73f2a2c31eb989d3`**。

八项实际展开类型与已读源码对应，公理均仅为 `propext`、`Classical.choice`、`Quot.sound`。完整文件2448条非空公理记录和8条无公理记录均无异常集合；末行为 **6989项全声明递归审计 PASS**。显式打印与递归总数分别记录。新源码无 sorry/admit/新增数学 axiom，没有以未证明假设提供目标逆界或 Rayleigh 界。

## 实际同 SHA CI 与独立原始证据

本 Agent 自行经 GitHub connector 查询 [main run 39217963129 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39217963129/attempts/1)：event=push，head 精确为 checked_sha，最终 completed/success，updated_at=`2026-10-19T07:48:00Z`。三项 job 全部 completed/success：lean **117946202613**（07:47:50Z）、state-check **117946202934**（07:44:54Z）、dashboard / snapshot **117947314719**（07:48:00Z）。Lean pin、构建、结果记录、证据保存及 post 步骤全部成功。

同 run 原始 artifact：`lean-ci-result` **12171060012**，ZIP492 bytes，digest `sha256:dc69edb03828d06729e1ea0bf8d23a7f01a763772b9f7782e4d0b28e7fc3d207`；`lean-declaration-evidence` **12170870541**，ZIP198082 bytes，digest `sha256:0e43adbeec5b30cc45816980896ceb73d5f758342a087c577718767477c92ddc`。实际 workflow_run 元数据均绑定本 run、main、精确 proof SHA。

本 Agent 自行 `gh run download 39217963129`，分别下载至 `/tmp/carleman-t135-filter-p1-main-ci/result.json` 和 `/tmp/carleman-t135-filter-p1-main-axioms/axioms.txt`。result 实际为 **PASS**，`checked_sha=source_head_sha=7ad1a9dd94d3abfe384564b1f24f351f5c60fe21`，target=Carleman，`finished_at=2026-10-19T07:46:46.513848+00:00`。远端 Lean 提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 与 pin 一致。解压 result 为537 bytes，SHA256 `af359dde8afc861a83fa27e039d161117128e422c4b550c73651cbccc7691380`。

独立逐字节比较远端 raw 与 `/tmp/carleman-t135-filter-p1-local-axioms.txt`，完全相同：**2,147,555 bytes**，SHA256 **`690b28457d73c9b0f025ae6c29901636d674ef65961194ac73f2a2c31eb989d3`**，末行6989项递归审计通过。原始文本摘要未与 artifact ZIP 摘要混同，没有使用动态 `.ci` 或其他阶段证据。

## 最终验收决定

**完整原 Proposition7.7 / P019：PAPER PASS。** C151/P019 可在本固定版本登记为 REVIEWED/PAPER。八项声明未发现数学、实际空间、测度、刚度、质量、supremum、嵌套、量词、额外前提或依赖公理缺陷；正式同 SHA 三项 CI 与独立原始产物全部核验通过。

本结论清偿真实一致质量 P1 粗空间的 Λ_F≤C Hc⁻²，常数只依赖维数及粗网格形状/准一致界。允许将原文完成数由14/26提升为15/26，但仅增加 P019；P011、P023、Cartesian P020以及其他观察/控制命题仍按各自未完成义务处理。

本次仅新增本报告，未修改实现、台账、原文或 root，未 commit/push。最终报告一致性检查并通知主 Agent 后，冻结上述 reviewed_at 与全部报告内容，不再改动。
