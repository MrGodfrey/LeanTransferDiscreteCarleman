# T181 / C197 独立本机验收：完整 P1 投影对任意 L² 初值的强一致性

- checked_sha / source_sha: `7a2f33cfe125a118ee1792410345603891957e6c`
- mathematical_base: `1d85add4836977c5a6b3bd55448110e9bad21a50`
- reviewed_at: `2026-10-19T15:01:04+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result / axiom_check: **PASS / PASS**；全部 **5/5** 显式定理通过，无阻断缺陷。
- scope: **AUXILIARY**；C197 可登记 REVIEWED，原文覆盖保持 **17/26**。本批完成原 P1 初值强一致性，不提升完整控制收敛、势一致性或连续 PDE 极限。

## 固定版本、原文和前置验收

直接读取固定 Git 对象中两个模块的全部源码与证明、固定 raw 中五项完整展开类型、T181 分析、MATH_SPEC、C197/T181 台账和关键旧依赖。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 与已读取 T178 版本逐字节相同，继续执行独立数学验收协议。固定台账仍为 SPECIFIED/RUNNING，不把执行者自检或已有 CI 当作语义审核。未来 FiniteCellMultiplier 等势配对草稿及动态 `.ci` 不在本次范围。

原文核对 `paper/main.tex:2294–2318` 中 `eq:conv-data-fe` 的 y₀,h=Π_hy₀、FE 的 E_h=R_h=实际包含，以及 `2897–2925` 的 `eq:conv-data-consistency`：任意 y₀∈L² 下 ‖E_hy₀,h−y₀‖→0。另结合 Section 6 的完整 H¹₀∩P1 空间与真实 L² 正交投影定义，以及控制收敛整条命题限定范围。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，相对已验版本无变化。

签发前完整读取并核实 [T180 冻结报告](T180-local-acceptance.md)，report commit=`5d7bf13e6d15857cf74bb5e3a234500ffada5e1e`，checked SHA 正是本批 mathematical_base，reviewed_at=`2026-10-19T14:55:17+00:00`，9/9 PASS；报告工作区字节与该提交完全一致。该报告补齐前置验收门槛，本次另重新读取 DenseReconstructionConvergence、IsometricReconstructionProjection 的实际全部证明，未用报告代替依赖检查。

## 五项声明逐项验收

顺序与固定 manifest、C197/T181 一致。源码位置相对于 `Carleman/Spatial/`；raw 行指固定原始产物中实际完整类型的起始行。

| 序号 | 完整声明 | 固定源码 / raw 行 | 判定及实际内容 |
| --- | --- | --- | --- |
| 1 | `Carleman.spatialTest_toLp_denseRange` | `SpatialTestLpDensity.lean:11` / 34554 | PASS；全部原紧支撑光滑测试在实际域 L² 中稠密，无预设稠密性。 |
| 2 | `Carleman.SimplicialPartition.nodal_lipschitz_value_error` | `P1InitialDataApproximation.lean:20` / 34557 | PASS；真实节点仿射插值在实际闭单元上的误差≤2 C maxDiameter。 |
| 3 | `Carleman.SimplicialPartition.test_nodal_L2_error` | 同文件:34 / 34565 | PASS；真实 nodalLp 和 a.e. 分割给原 L² 误差≤vol(S)^(1/2)·2 C maxDiameter。 |
| 4 | `Carleman.SimplicialPartition.test_projection_L2_error` | 同文件:46 / 34574 | PASS；节点插值的原 Dirichlet 成员资格内部供给，完整 P1 投影最佳逼近给同一误差界。 |
| 5 | `Carleman.full_p1_initial_projection_strong_convergence` | 同文件:69 / 34589 | PASS；变化网格的实际正交投影对任意原 L² 初值强收敛。 |

## 测试函数 L² 稠密性没有循环前提

`SpatialTest S` 的原定义是全空间 C∞、实际紧支撑且 tsupport⊆S 的函数；toLp 由真实 MemLp 构造，a.e. 代表就是该函数。第一项先令 P 为这些真实 H¹ 测试 jet 的线性 span，再令 D 为 P 经真实值映射进入 L² 的像。对 D 的任意正交向量 u，所有测试的 L² 配对均为零；调用实际 `spatial_eq_zero_of_tests`，以原限制测度 a.e. 落在开放 S 为资格，推出 u=0。

本次重新读取该分离定理及固定 mathlib 的 `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`：原 L² 资格给局部可积性，所有真实 C∞ 紧支测试的积分为零给 u 在 S 内 a.e. 为零；限制测度的 hν 再给整个原 Lp 类为零。它没有假设 H¹、H²、连续代表、目标投影收敛或测试已稠密。因此用 Hilbert 空间正交补为零等价于闭包为全空间，是合法的非循环稠密性证明。

还须证明 D 恰是**单个测试函数**的 toLp 值域，而不只是它的线性包。代码实际调用 `exists_test_of_mem_test_span`；重新读取 SpatialTestOperations：零、加法和实数乘法保持真实光滑性、紧支撑及支撑包含，jet 运算通过原开放域的真实弱导数唯一性识别，span induction 产生一个实际测试。由此得到 D=range(toLp)，严格满足最终 DenseRange 输入。第一项对任意开放 S 成立，不额外要求有限体积、凸性或非空。

## 真实节点误差、测度和完整 H¹₀ 成员

第二项对全空间 Lipschitz 函数 f 的实际值作节点插值。对单元 i，选其真实顶点 a=(M.simplex i).points 0，以常仿射函数 p=f(a) 比较。真实 `Metric.diam` 给单元内 dist(y,a)≤diam(K_i)≤maxDiameter，因而 |f(y)−p(y)|≤C maxDiameter。调用已证节点仿射再现与局部 L∞ 稳定常数 1，得到 **|f−I_hf|≤2 C maxDiameter**。没有使用内球半径、最小角、形状常数或梯度逆界；辅助定理所在模块虽另含导数估计，本次调用的是不带这些条件的零阶定理。

FaceMatching 是真实公共部分包含于公共顶点凸包的几何条件；它使局部节点插值在交界处一致，`nodalFunction_on_cell` 识别同一全局函数与当前单元的实际仿射多项式。并未将抽象多项式或任意 P1 函数命名为节点插值。节点取值仅作用于实际光滑测试/经典 Lipschitz 函数，最终任意 L² 初值从未在顶点评价。

第三项使用 φ.toLp_ae、真实 nodalLp_ae、Lp 差的 a.e. 身份与 M.ae_partition，得到真实差值 L² 类的 a.e. 范数界。固定 mathlib `Lp.norm_le_of_ae_bound` 给因子 `measureUnivNNReal(volume.restrict S)^(2.toReal⁻¹)=|S|^(1/2)`；没有漏掉体积因子或把点态界直接当作 L² 界。有限体积是声明中明确的实例前提，由原有界域满足。零测度和空域不需除以 |S|；粗网格 nodalBound 只用于建立 Lp 存在，不进入最终误差常数。

第四项没有把插值属于 H¹₀ 当作输入。φ 的 tsupport⊆S 及 S 开，使每个真实 frontier S 节点不在 φ 的支撑，从而该节点值为零。然后调用实际 `nodalLp_mem_dirichletConformingSpace hS hc hM hB`。本次重新读取这个依赖：BoundaryFitted 把单元边界部分表达为边界节点凸包；真实全局节点函数先具有 H¹ 弱 jet，向内缩放的 H¹ 强极限与紧支光滑卷积闭包证明它属于原 **dirichletSubspace**。此空间来自全部测试在完整 H¹ 图范数下的闭包，经真实值映射进入 L²，绝非任意边界零值类的替代定义。

上述成员资格只需要原开放凸域、真实 FaceMatching、BoundaryFitted 和有限网格；即使其存在性证明中的 Lipschitz 常数依赖某个网格，该常数也未进入第二、三项的统一零阶误差。空域分支在既有成员证明内实际处理，未偷偷要求一个内部点始终存在。

## 完整 P1 正交投影与变化网格

重新展开 `M.conformingSpace (dirichletSubspace S)`：它是实际 piecewiseAffineSpace 与原 H¹₀ 值空间的交。已有成员等价定理精确量化每个真实单元上的 a.e. 仿射表示；由真实有限系数空间的像取得有限维性，再由子空间继承有限维/完备性。因此它是完整原 V_h，不是本次构造的节点插值像，也不是另外选定的有限维子空间。

取 X 为该完整空间，E=X.subtypeₗᵢ 是原 L² 中的实际包含等距。真实 `Submodule.adjoint_subtypeL` 给 E* 正是 X.orthogonalProjectionOnto。第四项使用同一个 E 的真实最佳逼近，以已证在 X 内的 nodalLp φ 为比较向量；得到的左端严格是 **‖φ−Π_hφ‖_L²**。没有替换投影、改变质量内积或增加一个最优性假设。

底层最佳逼近证明由 E*E=id、实际残差正交和 Pythagoras 推出。取比较向量0给 `Id−EE*` 的范数收缩常数1。有限维性只用于保证 X 完备和真实正交投影存在；证明不使用网格相关的范数等价常数。

最终允许 ι_n 及 X_n 随 n 改变，所有投影仍落在同一个固定原 H=Lp ℝ 2 (volume.restrict S)。对每个固定测试 φ，实际 C∞ 紧支撑在内部通过连续真实导数的紧支界给一个全局 Lipschitz 常数 C_φ；该常数在所有 n 之前选出。于是 **‖φ−Π_nφ‖≤2|S|^(1/2)C_φ h_n→0**。h_n 正是每个网格真实单元直径的有限最大值；不是一个另给的形式尺度。

随后调用 T180 的真实稠密性推广：给任意 u 与 ε，先从本批证明的 DenseRange 选一个测试 φ 使 ‖u−φ‖<ε/2，再用残差线性和统一收缩界

`‖(Id−Π_n)u‖ ≤ ‖u−φ‖ + ‖(Id−Π_n)φ‖`，

最后取得趋零，转换成原 Lp 范数拓扑中的 **Tendsto(Π_nu)(𝓝u)**。不是弱拓扑收敛，也没有通过变化离散空间中的不同范数比较来声称收敛。原 FE 中 E_h=R_h=包含，y₀,h=Π_hy₀，所以这正是原 `eq:conv-data-consistency` 的 P1 初值结论。

## 量词、假设及范围

最终完整类型只要求：任意固定 d、开放凸 S、其限制 Lebesgue 测度有限；任意有限非退化单纯形分割序列，原覆盖/内部不交、FaceMatching、BoundaryFitted；真实 maxDiameter→0；然后量化**每个原 u∈L²(S)**。没有 u∈H¹/H²、零迹、连续代表、本质有界、目标近似误差、H² 正则性或 CE 输入。

没有形状正则、分级、准一致、嵌套网格、维数≤3 或时间耦合条件。原论文的有界凸多面体和合规 P1 网格均包含在此范围；所删去的形状等限制对零阶 L² 强逼近确实不必需。全部维数包括 d=0，顶点0属于 Fin(d+1)，无非法选取不存在顶点；maxDiameter 使用 NNReal 有限 sup，空网格时为0，覆盖条件迫使原域为空，原 L² 空间相应为零。

C_φ 允许依赖固定测试及域，不能将此结论误读为 L² 单位球上的投影算子范数一致趋零。最终对固定 u 的强收敛没有给不可能的一般 L² 定量 h² 率。原初值正交投影范数不增是既有 Hilbert 投影事实；本批五项新增定理的主结论是强一致性。势平均强一致性、FD 的 R_h−E_h、状态紧性、弱 PDE 和终态零值均不由本批完成，仍保持 AUXILIARY。

## 固定闭包、公理与构建

递归读取两模块实际 Carleman 导入闭包共 **123** 个模块，其中 **121** 个旧模块与 mathematical_base 逐字节相同。关键接受版本的完整闭包另行比较，均无变化：

| 依赖入口 / 已验收阶段 | 固定接受版本 | 闭包模块数 |
| --- | --- | --- |
| DenseReconstructionConvergence / T180 | `1d85add4836977c5a6b3bd55448110e9bad21a50` | 2 |
| NodalDirichletMembership / T044 | `50ea3111057c5d7b796cca799c10a9a900d14caf` | 113 |
| SimplexNodalRemainder / T059 | `daf0c9e455f04bf5d7eff4e4ecde1729e01f6a92` | 73 |
| SimplicialDiameter / T050 | `9ea552502177ccffb3f50593567578fc207c2568` | 28 |
| SpatialTestOperations / T040 | `4f669626b3228adea39a16fbf6c1d22313763331` | 31 |
| WeakDerivativeUnique / C022 | `a6c199412758d406be8c3f8d1e76587b9f820bc1` | 18 |

固定根 `Carleman.lean` 导入两模块，五项都实际执行完整 `#check @...` 和 `#print axioms ...`。新源码无 sorry、admit、新 axiom 或 native_decide。五项各只依赖 `propext, Classical.choice, Quot.sound`。独立解析完整 raw 的 **3201** 条显式公理记录（**3197** 个不同名字，含 9 条无公理记录），白名单外依赖为零；实际递归审计末行确认所有 **8314 项 Carleman 声明 PASS**。

实际读取 `/tmp/carleman-t181-test-density-target.log`：**3165 jobs**；最终 `/tmp/carleman-t181-p1-initial-target4.log`：**3293 jobs**；固定 `-build.log` 根目标 **4130 jobs**，均成功。早期草稿失败日志未当作最终证据；`-axioms.log` 为零字节 stderr，真实结论取自完整 raw。

Lean pin v4.35.0，正式 CI compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 与本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿、工具链、manifest、lean/dashboard workflows 和 `tools/lean_ci.sh` 相对已审 T178 未变。测试分离、正交补闭包、包含的伴随、真实紧支导数 Lipschitz 界及 Lp 范数积分界均在该固定 mathlib 版本核对。

## 独立同 SHA CI 与原始工件

本 Agent 自行查询 GitHub run/jobs/artifacts API，并分别执行两次 `gh run download`，均 exit 0；没有以 root 下载副本代替独立取证。曾见 lean 仍收尾，待实际三项最终成功后才签发。

- run: [39273494519 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39273494519/attempts/1)，event=push、branch=main、head_sha 精确等于本报告 SHA；最终 completed/success，updated_at=`2026-10-19T15:00:07Z`。
- lean job **118131644950**：completed/success，完成于 `2026-10-19T14:59:57Z`。
- state-check job **118131645586**：completed/success，完成于 `2026-10-19T14:56:44Z`。
- dashboard / snapshot job **118133470109**：completed/success，完成于 `2026-10-19T15:00:06Z`。
- `lean-ci-result` artifact **12197450111**，ZIP **491 bytes**；API digest `sha256:4f87476c74638ca2fb49391537163a0f19c7264de0db046d8dcdd46e42b1f857`。
- `lean-declaration-evidence` artifact **12195869384**，ZIP **245224 bytes**；API digest `sha256:158ffc8734a77579398039c7e22a8d353ee6ecd6c86fbcac8f04dcb6cd1757cc`。

两工件 workflow_run 均绑定同一精确 SHA、main 和 run。独立 result `/tmp/carleman-t181-p1-initial-consistency-main-ci/result.json` 为 **537 bytes**，SHA256 `a78f12e9635934606290b794a0a04f9df926ec94c4fb87dcf28192d988a5099d`；实际 status=PASS、checked_sha=source_head_sha=`7a2f33cfe125a118ee1792410345603891957e6c`、targets=[Carleman]、finished_at=`2026-10-19T14:58:49.545636+00:00`，ci_url/Lean/mathlib 均一致。

独立 raw `/tmp/carleman-t181-p1-initial-consistency-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t181-p1-initial-consistency-local-axioms.txt` **逐字节完全一致**，均为 **2648603 bytes**，SHA256 **`b24ada60ea3339c20f09003f765fe509374d35d112bf0a31880fec4d3ea15b79`**。ZIP digest 与解包 raw hash 分别记录；完整类型、公理及最终 8314 项成功记录均实际核对。

## 最终结论

**5/5 PASS，未发现阻断缺陷。** 真实测试 L² 稠密性、节点插值误差及原 H¹₀ 成员资格、完整 P1 空间的实际 L² 正交投影最佳逼近与统一残差收缩，共同证明任意原 L² 初值的强一致性。未增加初值正则性、形状/分级或网格嵌套假设。C197 可登记 **AUXILIARY/REVIEWED**，原文覆盖保持 **17/26**；完整控制收敛仍待后续义务。本报告仅单文件提交，不 push、不改实现/原稿/台账；通知后正文与 reviewed_at 冻结。
