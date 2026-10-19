# T183 / C199 独立本机验收：原时空单元平均与差分势的强 L² 一致性

- checked_sha / source_sha: `8e2e1e1a269c81ea0f9fdd98c6f13477cf8583b8`
- mathematical_base: `ffa5a6f8061e5b13aa96a7f77081aa4f8482e2e5`
- reviewed_at: `2026-10-19T15:18:34+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_foundations`
- result / axiom_check: **PASS / PASS**；全部 **13/13** 显式声明通过，无阻断缺陷。
- scope: **AUXILIARY**；C199 可登记 REVIEWED，原文覆盖保持 **17/26**。本批完成原差分时空平均势的强 L² 一致性，不提升有限元时间势、极限 PDE 或完整控制收敛。

## 固定版本与原文

直接读取固定 Git 对象四模块的全部证明、固定 raw 中十三项完整展开类型、T183 分析、MATH_SPEC 和 C198/C199 台账。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 与本 Agent 已读 T180 版本相同，沿用其规则。未来 FixedTimeCellStrongConvergence、TimePotentialReconstruction 等草稿与动态根导入、公理输出均不作为本批证据。

原文实际对照 `paper/main.tex:2294–2329`：原 b∈L∞(𝒬)、eq:conv-data-fd 的时间—空间平均、真实对偶单元及 E_h；另完整读取 `2893–2925` 的一致性范围和 eq:conv-potential-consistency。2893 行明确 **T、y0、b 固定，空间和时间独立趋零，不耦合**；2907 行定义差分势在原时空单元取 b_i^n，其他位置零延拓；2917–2920 行要求原 M 上界和强 L² 极限。本批确实针对这份原差分对象。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与已验版本不变。

已完整读取 [T182 冻结报告](T182-local-acceptance.md)，报告提交 **`7edbc905e19aabaa5b4300c0b835eb328edb4235`**，checked SHA 正是本批 mathematical_base，reviewed_at=`2026-10-19T15:07:21+00:00`，25/25 PASS。另重新读取其实际时空单元、完整势、Fubini 公式、平均系数、单元乘子以及本批使用的最佳逼近/密度代码。T180 自身冻结报告为 `5d7bf13e6d15857cf74bb5e3a234500ffada5e1e`，checked=`1d85add4836977c5a6b3bd55448110e9bad21a50`；关键闭包另行核对，不以报告代替源码检查。

## 全部十三项声明

顺序与固定 manifest 一致。源码相对 `Carleman/`；raw 行为固定完整类型起始行。三个定义只按定义忠实性验收，其余十项确有实际证明。

| 序号 | 完整声明 | 固定源码 | raw 行 | 判定 |
| --- | --- | --- | --- | --- |
| 1 | `Carleman.finiteCell_continuous_residual_tendsto` | `Spatial/FiniteCellStrongConvergence.lean:29` | 34820 | 真实紧集连续模和未覆盖测度给同一平均投影的连续类极限；PASS。 |
| 2 | `Carleman.finiteCell_average_strong_convergence` | `Spatial/FiniteCellStrongConvergence.lean:72` | 34844 | 实际密度与残差收缩推广到任意原 L² 数据；PASS。 |
| 3 | `Carleman.fixedSpacetimeCellIsometry` | `Spatial/FixedSpacetimeCellReconstruction.lean:14` | 34867 | 固定原时空域、原乘积单元及真实质量 dt·∏δ 的等距重构；PASS。 |
| 4 | `Carleman.fixedSpacetime_uncovered_volume` | `Spatial/FixedSpacetimeCellReconstruction.lean:24` | 34881 | 实际时空未覆盖测度恰为 T 乘空间未覆盖测度；PASS。 |
| 5 | `Carleman.fixedSpacetime_uncovered_volume_tendsto` | `Spatial/FixedSpacetimeCellReconstruction.lean:62` | 34896 | 固定 T 下真实时空条带测度趋零；PASS。 |
| 6 | `Carleman.fixedSpacetimeCell_average_strong_convergence` | `Spatial/FixedSpacetimeCellStrongConvergence.lean:15` | 34913 | 全部时空 L² 数据、独立空间/时间细化的强极限；PASS。 |
| 7 | `Carleman.BoundedMultiplier.toL2` | `Control/AveragedPotentialStrongConvergence.lean:14` | 34937 | 有限测度下同一实际 a.e. 有界函数的 L² 类；PASS。 |
| 8 | `Carleman.BoundedMultiplier.toL2_ae` | `Control/AveragedPotentialStrongConvergence.lean:17` | 34942 | 该真实 L² 类与原 b.value a.e. 一致；PASS。 |
| 9 | `Carleman.cartesianSpacetimePotential_eq_projection` | `Control/AveragedPotentialStrongConvergence.lean:22` | 34945 | 原完整分片势的 L² 类严格等于同一 E E* b；PASS。 |
| 10 | `Carleman.fixedSpacetimePotential` | `Control/AveragedPotentialStrongConvergence.lean:47` | 34955 | 精确时域/盒等式运输后的同一原势重构；PASS。 |
| 11 | `Carleman.fixedSpacetimePotential_bound` | `Control/AveragedPotentialStrongConvergence.lean:56` | 34970 | 保存同一个 b.bound，不引入网格或时间因子；PASS。 |
| 12 | `Carleman.fixedSpacetimePotential_eq_projection` | `Control/AveragedPotentialStrongConvergence.lean:65` | 34978 | 固定时空域上原势与实际正交平均的严格身份；PASS。 |
| 13 | `Carleman.cartesianAveragedPotential_strong_convergence` | `Control/AveragedPotentialStrongConvergence.lean:76` | 34990 | 原固定 a.e. 有界势的真实分片重构强 L² 收敛；PASS。 |

## 通用单元强逼近没有假设目标结论

第 1–2 项在同一有限 Borel 测度上，允许各层有限指标和离散空间变化。明确输入为真实可测、不交、同层等正质量单元，实际所选点 p_n,i 及全部单元均位于一个固定紧集 A，真实点到所选点距离≤r_n→0，以及真实未覆盖测度趋零。这里没有把任意数据的逼近或目标强收敛作为条件。第一项不需要 WeaklyRegular；第二项为调用实际 L² 密度定理保留该测度类条件，随后具体原时空域在内部满足它。

对辅助 f:Ω→ᵇℝ，代码使用真实 `toLp` 类，其 a.e. 代表等于 f。紧集 Heine–Cantor 供给同一 f 的局部模，不要求全空间一致连续。取 V=ν(univ)≥0、η=sqrt(ε²/(2(V+1)))，真实点距离趋零使各单元振幅≤η；未覆盖项乘 ‖f‖² 趋零。已验收实际积分估计给 **‖u−EE*u‖²≤η²V+‖f‖²ν(未覆盖区)**，两项各由 ε²/2 控制。V+1 避免零体积除法。辅助点仅用来选择比较候选 f(p_n,i)，被估计的仍是原单元平均 EE*u。

重新读取 FiniteCellApproximation：误差平方确由 L² 内积识别为真实积分；Lp 代表身份、逐单元控制和未覆盖区域的零值均在同一个 a.e. 集上使用；残差平方与常数指示函数的可积性在内部提供，再应用 integral_mono_ae。没有丢弃未覆盖项或假设单元覆盖全域。

第 2 项调用真实 `BoundedContinuousFunction.toLp_denseRange`，并使用 T180 的 **Id−E_nE_n*** 范数≤1与线性残差分解，推广至每个 u∈L²。完整物理有限空间的完备性在内部给出，不要求所有网格有同一指标类型。密度定理要求的有限 p=2、Borel/Normal 空间、相应第二可数性和弱正则测度均准确：通用 Ω 为 metric，值域ℝ满足所需 SecondCountableTopologyEither；具体乘积域有限 Borel 测度在可度量空间中具有弱正则性。没有新增密度公理或调用者提供的稠密族。

本批没有声称在整个 L² 单位球上一致趋零。连续模和所需细化程度可依赖原固定数据、ε和固定域，这与逐个原 L² 数据的强收敛相符。

## 固定原时空域、质量与条带

第 3 项直接由真实 `finiteCellIsometry` 构造，单元为 **(t_i,t_i+dt]×D_a**，指标为 Fin(g.steps)×CartesianInteriorIndex N，质量准确为 **dt·∏δ_j**。空间状态质量与时间质量均来自原限制 Lebesgue 测度，不是抽象指定的系数。hbox:lo_j+N_jδ_j=hi_j 和 hT:g.period=T 将全部网格的输出置于字面相同的 **Lp ℝ 2 ((volume|(0,T]).prod(volume|Ω))**。目标空间就是原时空 L²，不把不同域的范数数值混同。

第 4 项先计算全部时空测度 **T·ν(Ω)**，再由真实不交有限并、单元质量和指标基数得到已覆盖测度 **T·ν(⋃D_a)**：时间步数乘 dt 恰为 T。最后在有限测度中应用两个真实补集公式，得 **μ(未覆盖时空区)=T·ν(未覆盖空间区)**。没有漏掉时间步数、dt，亦未把每个时间截面分别估计后增加一个 T 因子。

第 5 项使用 T180 精确空间体积差 **∏(hi−lo)−∏(hi−lo−δ_n)** 的极限，再乘固定 T。空间 N_n,j≥1 使自然数内部节点数的 −1 转换合法；各 δ_n,j→0 足以清偿条带。这个条带极限定理本身无需 dt_n→0，因为每个合法时间网格已具有全部时间长度 T。后续完整逼近才加入时间直径趋零。

原时间单元为左开右闭，最后一个含 T，相邻端点处理继承真实不交证明；没有周期回绕节点或对 b 的周期性要求。时间0与原开区间端点的差异为零 Lebesgue 测度。空间开单元之间的面和边界条带仍在真实补集中，未冒称全域覆盖。

## 独立细化与真实距离

第 6 项内部选择固定紧集 **[0,T]×closure Ω**。辅助点为原时间左端节点与原空间内部节点；这份辅助点不必属于左开时间单元，但确实属于同一紧集，恰好满足通用引理的真实要求。单元内所有点也属于该紧集。

代码对 ℝ×SpatialCoordinates d 使用 mathlib 产品 metric，明确以 **Prod.dist_eq=max(时间距离,空间距离)** 计算，不把它误认为 Euclidean 平方和。时间距离≤dt_n；实际空间 Euclidean 距离≤d h_n。因此两者均≤ **r_n=dt_n+d h_n**。由 dt_n→0 与 h_n→0 分别推出 r_n→0；δ_n,j>0、δ_n,j≤h_n 又给全部坐标步长趋零。没有要求任何 dt/h 比例、嵌套网格、长宽比或数据光滑性。

T、lo、hi 是固定参数，所有 g_n.period=T，故这不是 T_n 变化的极限。声明写0≤T，而合法 TimeGrid 的正 dt 和正 steps 连同 hT 实际强制 T>0；未以不存在的 T=0 正步长网格支撑结论。空间可在某粗层 N_j=1 而没有内部节点，此时重构为零、条带可为整个空间，公式仍成立。d=0 时空间质量空乘积为1、空间条带为零，r_n=dt_n，定理退化为真实时间平均。没有除以 d 或选取不存在的空间节点。

这里所有实际几何、正质量、紧集、可测性、不交性和条带极限均在具体实例内部清偿；最终任意时空 L² 输入不需要提供平均逼近能力或紧支撑代表。

## 同一原 a.e. 势，真实 Fubini 与 EE* 身份

`BoundedMultiplier` 的实际字段只有原 value、AEStronglyMeasurable、非负有限 bound 和 a.e. 绝对值界。第 7 项用有限测度下的 `MemLp.of_bound` 对**同一个 value**建立 L² 类；第 8 项给其真实 a.e. 身份。没有对原势加入处处有界、连续、Sobolev、时间周期性或额外可积性前提。

第 9 项实际逐坐标比较真实 Hilbert 伴随与原 cartesianAveragedPotential：两者均为 **(dt·∏δ)⁻¹∫_(timecell×D_a)b**。T182 的 product_formula 从原先时间、后空间平均出发，使用同一原 b 的可积性和真实 setIntegral_prod；可积性由有限柱体上的 a.e. 有界性内部供应，重复限制利用单元包含于原域消去，确为原稿的 Lebesgue 双积分。

本批再把 b.toL2_ae 正确限制到每个时空单元，integral_congr_ae 得每个系数与 E*b.toL2 **严格相等**。最后用 Lp.ext、原分片势 toL2 的 a.e. 身份及 E 的真实有限指示和身份，证明其整个 L² 类等于 **E(E*b.toL2)**。这不是仅比较两者范数，也不是在通用等距存在量词中另选一个替身重构；E、E*、b 及全部平均系数都是原具体对象。

第 10 项只用精确 hbox/hT 代入，返回同一原 cartesianSpacetimePotential；第 12 项将上述整个身份运输到固定原时空域。原 b 的零测修改不会被节点采样放大：本批只积分实际 b，且既有 cartesianAveragedPotential_congr 已保证平均系数的代表无关性。辅助连续类使用节点值的步骤没有进入对原 b 的定义。

第 11 项的 bound 字段**恰为原 b.bound**，配合原分片构造中的真实 bounded 证明给实际 a.e. 上界；并非宣称其本质上确界必等于预算。若原 b.bound≤M，则原离散势仍满足 M，M=0 亦允许。finiteCellFunction 的原指示和在所有未覆盖位置逐点为零，第 10 项没有修改此值；所得 L² 身份保留这个具体零延拓代表。

第 13 项只重写该已证 EE* 身份，随后把 **同一固定 b.toL2** 交给第 6 项；不是每个 n 选择不同 b_n。得到原 **‖b_h,dt−b‖L²(𝒬)→0**。T 固定、h和dt独立趋零，且保界常数仍为1，不含 T、网格节点数或质量倒数的损失。此定性强收敛不声称对变化 T 或全部 L∞ 单位球统一收敛速率。

## 固定闭包、公理和构建

递归解析四入口实际 Carleman 导入共 **346** 模块，除四新增模块外 **342** 个与 mathematical_base 逐字节相同。关键接受版本的完整闭包另行比较，全部无变化：

| 入口 / 已接受阶段 | 固定接受版本 | 闭包模块数 |
| --- | --- | --- |
| CartesianSpacetimePotential / T182 | `ffa5a6f8061e5b13aa96a7f77081aa4f8482e2e5` | 336 |
| FixedBoxCellReconstruction / T180 | `1d85add4836977c5a6b3bd55448110e9bad21a50` | 331 |
| DenseReconstructionConvergence / T180 | `1d85add4836977c5a6b3bd55448110e9bad21a50` | 2 |
| TimeCellReconstruction / T177 | `d1134c0ccc8f343aef6223f304fe52f86a7aff1d` | 23 |

固定 Carleman.lean 导入全部四模块，十三项在固定 CheckAxioms 中实际执行完整 #check @ 和 #print axioms。新源码无 sorry、admit、新 axiom 或 native_decide。十三项公理只含正常 `propext, Classical.choice, Quot.sound`；独立解析 raw 全部 **3239** 条显式公理记录（**3235** 个不同名字，**9** 条无公理记录），规范化换行空白后白名单外依赖为零。实际递归 auditor 末行确认 **8379 项 Carleman 声明全部 PASS**。

实际读取 `/tmp/carleman-t183-potential-strong-target2.log` 的最终强收敛目标 **3538 jobs** 和 `/tmp/carleman-t183-potential-strong-convergence-build.log` 的根构建 **4138 jobs** 均成功。`-axioms.log` 是零字节 stderr，成功结论取自固定 raw 的真实末行。

Lean pin v4.35.0，正式 CI compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 和本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、workflow 与 lean_ci.sh 相对已审 T180 未变。MemLp.of_bound、setIntegral_prod 和 toLp_denseRange 的实际类型/证明入口本次重新读取；已核对的紧集一致连续性与有限 Borel 测度弱正则实例来自同一固定 mathlib。

## 独立同 SHA CI 与原始工件

本 Agent 自行查询实际 GitHub run/jobs/artifacts API，并分别自行执行两次 gh run download，两命令均 exit 0；未以执行者的 root 副本替代独立下载。

- run: [39276162774 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39276162774/attempts/1)，event=push、branch=main、head_sha 精确等于本报告 SHA；最终 **completed/success**，updated_at=`2026-10-19T15:17:31Z`。
- state-check **118140901118**、lean **118140901330**、dashboard / snapshot **118142570220**：最终三项均实际查询为 **completed/success**。曾观察 dashboard 仍运行，等待最终成功后才签发。
- `lean-ci-result` artifact **12197986920**，ZIP **492 bytes**，API digest=`sha256:a035ca70f548a281685d38593e2ed6680d0c6abc31b682f864dcdf0e6f517ead`。
- `lean-declaration-evidence` artifact **12197228604**，ZIP **247406 bytes**，API digest=`sha256:2bb9971cba6340e1cea39f8182c19d1f82305ea844ff2fa10960c6bdd0639a55`。
- 两工件 workflow_run 均绑定同一精确 SHA、main 和 run；压缩工件 digest 与解包 raw hash 分开记录。

独立 `/tmp/carleman-t183-potential-strong-convergence-main-ci/result.json` 为 **537 bytes**，SHA256=`09aa78f292e81299c7ab1af28f94c270026211687d4ab6d96c30533eb420cc9d`；实际 status=PASS、checked_sha=source_head_sha=`8e2e1e1a269c81ea0f9fdd98c6f13477cf8583b8`、targets=[Carleman]、finished_at=`2026-10-19T15:16:16.792427+00:00`，ci_url、Lean、mathlib 与上述记录一致。

独立 `/tmp/carleman-t183-potential-strong-convergence-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t183-potential-strong-convergence-local-axioms.txt` **逐字节完全一致**，均为 **2676806 bytes**，SHA256 **`e0e571fd89f5088d6cc8280b277295e649c4b36542368a975409ceb1b83c4aef`**；完整类型、公理和末行8379项成功实际核对。

## 最终结论

**13/13 PASS，无需修复。** 真实有限单元密度论证与固定时空几何给任意原时空 L² 平均强逼近，同一原 a.e. 有界势的实际重构严格识别为 EE*，保留原上界及未覆盖区零值，并在独立时空细化下强收敛。C199 可登记 **AUXILIARY/REVIEWED**，覆盖保持 **17/26**。有限元时间势、R_h−E_h 误差、状态弱极限方程、初终值及完整控制收敛不由本批完成。仅本报告单文件提交，不 push、不改数学/台账；通知后正文与 reviewed_at 冻结。
