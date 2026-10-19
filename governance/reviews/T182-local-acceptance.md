# T182 / C198 独立本机验收：原平均势重构、时空单元与精确配对

- checked_sha / source_sha: `ffa5a6f8061e5b13aa96a7f77081aa4f8482e2e5`
- mathematical_base: `7a2f33cfe125a118ee1792410345603891957e6c`
- reviewed_at: `2026-10-19T15:07:21+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_section3`
- result / axiom_check: **PASS / PASS**；全部 **25/25** 显式声明通过（6 个定义、19 个定理），未发现阻断缺陷。
- scope: **AUXILIARY**；C198 可登记 REVIEWED，原文覆盖保持 **17/26**。未完成时空平均强收敛、状态极限方程或完整控制收敛。

## 固定版本与原文定位

直接读取固定 Git 对象的四模块全部源码、固定 raw 中 25 项完整展开类型及证明，并核对 [T182 分析](../analysis/T182-potential-reconstruction.md)、MATH_SPEC 和 C198/T182 声明清单。声明、scope、依赖和基线与 manifest 一致。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 与本 Agent 已读的 T179 版本逐字节一致，沿用其独立验收协议。未来 FiniteCellStrongConvergence 等草稿及动态 root/audit 不属于本次审查。

实际对照 `paper/main.tex:2300–2318` 的原对偶单元、`eq:conv-data-fd` 中 b_i^n 的时间—空间平均、E_h 的单元常数及未覆盖条带零值；另读 `paper/main.tex:2907–2926` 的完整分片势、原 L∞ 界、`eq:conv-potential-consistency` 及紧接其后的精确配对。原文要求的配对是 `(V_h^n z,w)_X=(b_h,dt E_hz,E_hw)_H`，不能用 P1 重构 R_h 或普通节点 sup 内积替代。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与已审版本不变。本批证明原分片对象及该配对，尚未证明紧邻的强收敛极限式。

## 全部 25 项声明

源码相对于 `Carleman/`；raw 行为本次固定完整类型产物中的起始行。顺序与固定 manifest 和台账一致。

| 序号 | 完整声明 | 固定源码 / raw 行 | 判定与实际内容 |
| --- | --- | --- | --- |
| 1 | `Carleman.finiteCellFunction` | `Spatial/FiniteCellMultiplier.lean:16` / 34602 | PASS；真实有限标量指示和。 |
| 2 | `Carleman.finiteCellFunction_on_cell` | 同文件:19 / 34604 | PASS；单元内精确等于同一系数。 |
| 3 | `Carleman.finiteCellFunction_zero_outside` | 同文件:28 / 34608 | PASS；整个未覆盖区逐点为零。 |
| 4 | `Carleman.finiteCellFunction_bound` | 同文件:35 / 34611 | PASS；保留原 B，不乘单元数。 |
| 5 | `Carleman.finiteCellMultiplier` | 同文件:45 / 34615 | PASS；真实可测有界乘子。 |
| 6 | `Carleman.finiteCellMultiplier_commute` | 同文件:56 / 34625 | PASS；L² 乘法与实际 E 重构严格交换。 |
| 7 | `Carleman.finiteCellMultiplier_pairing` | 同文件:75 / 34632 | PASS；连续 L² 配对等于物理质量配对。 |
| 8 | `Carleman.cartesianReconstructedPotential` | `Control/CartesianPotentialReconstruction.lean:16` / 34641 | PASS；原 b_i^n 的空间单元势。 |
| 9 | `Carleman.cartesianReconstructedPotential_bound` | 同文件:22 / 34653 | PASS；实际 bound 字段仍为 b.bound。 |
| 10 | `Carleman.cartesianReconstructedPotential_on_cell` | 同文件:25 / 34661 | PASS；原 dt·∏δ 归一化双积分。 |
| 11 | `Carleman.cartesianReconstructedPotential_zero_outside` | 同文件:34 / 34674 | PASS；真实未覆盖空间区域为零。 |
| 12 | `Carleman.cartesianReconstructedPotential_commute` | 同文件:39 / 34683 | PASS；同一原物理节点乘法与 E_h 交换。 |
| 13 | `Carleman.cartesianReconstructedPotential_pairing` | 同文件:44 / 34694 | PASS；原全部独立 z、w 的精确势配对。 |
| 14 | `Carleman.cartesianSpacetimeCell` | `Geometry/CartesianSpacetimeCells.lean:13` / 34706 | PASS；真实半开时间单元×空间对偶单元。 |
| 15 | `Carleman.cartesianSpacetimeCell_measurable` | 同文件:17 / 34713 | PASS；实际乘积集合可测。 |
| 16 | `Carleman.cartesianSpacetimeCell_disjoint` | 同文件:21 / 34716 | PASS；全部不同时间—节点索引两两不交。 |
| 17 | `Carleman.cartesianSpacetimeCell_restrict_volume` | 同文件:32 / 34722 | PASS；实际乘积限制测度质量恰为 dt·∏δ。 |
| 18 | `Carleman.cartesianSpacetimePotential` | `Control/CartesianSpacetimePotential.lean:16` / 34730 | PASS；同一平均系数的完整时空势。 |
| 19 | `Carleman.cartesianSpacetimePotential_bound` | 同文件:23 / 34742 | PASS；完整势保留同一 b.bound。 |
| 20 | `Carleman.cartesianSpacetimePotential_on_cell` | 同文件:25 / 34750 | PASS；时空单元内为同一 b_i^n。 |
| 21 | `Carleman.cartesianSpacetimePotential_zero_outside` | 同文件:30 / 34760 | PASS；完整时空未覆盖区为零。 |
| 22 | `Carleman.cartesianAveragedPotential_product_formula` | 同文件:36 / 34769 | PASS；原迭代平均等于真实乘积单元平均。 |
| 23 | `Carleman.cartesianSpacetimePotential_on_time_cell` | 同文件:48 / 34784 | PASS；每个时间单元的完整空间截面身份。 |
| 24 | `Carleman.cartesianSpacetimeCellIsometry` | 同文件:63 / 34796 | PASS；真实时空 L² 指示重构等距。 |
| 25 | `Carleman.cartesianSpacetimeCellIsometry_adjoint_average` | 同文件:72 / 34806 | PASS；对任意时空 L² 数据的实际伴随平均。 |

## 单元乘子、a.e. 身份与物理质量

`finiteCellFunction K c` 的实际值是 Σ_i 1_Ki c_i。第 2 项通过单元真正不交消去其余项，第 3 项在并集外使每项为零，第 4 项据这两种情况保持 |value|≤B。系数可混合正负；不要求 B>0、指标非空、覆盖全域或等体积。前四项的实际类型甚至不需要测度结构，第 5 项才使用各 K_i 可测构造 AEStronglyMeasurable 的有限指示和及相同 B 的 a.e. 界；该乘子定义本身不要求 ν 有限。

重新读取固定 `WeightedL2`：BoundedMultiplier 保存实际函数、AEStronglyMeasurable 和 a.e. 绝对值界；map 用该界内部证明乘法后的 MemLp，再取真正 L² 等价类。map_ae 才把此类识别为 value·u，不在任意 L² 类上断言不合法的逐点相等。第 6 项在 ν 有限时同步取得 map_ae 与两份 finiteCellLinear_ae，通过 Lp.ext 证明 **bhat.map(Ef)=E(c f)**：单元内两边为 c_i f_i，并集外两边为零。目标交换身份没有被列作输入。

第 7 项额外使用 ν(K_i)=mass>0，此时原有限物理空间内积为 **mass·Σ_i f_i z_i**，E 的真实等距性来自相同单元积分。先用交换式，再用 finiteCellLinear_inner，得到严格相等。第 13 项实例化 mass=∏δ_j、原完整 CartesianPhysicalState、实际 cartesianCellIsometry 和同一 PhysicalFiniteSpace.multiplier；z、w 独立任取，未缩小到连续采样数据、PDE 解或特定测试。将内积展开即原 **∫Ω bhat(E_hz)(E_hw)=(∏δ)Σ b_i z_i w_i**，没有遗漏质量、引入未知等价常数或把 E_h 换为 R_h。乘法结果为 L²，故其与 E_hw 的内积为真实合法 L² 配对。

## 原 a.e. 势与逐步重构

本批输入 b 是 `(volume|(0,T]).prod(volume|Ω)` 上任意实际 BoundedMultiplier。原实 L∞ 势有这样的 a.e. 可测有界代表；没有输入点态连续、光滑、时间周期性或处处有界。重新读取 T176 的 TimeCellAverage、BoundedMultiplierAverage 和 CartesianAveragedPotential：先沿真实限制测度缩小到时间单元，再以 dt 归一化，随后在实际 D_a 上以 ∏δ 归一化，得到原 b_a^{i+1}。正质量来自 g.dt_pos 与每个 δ_j>0，不是外加抽象体积假设。

T176 的真实 Fubini/平均界证明仍在本批固定依赖中；它给所有实际平均系数 |b_a^{i+1}|≤b.bound。第 8 项直接使用这些系数构造空间势，未另选一份同界函数。第 10 项单元内值为 **(dt·∏δ)⁻¹∫_(i dt,(i+1)dt]∫_D_a b**；第 11 项在包括原边界条带的整个单元并补集为零。b.bound≤M 时这些界立即给原 M；B=M=0 允许。第 9、19 项是保存的 bound 字段等于原 b.bound，配合构造中的 bounded 证明给真正 L∞ 上界，未声称实际本质上确界必须等于这个预算值。

原代表的零测修改也没有被采样放大：既有 cartesianAveragedPotential_congr 从原时空 a.e. 相等证明每个有限系数严格相同。本批指示重构只依赖这些系数，故得到同一值函数及乘法作用；不需要假设每个时刻的原势切片都处处有界或可积。不同 BoundedMultiplier 可携带不同上界字段，但这不影响其平均系数与实际乘法身份。

## 真实时空单元和完整截面

重新读取 TimeGrid、nodeTime、physicalTimeCell 及 T177 的不交/限制体积证明：steps>0、dt>0、T=steps·dt，实际时间单元为 **(i dt,(i+1)dt]**。这对应原 n=i+1；最后单元包含 T，相邻端点属于左侧单元，未通过周期 next 把终点改成 0。时间 0 的端点差异仅为 Lebesgue 零测，b 本身没有周期假设。

第 14 项的单元不是抽象标签，而是该真实时间集合与原开对偶盒 D_a 的笛卡尔积。第 16 项对不同 (i,a)、(j,c)，若 i≠j 用真实时间不交，否则用空间不交；相邻端点亦包含在这份证明中。第 17 项用固定 mathlib 的真实 measureReal_prod_prod，结合两个限制体积分别为 dt、∏δ，得到 **dt·∏δ**。各因子测度有限，实际实数测度没有隐藏的 ∞ 转换。

第 18 项以整个有限积指标 `(Fin steps × CartesianInteriorIndex N)` 及同一组 cartesianAveragedPotential 系数构造完整分片势。第 20、21 项是这个具体代表的逐点身份；空间开单元共享边界及未覆盖条带上的选择为零。没有因为边界零测而错误宣称空间单元覆盖原域。

第 23 项对**每个** i、**每个** t∈该时间单元和**每个**空间 x，证明完整势截面恰等于第 8 项的空间势。在某空间单元内用乘积单元身份；空间单元并外两份势均严格为零。因此结合第 13 项，原精确势配对适用于完整 b_h,dt 在该时间单元的真实截面，而非仅对离散时间节点成立。

## Fubini 与真实时空 Hilbert 伴随

第 22 项从已经确认的原双重平均公式出发。原空间盒和时间区间具有有限测度，BoundedMultiplier.integrable 用真实 a.e. 界及可积常数证明 b 在整个乘积域可积，故其在矩形单元上仍可积。固定 mathlib 的 setIntegral_prod 明确要求这个 IntegrableOn，实际证明以 b.integrable.restrict 供应；没有对任意不可积函数直接交换积分。

Fubini 先给真实乘积限制测度下的迭代积分；再用时间单元⊆(0,T]、D_a⊆Ω 以及各集合可测，逐一消去重复 restrict，严格回到原 Lebesgue 双积分。因此平均系数等于 **(dt·∏δ)⁻¹∫_(timecell×D_a) b d(μ×ν)**，乘积/迭代积分和归一化方向都正确。

第 24 项使用相同 product cells 构造 finiteCellIsometry，输入有限空间的质量确为 **dt·∏δ**，其范数平方因而为 dt·∏δ·Σ_(i,a) z_(i,a)²，输出是真正乘积测度 L²。正质量、可测性、不交性、实际体积均由本批或既有几何内部供应。第 25 项直接使用该真实等距映射的 Hilbert 伴随，对**任意原时空 L² u** 给出上述单元平均；它没有 b 参数或额外 L∞/连续性要求。底层伴随公式通过全部有限物理测试的内积身份识别，有限测度下 L² 单元积分合法，不是一个以同范数为特征另选的映射。

本批没有另声明完整分片势作为某个特定 toLp b 的 EE*b 等式或该 EE* 的极限定理；平均系数和代表身份已为这样的后续组合提供实际对象。不能把这一基础自动记作原 `eq:conv-potential-consistency` 的强收敛。

## 量词、退化情形与剩余范围

结论对所有维数 d、任意位置 o、正步长 δ、全部 N、所有合法 TimeGrid、全部原有界势及完整物理状态成立。没有细化条件、时间空间耦合、网格形状常数、频率过滤或离散方程假设。界使用同一 b.bound，配对和等距常数恰为 1，不依赖 T、dt、空间节点数或长宽比。

空内部索引合法：有限指示和、空间/时空状态空间相应为零，未覆盖区域上仍为零，带指定节点的定理自然无实例；没有偷偷选取一个不存在的节点。若某 N_j=0，原盒为空，也未造成除零，因为除数仍是正 dt 与正步长的乘积。d=0 时空间空乘积为 1、空间模型为单点，时空部分退化为真实时间平均；无需除以 d。steps=1 合法，steps=0 不在原合法 TimeGrid 范围内。

本阶段完成原时空势的构造、保界、精确配对和平均伴随，未声称平均势强收敛、状态紧性、测试一致性、极限弱方程、初终值或连续 null control。也没有把原 L∞ 数据增加为光滑类。结论范围与 AUXILIARY 规格一致，覆盖保持 17/26。

## 固定依赖、公理和构建

独立递归解析四入口的 Carleman 导入闭包共 **336** 模块，除四新增模块外 **332** 个与 mathematical_base 逐字节不变。关键接受版本的完整闭包另行比较：

| 入口 / 已接受阶段 | 固定接受版本 | 闭包数 / 比较 |
| --- | --- | --- |
| CartesianCellReconstruction / T175 | `7c2ceacf62d42b168879106b8c6d6fc246c45794` | 326 / 全部相同 |
| CartesianAveragedPotential / T176 | `ef4e3f83320e3a2d4cc7a074a1df996c13bd9d52` | 331 / 全部相同 |
| TimeCellReconstruction / T177 | `d1134c0ccc8f343aef6223f304fe52f86a7aff1d` | 23 / 全部相同 |

已读 [T175 报告](T175-local-acceptance.md)、本 Agent 已签发的 [T176 报告](T176-local-acceptance.md)，本次完整读取 [T177 报告](T177-local-acceptance.md)；分别冻结在 `8a921065b09fe7082c4ef5d1163e9925f3f98709`、`47fcf88f7bc34bebea05f6ae285efc85aeaeef2b`、`923f74e8dc1e4b64967bdc10ba8248aa71dd96e9`，工作区字节仍与各冻结提交相同。以上实际实现亦重新核对，不只依赖历史 PASS。

固定 Carleman.lean 导入四模块，固定 tools/CheckAxioms.lean 对25项均执行 #check @ 和 #print axioms。新源码无 sorry、admit、axiom 或 native_decide。25项公理依赖均只有 `propext, Classical.choice, Quot.sound`。独立解析完整 raw 的 **3226** 条显式记录、**3222** 个不同名字，含 **9** 条无公理记录；白名单外依赖为零。实际 auditor 对所有 Carleman 常量运行递归 collectAxioms，raw 末行确认 **8352 项 PASS**；空 stderr 不作为成功证据。

实际读取 `/tmp/carleman-t182-potential-pairing-target.log` 的 **3524 jobs**、`/tmp/carleman-t182-full-potential-target2.log` 的 **3527 jobs** 和 `/tmp/carleman-t182-potential-reconstruction-build.log` 的根目标 **4134 jobs** 全部成功。Lean pin v4.35.0，正式 CI compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 和本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿、工具链、manifest、lean workflow、tools/lean_ci.sh 与已读 T179 版本不变。新用乘积实测度与 Fubini 的实际定理类型/证明已从该固定 mathlib 核对。

## 独立同 SHA CI 与自行下载工件

本 Agent 自行访问实际 GitHub run/jobs/artifacts API，并独立执行两次 gh run download，两命令均 exit 0；未以执行者的 root 下载替代取证。曾见 lean 运行及缓存收尾，待全部三项最终成功后签发。

- run: [39274456878 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39274456878/attempts/1)，event=push、branch=main、head_sha 精确为 checked_sha；最终 **completed/success**，updated_at=`2026-10-19T15:07:07Z`。
- state-check **118135004275**、lean **118135004984**、dashboard / snapshot **118137144154**：实际全部 **completed/success**。
- `lean-ci-result` artifact **12198025091**，ZIP **491 bytes**，API digest `sha256:183ad0287224bce49c69dc768bfa3b8b86f938c83eab2991b16ac44e6dfba691`。
- `lean-declaration-evidence` artifact **12196273406**，ZIP **246405 bytes**，API digest `sha256:2928e2109110e0ed7b6ef5eab5e81fcb4b454a49c91702b2c671eec3af686924`。

两个 artifact 的 workflow_run 均绑定同一精确 SHA、main 和该 run。独立 `/tmp/carleman-t182-potential-reconstruction-main-ci/result.json` 为 **537 bytes**，SHA256=`5ce8d15e492e2a3aebd51940659335064ba1a12f59756581afc0ad1ff72c43af`；实际 status=PASS、checked_sha=source_head_sha=`ffa5a6f8061e5b13aa96a7f77081aa4f8482e2e5`、targets=[Carleman]、finished_at=`2026-10-19T15:05:44.564027+00:00`，ci_url、Lean 和 mathlib 与实际记录相符。

独立 `/tmp/carleman-t182-potential-reconstruction-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t182-potential-reconstruction-local-axioms.txt` **逐字节完全一致**，均为 **2664379 bytes**，SHA256 **`6aa79980d546914974dcd87664f7ca8f5bb88f76213b9de9903ab509755b4a84`**。实际远端25项完整类型、公理名单及末行8352项成功均重新核对；ZIP digest 和解包 raw hash 分别记录。

## 最终结论

**25/25 PASS，无需修复。** 同一原平均系数供给真实空间/时空分片势，保留原 L∞ 预算；实际 E_h 与原物理节点乘法交换，原质量内积配对严格成立；真实乘积单元质量和 Fubini 确认时空平均，实际 Hilbert 伴随覆盖任意时空 L² 数据。C198 可登记 **AUXILIARY/REVIEWED**，覆盖保持 **17/26**。仅本报告单文件提交，不 push，不改数学、原稿或台账；通知后 reviewed_at 与正文冻结。
