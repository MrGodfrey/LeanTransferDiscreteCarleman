# T105 / C121 独立本机验收

- `checked_sha`: `2f2e71d4359a206ac9035d73b61889bfa3cb7bfb`
- `base_commit`: `29ebd0b76cccb70d6da4499eaa09d35cab2895ff`
- `reviewed_at`: `2026-10-19T03:35:56+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**；原 FD 观察节点、真实限制/零延拓的物理配对，以及原 `eq:observationinterface` 的全允许权统一估计。完整 FD 数值接口及 P012 不在本次完成范围，原文保持 **14/26**。

独立以 `git show` 读取固定提交三个新模块的全部证明、15 项实际完整展开类型、规格 `governance/analysis/T105-fd-observation.md` 和关键依赖，对照原 `paper/main.tex` 的 N5（466–469）、Section 6 原物理节点/控制空间（1634–1667）、`prop:fd`（1672–1676）及 Appendix B Step 3（2878–2889）。执行者说明和 CI 没有代替语义核验。本验收自行查询实际同 SHA main CI，并自行下载、读取和逐字节比较同 run 两份原始产物。工作树后续的物理 Hilbert 空间模块未混入本次范围。

## 全部 15 项声明

名称均省略公共前缀 `Carleman.`；位置相对于固定提交的 `Carleman/`。名单与交付 JSON、固定 C121 和 T105 台账逐项一致。

| # | 声明 | 固定位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `cartesianObservedState` | `Spatial/CartesianObservationLocalization.lean:16` | PASS；原全内部节点状态乘以真实观察区域的节点指示值，是已有实际节点乘子的实例。 |
| 2 | `cartesianObservedState_apply` | `Spatial/CartesianObservationLocalization.lean:21` | PASS；实际节点在 ω 内保留原值，在 ω 外严格为零。 |
| 3 | `cartesianKuhnHat_support_dist` | `Spatial/CartesianObservationLocalization.lean:29` | PASS；实际非零帽函数的节点与点属于同一真实闭 Kuhn 单元，距离不超过 d h。 |
| 4 | `cartesianKuhnReconstruction_observed_eq` | `Spatial/CartesianObservationLocalization.lean:45` | PASS；原紧包含内部供应正 h₀，先于全部网格和状态；ω₀ 上原重构与筛选节点重构逐点相等。 |
| 5 | `CartesianObservationIndex` | `Spatial/CartesianNodalControl.lean:14` | PASS；控制指标确为实际内部节点落在 ω 中的子类型。 |
| 6 | `cartesianControlRestriction` | `Spatial/CartesianNodalControl.lean:18` | PASS；全状态至全部控制节点的真实线性限制。 |
| 7 | `cartesianControlExtension` | `Spatial/CartesianNodalControl.lean:25` | PASS；全部控制节点数据至全状态的真实线性零延拓。 |
| 8 | `cartesianControlPhysicalInner` | `Spatial/CartesianNodalControl.lean:38` | PASS；原物理质量 ∏δ_j 乘控制指标上的独立双线性配对。 |
| 9 | `cartesianControlWeightedSq` | `Spatial/CartesianNodalControl.lean:44` | PASS；同一物理质量乘实际节点权值与控制数据乘积的平方和。 |
| 10 | `cartesianControlRestriction_extension` | `Spatial/CartesianNodalControl.lean:51` | PASS；先零延拓再限制，对全部控制数据严格等于恒等。 |
| 11 | `cartesianControlExtension_restriction` | `Spatial/CartesianNodalControl.lean:58` | PASS；先限制再延拓，严格等于第 1 项实际观察节点指示乘子。 |
| 12 | `cartesianControlExtension_pairing` | `Spatial/CartesianNodalControl.lean:67` | PASS；对任意独立 v、f 证明原物理配对的 B/B* 伴随身份。 |
| 13 | `cartesianObservedState_weighted_energy` | `Spatial/CartesianNodalControl.lean:91` | PASS；筛选后全节点加权能量严格等于限制后控制节点加权平方和。 |
| 14 | `cartesianKuhnReconstructionLp_observed_eq` | `Spatial/AllowedCartesianObservation.lean:15` | PASS；逐点区域身份与真实重构 L² 代表的 a.e. 身份给区域指示乘子后的 L² 类相等。 |
| 15 | `allowed_weight_cartesian_observation` | `Spatial/AllowedCartesianObservation.lean:35` | PASS；内部供应几何局部性及全允许权质量估计，得到原真实观察范数对控制节点加权平方根的统一界。 |

## 真实支撑、距离与观察局部化

`cartesianKuhnHat_support_subset` 的支撑是真实帽函数非零点的集合，其目标是真实有限闭节点星。第 3 项从该并集成员取得一个实际单元，同时取得该节点是单元顶点；用顶点属于真实凸包及已有 `cartesianKuhnSimplex_dist_le` 得到节点到点的距离 ≤d h。这里只用每个正坐标步长 δ_j≤h，没有把目标局部性、单元邻近性或最终观察估计作为前提。

第 4 项对固定紧集 closure ω₀ 和开集 ω 使用真实闭邻域包含定理，得到 r>0 及 `cthickening r (closure ω₀) ⊆ ω`，然后取 h₀=r/(d+1)。在任意 x∈ω₀ 处，若一个 ω 外节点的帽函数非零，则节点到 x 的距离 ≤d h≤r，从而该节点属于上述闭邻域，矛盾。因此每个被筛去节点在 x 处的帽函数实际为零，有限和逐项相等。论证覆盖全部原状态 f，没有预先要求 f 的支撑位于 ω。

分母 d+1 始终为正；证明没有除以 d、节点个数、控制集合大小或观察集合测度。空 ω₀、没有控制节点、某方向无内部节点及退化空索引均由真实空和/空命题覆盖。原论文 d≥1、N_j≥2、δ_j>0、h=max δ_j 的网格直接满足所用条件。此观察步骤不需要额外的步长下界或互相比常数。

## 原控制空间与精确物理伴随配对

完整状态是 `CartesianInteriorIndex N → ℝ`，每个方向的 `Fin (N_j-1)` 通过 a_j+1 对应原内部指标 1,…,N_j−1。控制空间保留其中实际物理点属于 ω 的所有指标，无光滑状态或较小子空间限制。B 为零延拓，B* 为限制，两个组成身份方向均正确。

第 12 项先将完整节点和限制到 ω 内指标，因为其补集上的零延拓为零，再使用 `Finset.sum_subtype` 转为真实控制指标和。两侧使用完全相同的质量 m_δ=∏δ_j，结论针对任意独立 v 与 f：`(Bv,f)_X=(v,B*f)_U`，并非只检查对角二次型。正步长保证 m_δ>0；原内积没有被未加权有限函数空间内积替代。

控制加权平方范数精确为 `m_δ Σ_{a:x_a∈ω}(σ(x_a)v_a)²`，与原 `Σ ω_a σ(x_a)² v_a²` 相同。第 13 项证明它恰是 B B* f 的全节点加权能量，未使用上界代替等式，也没有把右侧扩大为全节点 f 的范数。

本批形式化对象是实际线性映射和精确物理配对公式；尚未安装采用此物理内积的 `InnerProductSpace`/Hilbert 包装并把 B* 表达为该包装上的 `ContinuousLinearMap.adjoint`。上述公式正是原代数伴随身份，足以完成本批观察估计；报告不把后续物理 Hilbert/通用接口装配宣称已经完成。

## 实际区域 L²、允许权及统一量词

第 14 项不是任意代表上的形式代换：证明同时使用两份 `cartesianKuhnReconstructionLp_ae` 和两份真实 cutoff 乘法的 `map_ae`，再用 `Lp.ext`。ω₀ 内使用实际逐点重构相等，ω₀ 外指示系数为零。ω₀ 的可测性是构造真实指示乘子所需的明确前提，原开放观察域满足它。

已有 `BoundedMultiplier.observation` 定义为真实加权 L² 半范数与区域指示乘子的复合，`observation_sq_integral` 精确给出 `observation²=∫_{ω₀}|σ|²|u|² dν`。本批 ν 是物理盒 Ω_g 上的 Lebesgue 限制，故一般型结论对应 Ω_g∩ω₀ 的真实积分；原情形 ω₀⊆Ω=Ω_g 时恰为原 L²(ω₀) 范数。这里使用 ambient L² 的实际 cutoff 表达区域范数，不将它误称为本批新建了原生 `Lp (volume.restrict ω₀)` 空间。

第 15 项固定 d、开凸 S、紧 closure S、实际轮廓 ρ 及其闭包 C¹ 性、两观察区域，然后先选择 h₀>0、C>0；之后才量化全部原点 o、正步长 δ、N、Ω_g⊆S、h、TimeWeight w、实幂 τ、时刻 t、符号 η 和全部状态 f。原矩形域可取 S=Ω_g，原闭包光滑轮廓供应这里较弱的 C¹ 前提，原观察域紧包含供应全部几何前提。

实际 σ 为 `(ρ.scaled η).multiplier w τ t` 在 Ω_g 上的真实限制，即原 `q(t)^τ exp(ηρ(x)q(t))`。条件 abs η=1 同时覆盖两符号；τ 甚至可为任意实数，故包含原有界允许幂族。C 不依赖网格、节点数、周期、qmax、τ、t、η 或状态。

已直接读取 C108 质量比较的证明：真实闭包 C¹ 界与凸性内部给轮廓 Lipschitz 常数 L，真实闭单元直径及 hq(t)≤1 给权比 W=exp(Ld)，q(t)^τ 精确抵消。其常数 C₀=W⁴(d+2) 在全部网格与权之前选择；比较包含真实节点值及闭单元点，不是仅用 a.e. 轮廓界控制节点。最终调用其上界分量 `.2.1` 于同一个 g=B B* f，结合观察范数≤全域加权范数、区域 L² 身份和第 13 项精确能量身份，再利用非负性及真实平方根，得到 C=√C₀ 的所需界。未输入最终估计作为假设。

最终 Lean 类型明确保留 h≤h₀ 与 hq(t)≤1 两项条件，并没有在这 15 项中另封装单一 qmax 条件的推论。原 δ_num=min(h₀,1)>0、qmax≥1、q(t)≤qmax 和 hqmax≤δ_num 直接给出 `h≤hqmax≤h₀` 及 `hq(t)≤hqmax≤1`。因此没有新增原数值允许权族以外的独立限制，h₀ 和 C 的量词也保持原统一性；将此转换和所有数值对象一起装入完整 FD 接口仍是后续义务。

## 依赖和范围边界

固定三模块的 Carleman 导入闭包共 309 文件，其中 306 个既有文件相对本批基线逐字节不变。三个新模块均已由固定 `Carleman.lean` 导入。进一步比较关键依赖的整个 Carleman 导入闭包，而非仅比较主声明名称：

- 帽函数与真实支撑的 140 文件闭包，与 [T087 验收](T087-local-acceptance.md) 的 `7b2627620e04ad9b44e6bee31fab8a241d4f4d1a` 完全相同。
- 实际节点乘子/允许对角测试的 306 文件闭包，与 [T101 验收](T101-local-acceptance.md) 的 `88306d8177aee83bfc8c6011f9d964a273e042b9` 完全相同。
- 允许权质量比较的 252 文件闭包，与 [T092 验收](T092-local-acceptance.md) 的 `1c3da9ffc54b5624f27760db5368aa05cbdfc0a5` 完全相同。
- 真实区域观察范数的 23 文件闭包，与已验收 Section 3 版本 `a315bdc449c58a705a982f0d009f1dde24d6af66` 完全相同；本次仍直接检查其 cutoff、平方积分及收缩证明如何被调用。

原稿逐字节未改，SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本批没有依赖后续未提交物理空间模块，没有把观察估计扩展声称为已完成全部 N1–N5、完整 FD/P012 或全局连续 Carleman 供应。对本次辅助目标，未发现额外未清偿数学前提或阻断性缺陷。

## 本机与真实同 SHA 远端证据

本机 `/tmp/carleman-fd-observation-full.log` 实际记录 `Build completed successfully (3818 jobs).`，并完整打印本批类型和 6321 声明递归公理审计成功。规格记录定向 3500 jobs；本次约定目录没有独立 target 日志，因此不将该数字另称为已独立复核的日志结果。全库日志和同 SHA 远端 `Carleman` 构建已经覆盖三个模块。

独立查询 [main CI run 39194940847 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39194940847/attempts/1)：head 为本次固定 SHA，分支 main，最终 `completed/success`，更新于 `2026-10-19T03:35:12Z`。三项均有实际最终成功记录：

| Job | ID | 最终结论 | 完成时间 UTC |
|---|---|---|---|
| state-check | 117875581625 | success | 2026-10-19T03:29:50Z |
| lean | 117875581844 | success | 2026-10-19T03:35:01Z |
| dashboard / snapshot | 117876877801 | success | 2026-10-19T03:35:11Z |

自行下载的同 run artifact `lean-ci-result` ID 为 **12161192774**；其原始 `/tmp/carleman-fd-observation-main-ci/result.json` 为 PASS，`checked_sha=source_head_sha=2f2e71d4359a206ac9035d73b61889bfa3cb7bfb`，目标 `Carleman`，`finished_at=2026-10-19T03:32:50.819269+00:00`，CI URL 与上述 run/attempt 精确一致。

自行下载的 `lean-declaration-evidence` artifact ID 为 **12161382078**；其原始 `/tmp/carleman-fd-observation-main-axioms/axioms.txt` 与固定 `/tmp/carleman-fd-observation-local-axioms.txt` **逐字节相同**：**1,898,406 bytes**，SHA256 **`b035b1e8efe524f70197bcd06f5a942cb4a61185902315a51125e7a24ceee7f7`**。两 artifact 的 workflow_run 元数据也指向同一 main/head/run，未拼接其他提交证据。

15 项每项恰有一份完整类型和对应公理记录，均仅使用 `propext`、`Classical.choice`、`Quot.sound`。全产物有 2132 条非空公理打印及 8 条无公理打印，共 2136 个不同显式打印名称；这些显式记录数与包含生成声明的 **6321** 项实际递归审计是不同计数。已检查固定 `CheckAxioms.lean` 的实际遍历器：对全部 Carleman 命名空间常量执行 `collectAxioms`，拒绝上述三项之外的公理。其逻辑相对基线未改，本批只增加 15 对类型/公理打印。未见 sorryAx 或额外数学公理。

原始结果记录 Lean **4.35.0**、mathlib **`56a005855ea17e0b0958f73ec801ae140b0a1679`**；与固定工具链及 manifest 一致。本机 mathlib HEAD 相同且工作树干净。没有因主执行者后续工作树变化重新解释此固定版本的证据。

## 验收决定

**C121 可升为 REVIEWED / AUXILIARY。** 原观察区域局部化、全部真实控制节点上的限制/零延拓物理配对、实际区域 L² 身份和原全允许权统一观察估计均通过。未发现本批固定版本需要修复的数学缺陷；完整物理 Hilbert/数值接口组装仍待，不提升 P012，原文覆盖保持 **14/26**。本报告定稿后不再刷新验收时间。
