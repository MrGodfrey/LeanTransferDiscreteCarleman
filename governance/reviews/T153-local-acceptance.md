# T153 / C169 独立本机验收：真实时间反射与同常数双方向估计

- checked_sha / source_sha：`7a2da98bcead43801f48dc03ecffbc70adc7585e`
- mathematical_base：`86686ea4d106798727d898bf61abc238812a8cb8`
- reviewed_at：`2026-10-19T10:51:05+00:00`
- reviewer：独立本机 Agent `/root/accept_spatial_lemma`，未参与本批实现。
- result：**PASS**；axiom_check：**PASS**；全部 **14/14** 显式声明通过。
- scope：**AUXILIARY — C∞ 周期坐标盒的双方向估计**。C169 可登记 REVIEWED；**P024 / prop:continuousCE 不提升，原文覆盖保持 17/26**。

直接从固定 Git 对象读取两个模块的全部定义和证明、14 项完整展开类型、原稿、相关依赖、T153 分析、MATH_SPEC、固定台账和治理协议。独立查询同 SHA 的正式 main CI 及三个实际 job，自行下载同次原始 result / axioms，并与固定本机产物逐字节比较。规格、执行者说明、既有报告和 CI 未替代数学审查；动态 `.ci/axioms.txt`、后续 TemporalMollification 等草稿均排除。仅新增并单独提交本报告，不改实现、根导入、审计、台账或原稿，不 push；签发通知后冻结内容与时间。

## 原文定位和范围

核对固定 `paper/main.tex:292–299` 的原 C² 闭区间 qclass 和匹配端点、`374–381` 的 Pε=ε∂t+A 及真实加权范数、`2672–2733` 的 `prop:continuousCE` 与证明。对 Dirichlet A=−Δ，原负向算子为 **−∂t−Δ**；时间反射不能把整个正向热算子乘以负号。本批直接清偿 `2730` 所述时间反射在已经得到的光滑周期盒估计中的实际实现。

固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未改原命题。最终声明包括所有正坐标盒（维数 d+1≥1）、任意非空开 W⊆Ω、全部全时空 C∞ 周期 q/u 和逐点零边界状态，使用真实权 θ=exp(qρ)、真实空间梯度、真实热残差和真实观察积分。W 的相对紧包含不是附加前提；原 ω₀⊂⊂Ω 在该 W 范围内。

该声明仍比原全文命题窄：要求全局 C∞ 时间权、全时空 C∞ 周期状态、所有时刻 frontier 上逐点零值，且仅处理坐标盒。原 C²([0,T]) 时间权与匹配到二阶端点、全部 H¹_tL²_x∩L²_tD(A) 周期弱轨道及一般凸多面体没有由本批恢复。AUXILIARY 的 PASS 或台账 `extra_hypotheses=[]` 不能消除这些明确的范围限制。

## 十四项实际声明

清单名称及顺序与固定 C169 / T153、`/tmp/carleman-t153-smooth-heat-both-signs-declarations.json` 完全一致。下表路径前缀为 `Carleman/Spatial/`，行号均指 checked_sha；所有项已核对实际完整类型和证明。

| # | 完整声明 | 固定源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `Carleman.heatTimeReflection` | `HeatTimeReflection.lean:13` | PASS。真实映射 R_T(t,x)=(T−t,x)，空间坐标完全不变。 |
| 2 | `Carleman.heatTimeReflection_contDiff` | `HeatTimeReflection.lean:16` | PASS。真实 fst/snd 和仿射减法的乘积给全空间 C∞，未预设反射后状态光滑。 |
| 3 | `Carleman.heatTimeReflection_involutive` | `HeatTimeReflection.lean:19` | PASS。实际两次反射严格等于原点，保证真正可逆而非仅几乎处处映射。 |
| 4 | `Carleman.time_reflection_mem_interval` | `HeatTimeReflection.lean:23` | PASS。从 0≤t≤T 推出 0≤T−t≤T，端点交换而非丢弃。 |
| 5 | `Carleman.heatTimeReflection_periodic` | `HeatTimeReflection.lean:26` | PASS。R_T(tx+(T,0))=R_T(tx)−(T,0)，用原周期性的负平移身份得到反射状态仍以 (T,0) 为周期。 |
| 6 | `Carleman.time_reflection_measurePreserving` | `HeatTimeReflection.lean:34` | PASS。真实 Lebesgue 反射保测与 [0,T] 的精确逆像身份，给同一受限时间测度保持；没有附加 T 因子。 |
| 7 | `Carleman.heatTimeReflection_measurePreserving` | `HeatTimeReflection.lean:43` | PASS。与空间恒等映射取真实乘积，保持实际 `(volume.restrict [0,T]).prod (volume.restrict Ω)`。 |
| 8 | `Carleman.boxTimeIntegral_reflection` | `HeatTimeReflection.lean:49` | PASS。由真实可测自反双射及 MeasurePreserving.integral_comp，严格得到任意被积函数的实际柱积分换元。 |
| 9 | `Carleman.deriv_time_reflection` | `HeatTimeReflection.lean:56` | PASS。真实 HasDerivAt 复合 t↦T−t 给 (q∘r_T)′(t)=−q′(T−t)。 |
| 10 | `Carleman.deriv_deriv_time_reflection` | `HeatTimeReflection.lean:63` | PASS。先建立全函数一阶导数身份，再对真实 q′ 的复合求导，两负号抵消，得到 q″(T−t)。 |
| 11 | `Carleman.spaceTimeHeat_time_reflection` | `HeatTimeReflection.lean:74` | PASS。真实时空函数的时间切片链式法则给 −u_t(T−t,x)，空间切片仍为 u(T−t,·)，得到 −u_t−Δu。 |
| 12 | `Carleman.spaceTimeOrientedHeat` | `BoxSmoothHeatBothSigns.lean:13` | PASS。定义为 ε 乘真实时间 deriv 减真实 spatialLaplacian，准确对应原 Pε=ε∂t−Δ。 |
| 13 | `Carleman.spaceTimeHeat_time_reflection_eq` | `BoxSmoothHeatBothSigns.lean:17` | PASS。全函数身份 `P₊(u∘R_T)=(P₋u)∘R_T`；没有将空间 Laplacian 符号一并反转。 |
| 14 | `Carleman.box_smooth_gaussian_heat_both_signs` | `BoxSmoothHeatBothSigns.lean:25` | PASS。同一次选定 c/λ/β/qc/C 后才量化 T/q/ε/u；正向直接调用既有估计，负向内部供应全部反射资格并对四个原积分换元，指数 (3,1;3) 与原观察区域完整保持。 |

## 关键数学核对

**实际保测和可逆性。** `time_reflection_measurePreserving` 使用的是 Lebesgue 测度对减法映射 t↦T−t 的保测定理，再调用 `restrict_preimage`；源码通过双向实数不等式证明逆像恰为 Icc 0 T。两端都使用同一受限测度，没有把区间换成另一个长度。柱体保测使用该映射与空间恒等的 `MeasurePreserving.prod`，空间测度仍是原 openCoordinateBox 的受限 Lebesgue 测度。限制测度所需可测性、乘积所需 SFinite 均由实际 Lebesgue 数据供应。

积分步骤构造 `MeasurableEquiv.ofInvolutive`：R_T 全空间连续可测且自反，逆映射就是自身。核对固定 mathlib `MeasurePreserving.integral_comp` 的实际证明是 map_eq 和可测嵌入的 integral_map，合法给任意 f 的换元。此一般引理不需要可积性输入，并不意味着最终估计利用非可积时 Bochner 积分默认值：实际值项、梯度项和残差均由全 C∞ 数据在紧闭柱连续而可积；观察项由 W 开而可测，用 `continuous_box_observation_integrable` 保证可积。观察示性函数没有被误认为连续。

**时间权和周期。** 对 q_R(t)=q(T−t)，真实 HasDerivAt 复合给 q_R′=−q′∘r_T；二阶证明先以 funext 取得完整一阶导数函数等式，并由 `smoothD_contDiff hq 1` 得真实 q′ C∞，再求导得到 q_R″=q″∘r_T。这不是另设二阶导数字段或仅在一点替换后微分。区间不变性将 q≥qc、两个绝对值界分别保持为同一 qc、βq_R² 和 β²q_R³；abs_neg 只去掉一阶导数的符号，不改变原界。

q_R 的周期性由真实 `Function.Periodic.const_sub` 供应；u_R 的周期性由第 5 项供应。R_T 的 C∞ 与复合规则保证 u_R/q_R 光滑。原 `u(t,x)=0` 对每个实 t 及 frontier Ω 的全部 x 成立，反射只需取原时刻 T−t，所以边界条件内部保持；无需另给反射零边界或新迹条件。全局 C∞ 周期性本身也蕴含真实时间导数的匹配端点，未另外假定目标导数周期性。

**原算子和空间项。** 展开定义可独立得到

```text
P₊(u∘R_T)(t,x)
 = ∂t[u(T−t,x)] − Δx[u(T−t,x)]
 = −(∂tu)(T−t,x) − (Δxu)(T−t,x)
 = (P₋u)(R_T(t,x)).
```

空间切片 `y↦u_R(t,y)` 与 `y↦u(T−t,y)` 是同一实际函数，因而真实 gradient 和 spatialLaplacian 无符号或比例损失。反射权 L_R=q_Rρ 严格等于 L∘R_T，空间 profile ρ 和中心 c、λ 均保持。空间观察集是 `Prod.snd ⁻¹' W`，由于 R_T 的 snd 原样不变，观察示性函数与反射逐点相容；不需 W 的任何时间对称性。

**四个积分和同一常数。** 最终证明对固定原 q/u 定义 F₀=q³exp(L)²u²、F₁=q exp(L)²‖∇u‖²、R=(exp(L)P₋u)²、O=1_W F₀。先把反射正向不等式中的四项逐点严格识别为 F₀∘R_T、F₁∘R_T、R∘R_T、O∘R_T，再对它们各调用同一 `boxTimeIntegral_reflection`。因此返回后的右端确为原负向残差和同一原 W 观察项，左端为完整原状态值及全空间梯度；没有换权符号、遗漏状态、把整个残差改号或增添 Jacobian/T 系数。

参数顺序直接体现在完整展开类型及证明：先固定 d+1、a/b、W，调用 C168 得 **一次** `∃c,λ,β,qc,C`，保留 c∈W、λ≥1、0<β≤1、qc≥1、C>0 及全空间 −2<ρ≤−1，然后才 `intro T ... q ... ε ... u` 并按 ε=1/−1 分支。负向分支使用的正是已固定 `hforward`，没有重新调用存在性结论选择参数。原 qmax 未出现于常数；连续 q 在 [0,T] 上的有限上界自动存在，原 qclass 的这一部分不成为额外依赖。

辅助保测/换元定理对任意实 T、任意盒端点和自然数维数有效；T<0 时 Icc 0 T 为空，T=0 时受限时间 Lebesgue 测度为零。最终估计要求 T≥0、正盒以及 d+1≥1，包含原 T>0 和所有正维数盒；T=0 只给自然的零积分结论，未用于回避正时间情形。最终 [0,T] 与原 (0,T) 柱体积分仅相差时间 Lebesgue 零测端点。观察项经既有 `boxTimeIntegral_observation` 严格为 Ω∩W 的限制乘积积分，由 W⊆Ω 即得原观察柱。

## 依赖闭包、构建和公理

按固定 import 递归读取两个新模块共有 **129** 个 Carleman 源文件，其中 **127** 个旧文件与 mathematical_base 逐字节相同。正式依赖 C168 的 `BoxSmoothHeatEstimate.lean` **127 文件完整闭包**与已验收版本 `86686ea4d106798727d898bf61abc238812a8cb8` 全相同。已读取 [T152 独立验收报告](T152-local-acceptance.md)，并重新直接核查其最终正向声明及证明、实际 `boxTimeIntegral` 定义/有限柱可积性、真实观察限制积分，以及本批对这些接口的全部前提供应。依赖报告不能扩大本批正则性或几何范围。

两个模块均已由固定 `Carleman.lean` 导入，14 项各有固定 `tools/CheckAxioms.lean` 中 `#check @...` 与 `#print axioms ...`，并实际出现在同次远端 raw。固定目标日志 `/tmp/carleman-t153-both-signs-target2.log` 为 **3290 jobs** 成功，完整 `/tmp/carleman-t153-smooth-heat-both-signs-build.log` 为根目标 **4030 jobs** 成功；此处核验固定日志，不声称重新构建变动中的工作树。

Lean 固定为 4.35.0；远端编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。固定 lake manifest、实际干净的 mathlib checkout 和 CI result 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。实际读取该版本 `MeasurableEquiv.ofInvolutive`、`MeasurePreserving.restrict_preimage` / `prod` / `integral_comp`，确认它们对应真实受限/乘积测度和可测双射换元。

14 项各仅依赖正常基础公理 `propext`、`Classical.choice`、`Quot.sound`。全部显式打印记录为 2841 条标准基础公理依赖及 9 条无公理记录，没有未知公理；该打印数不与递归审计总数混同。固定审计器对全部 Carleman 常量（包括 privateToUserName）执行 collectAxioms，白名单仅上述三项；raw 实际末行是 **`Axiom audit passed for all 7588 Carleman declarations.`**。本批没有 sorry / admit / 新增 axiom 或未清偿数学占位。

## 独立实际 CI 与下载证据

独立通过 GitHub API 查询 [main run 39239955552 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39239955552/attempts/1)：最终整体 **completed/success**，head 精确为 checked_sha，分支 main。三个实际 job 的 head_sha 同样精确匹配：

| job | 实际 ID | 最终结论 | completed_at UTC |
|---|---|---|---|
| state-check | `118018079647` | completed / success | `2026-10-19T10:47:33Z` |
| lean | `118018079939` | completed / success | `2026-10-19T10:50:33Z` |
| dashboard / snapshot | `118019319884` | completed / success | `2026-10-19T10:50:44Z` |

本 Agent 实际执行两次 `gh run download 39239955552`，分别下载 lean-ci-result 与 lean-declaration-evidence；API 返回两者均属于该 run、main 和同一 proof SHA，未过期：

- result artifact **12181665318**（API 压缩大小 492 bytes）：`/tmp/carleman-t153-smooth-heat-both-signs-main-ci/result.json` 实际 **537 bytes**，SHA256 **`09c57eaaa5067ef2026c130b927f08fc5be7ba43bfa304fc5cde738208d5e616`**。内容 `status=PASS`，`checked_sha=source_head_sha=7a2da98bcead43801f48dc03ecffbc70adc7585e`，`targets=[Carleman]`，`finished_at=2026-10-19T10:49:27.182910+00:00`，ci_url 属于同次 attempt。该 result 产生早于 job 收尾，验收已另等到三个 job 最终成功。
- raw artifact **12181685162**（API 压缩大小 218777 bytes）：`/tmp/carleman-t153-smooth-heat-both-signs-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t153-smooth-heat-both-signs-local-axioms.txt` **逐字节完全一致**，均为 **2357888 bytes**，SHA256 **`dc67c50476d527f50e8ed5ba9e1ad616a91814e20cd0c624b526226b1ca8483b`**；远端末行同为 7588 声明审计通过。

## 签发结论

**14/14 PASS，无阻断 C169 AUXILIARY 验收的语义或证据缺陷。** 真实反射、受限时间与柱体保测、两个真实时间导数、原负向热算子、完整空间梯度及观察项、四项积分换元与同常数顺序均已核对。可以登记 REVIEWED / AUXILIARY；不能据此提升 P024 或改变 17/26。原 C² 时间权、全部弱周期轨道和一般凸多面体仍是后续义务。本报告及 reviewed_at 在签发通知后冻结。
