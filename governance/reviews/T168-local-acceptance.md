# T168 / C184 独立本机验收：物理有限空间与计数 L² 接口

- checked_sha / source_sha: `30a03e32af45ef82baacbbfe6917cd7ceff234f3`
- mathematical_base: `d4b7f2d6d6894520fc5db06dc3a230be27518297`
- reviewed_at: `2026-10-19T13:16:43+00:00`
- reviewer: 独立本机 Agent `/root/accept_spatial_foundations`，未参与本批实现。
- result: **PASS**；axiom_check: **PASS**；全部 **16/16** 显式声明通过。
- scope: **AUXILIARY**。原物理质量 Hilbert 空间、节点乘子及物理时间权的精确接口；尚不构成新的完整物理观测或控制定理，**原文覆盖保持 17/26**。

本 Agent 从固定 Git 对象读取三个模块全部源码、十六项实际展开类型与公理、原稿、分析、MATH_SPEC、台账及关键依赖。独立查询同 SHA 的真实 GitHub run/jobs/artifacts，自行下载 result/raw 并逐字节比较固定本机证据。执行者说明和 CI 未代替数学验收。后续工作树、动态根导入和 `.ci/axioms.txt` 全部排除；仅新增并单独提交本报告，不改数学、总账或原稿，不 push。

## 原文对应与范围

固定 `paper/main.tex:1642–1645` 的 Cartesian 内节点质量为同一正数 mass=∏hᵣ，原内积为 mass·Σfᵢgᵢ；`1660–1666` 的载荷和控制采用真实节点空间、限制物理内积及对应节点加权范数。`1726` 的差分势是实节点值 bᵢⁿ 的乘法，|bᵢⁿ|≤M。`1871–1890` 的 physicalO 证明使用实际光滑周期物理权及一二阶预算；一般 qclass 位于 `292–299`，包含 C²、三阶次端点匹配和两项导数预算。

本批保留同一个 PhysicalFiniteSpace 及其真实物理范数，将它等距识别为计数测度 L²；并未把原物理质量换成未缩放的计数范数。常质量适配原 uniform Cartesian 网格，不声称已经处理原文扩展说明中的变节点质量。有限指标可为空，因而也覆盖某个受限控制节点集为空的代数情形；没有据此声称空观察区具有可观测性。

最终时间权声明是已有 PhysicalQClass 到完整 IntervalQClass 的正向转换。它保持同一 w、q、T、β、qc，不声称任意区间 C² 权都具有全局光滑物理权表示，也不把一阶 TimeWeightRegularity 误当作完整 qclass。当前范围是为后续物理观测/控制组装供应接口，不提升 prop:fd、prop:physicalO 或其它原文结论。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 十六项声明逐项核对

以下清单与固定 C184/T168 及 `/tmp/carleman-t168-physical-finite-lp-declarations.json` 完全一致；行号指 checked_sha。全部完整展开类型已读取，未依据名称推断数学含义。

| # | 完整声明 | 固定源码位置 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.PhysicalFiniteSpace.finiteMemLp` | `Carleman/Spatial/PhysicalFiniteLp.lean:16` | PASS。任意有限节点实函数在实际计数测度下属于 L²；可测性和有界性内部供应。 |
| 2 | `Carleman.PhysicalFiniteSpace.toCountLp` | `Carleman/Spatial/PhysicalFiniteLp.lean:20` | PASS。输出实际函数 √mass·f 的 Lp 类，缩放方向和因子准确。 |
| 3 | `Carleman.PhysicalFiniteSpace.toCountLp_apply` | `Carleman/Spatial/PhysicalFiniteLp.lean:23` | PASS。计数测度 ae_count_iff 将真实 toLp 代表身份合法升级为每个节点的精确公式。 |
| 4 | `Carleman.PhysicalFiniteSpace.toCountLpLinear` | `Carleman/Spatial/PhysicalFiniteLp.lean:27` | PASS。对同一 map，以 Lp 加法/数乘代表和实际标量分配律证明线性。 |
| 5 | `Carleman.PhysicalFiniteSpace.toCountLp_norm` | `Carleman/Spatial/PhysicalFiniteLp.lean:42` | PASS。真实 L² 平方积分转为计数和，(√mass)²=mass，恰恢复原物理范数；系数为 1。 |
| 6 | `Carleman.PhysicalFiniteSpace.countLpEquiv` | `Carleman/Spatial/PhysicalFiniteLp.lean:49` | PASS。已证线性等距加显式满射，逆向节点函数为 uᵢ/√mass，除数严格为正。 |
| 7 | `Carleman.PhysicalFiniteSpace.countLpEquiv_apply` | `Carleman/Spatial/PhysicalFiniteLp.lean:64` | PASS。等距满射的正向 map 就是第 2 项，无任意替换。 |
| 8 | `Carleman.BoundedMultiplier.ofFinite` | `Carleman/Spatial/PhysicalFiniteWeights.lean:14` | PASS。value=b、bound=M，真实逐节点界直接给出计数测度上的乘子界。 |
| 9 | `Carleman.SpatialProfile.ofFinite` | `Carleman/Spatial/PhysicalFiniteWeights.lean:22` | PASS。value=r、bound=R，完整有限相位及显式逐节点界；不从连续空间 a.e. 数据偷取节点值。 |
| 10 | `Carleman.PhysicalFiniteSpace.countLpEquiv_multiplier` | `Carleman/Spatial/PhysicalFiniteWeights.lean:33` | PASS。真实等距 map 严格交换节点乘法与同一 b 的 Lp 乘法。 |
| 11 | `Carleman.PhysicalFiniteSpace.countLpEquiv_weighted_norm` | `Carleman/Spatial/PhysicalFiniteWeights.lean:42` | PASS。计数加权 seminorm 精确等于原物理空间的节点乘法后范数。 |
| 12 | `Carleman.PhysicalFiniteSpace.countLpEquiv_symm_map` | `Carleman/Spatial/PhysicalFiniteWeights.lean:48` | PASS。等距逆映射把 Lp 乘法严格带回同一原节点乘子。 |
| 13 | `Carleman.PhysicalFiniteSpace.multiplier_symmetric` | `Carleman/Spatial/PhysicalFiniteWeights.lean:54` | PASS。直接在原 mass·Σ 内积下对全部 f、g 证明实节点势对称，不依赖正势或特殊状态。 |
| 14 | `Carleman.PhysicalFiniteSpace.multiplier_opNorm_le` | `Carleman/Spatial/PhysicalFiniteWeights.lean:63` | PASS。由实际计数乘子界和精确等距得到原物理 CLM 范数≤同一 M，无节点数或质量损失。 |
| 15 | `Carleman.smooth_interval_derivatives` | `Carleman/Control/PhysicalIntervalQClass.lean:13` | PASS。T>0 下整个 Icc（含两端点）一阶及二阶 within 导数分别等于实际全局导数。 |
| 16 | `Carleman.Physical.PhysicalQClass.toInterval` | `Carleman/Control/PhysicalIntervalQClass.lean:30` | PASS。逐字段转移原 C²、下界、两导数预算及三个端点条件，β/qc/T 不变。 |

## 原质量、全部节点及等距满射

已直接读取 PhysicalFiniteSpace 的类型、inner core 和实例：它的元素仍是所有函数 ι→ℝ，代数结构和 valuesEquiv 保持节点值；实际内积定义为 mass·Σfᵢgᵢ，范数由该内积产生，norm_sq 为 mass·Σfᵢ²。它与普通函数空间的 sup 范数分开。第 1 项中 ‖f‖ 仅是普通有限函数的 sup 上界，用于证明计数 L² 成员资格，未被冒充为物理范数。

计数测度在有限可测单点空间上有限，所有实函数真实可测且有界，因此 finiteMemLp 的输入没有额外可积性限制。第 5 项实际使用 lp_two_norm_sq_integral、integral_count 和 PhysicalFiniteSpace.norm_sq，逐项计算 |√mass·fᵢ|²=mass·fᵢ²，再以两个范数非负恢复范数相等；没有仅由有限维范数等价选取一个可能依赖节点数的常数。

第 3 项使用 mathlib `Measure.ae_count_iff`，其证明基于计数零测集合只能是空集。因此计数 Lp 代表的身份确实对每个 i 成立；这与连续 Lebesgue Lp 无法从 a.e. 身份获取指定节点值的情形不同。该步骤在本批是合法且必要的，所有节点均被保留。

第 6 项对任意实际计数 Lp 元素 u，构造 `valuesEquiv.symm (fun i => u i / √mass)`。hmass>0 给 √mass>0；Lp.ext 后对每个 i 清偿 √mass·(uᵢ/√mass)=uᵢ，从而得到全空间满射。不存在有限谐波、支持或频率限制。代码没有要求 Nonempty ι，空指标时两边均为零维空间、所有求和为空和，证明仍适用；也没有除以节点数。

已查看 mathlib LinearIsometryEquiv.ofSurjective 的实际构造，正向函数保持原线性等距，逆向由已证双射生成；另核对 inner_map_map 由极化恒等式从线性等距证明。因此 countLpEquiv 保留原物理内积及范数，而非仅提供集合双射。质量平方根出现在表示中，不进入估计损失常数。

## 节点势、权与统一界

`BoundedMultiplier.ofFinite` 和 `SpatialProfile.ofFinite` 都以传入的全部节点值作为真实 value，并采用给定 M/R 作为 bound。二者要求的 |bᵢ|≤M、|rᵢ|≤R 是明确逐节点条件；没有从空间连续函数的 L∞ 等价类或某个 a.e. 上界擅自取点值。相位构造本身只负责有界性，不声称任意节点相位满足负性或 Carleman 几何条件。

第 10 项展开实际 b.map_ae、countLpEquiv_apply 和 multiplier_apply 后，逐点计算 √mass·(bᵢfᵢ)=bᵢ(√mass·fᵢ)。第 11 项再取同一 Lp 范数并用 norm_map，故对于任意 b，准确得到

`b.seminorm(countLpEquiv f)² = mass · Σᵢ (bᵢ fᵢ)²`。

这包括实际允许权 q^τ exp(±qρ) 的节点乘子，也允许变号或为零的普通势乘子；不需要 b 正或可逆。第 12 项用同一个等距满射的 symm_apply_apply，确认反向传输后的算子就是原 physical multiplier。没有替换其作用或原物理空间。

第 13 项的实际类型是原线性映射的 IsSymmetric，即对全部 f、g 有 ⟨bf,g⟩=⟨f,bg⟩。证明直接展开两个原物理 inner_eq，再逐节点交换实数乘法。对该完整 Hilbert 空间上的 CLM，这等价于自伴；已查看 mathlib IsSymmetric.clm_adjoint_eq / isSelfAdjoint_iff_isSymmetric 的实际陈述和证明。该结论针对真实实节点势，不涉及任意矩阵或非实系数。

原 multiplier 定义使用有限维性把真实线性节点乘法包装为 CLM；本批没有用这项自动连续性抽取统一范数常数。第 14 项重新以 opNorm_le_bound 证明对每个 f 的界：ofFinite 的 bound=M，原 BoundedMultiplier.seminorm_le 给 M 倍计数 L² 范数，再由两项精确等距身份恢复物理范数。最终常数就是 M，独立于质量、节点数、时间和状态。M=0 与空索引均无需特别排除或除法处理。

## 实际物理权与两阶区间导数

PhysicalQClass 的实际结构包含全局光滑 w.q、全局 qc 下界、实际 deriv 和 deriv(deriv q) 的两项预算，以及 q、q′、q″ 的三个端点匹配。已有 physicalTimeWeight_qclass / physical_qclass_uniform 为原 `qb/sqrt(sin²(πt/T)+δ²)` 供应这些性质；本批只把这个既有完整输入转入原 IntervalQClass，没有重新选择 Cb、qb、δ、S 或新增预算。

第 15 项先利用 T>0 得到整个 Icc 的 UniqueDiffOn。全局 HasDerivAt 限制为 HasDerivWithinAt，再由唯一性证明 `derivWithin q Icc = deriv q` 在 Icc 上逐点成立，包括一侧端点。随后对这个 EqOn 使用 derivWithin_congr，合法地把二阶 within 导数的内层函数替换为实际 deriv q；hq.deriv′ 供应后者的全局可微性，再次用同一 UniqueDiffOn 恢复二阶身份。没有把区间外任意延拓的导数混入，也没有通过端点零测忽略端点值。

第 16 项用 g.period_pos 清偿唯一微分条件；全局 smooth 降阶并限制给 C²(Icc)，lower 直接限制。first_bound、second_bound 经第 15 项改写；三个端点条件分别原样使用 q 的 endpoint 及改写后的一、二阶 endpoint。beta_pos、qc_ge_one 同样原样保留。结论对全部 g、w、β、qc 成立，不缩小 β、不放大 qc、不改变 T，也没有网格或状态输入。方向仅为已有物理光滑类到完整区间类，不是完整区间类到全局光滑类的等价断言。

## 固定闭包、公理和本机证据

三个模块的 Carleman 导入闭包共 **61** 文件，除三个新模块外的 **58** 个文件与 mathematical_base 逐字节一致。另行核对以下关键已接受版本的完整递归闭包，均未改变：

| 依赖 | 接受版本 | 比较入口及闭包文件数 |
|---|---|---|
| C122 | `337d9c1b8c5fadce4e638a2c96311e230ee94bb1` | PhysicalFiniteSpace；1 |
| C062 | `0c632f37eadbcece6459555fef22a2bb4b3ca688` | AffineSimplexNorm；41 |
| C044 | `fba691ef4acce0af1d303f19cae7ceaccfe7eb20` | PhysicalQClass；31 |
| C182 / T166 | `28789e8973368055acc0c17d5b395332e6ee7364` | IntervalQClass；17 |
| C022 | `a6c199412758d406be8c3f8d1e76587b9f820bc1` | AllowedWeight；18 |

已读取这些关键实际对象及 WeightedL2、SpatialProfile/allowed multiplier 的定义与范数证明；对 mathlib 的 ae_count_iff、integral_count、uniqueDiffOn_Icc、等距满射及内积/自伴含义作了源码核对。三模块均在固定根目标导入，十六项均列有实际 #check 与 #print axioms；新增源码无 sorry、admit、新数学 axiom 或 native_decide。治理协议及覆盖规则与上次已读版本一致。

实际检查器遍历所有 privateToUserName 下的 Carleman 常量并递归 collectAxioms，仅准许 propext、Classical.choice、Quot.sound。固定 raw 有 **3052** 条显式公理打印记录（**3048** 个不同名字），均为空或仅含正常三项基础公理；十六项各自的实际类型和公理输出均已逐项读取。显式打印数量不与递归总数混同；实际末行为 `Axiom audit passed for all 8062 Carleman declarations.`。

实际读取三份定向日志：`/tmp/carleman-t168-finite-lp-target3.log` 为 **3182 jobs**，`/tmp/carleman-t168-finite-weights-target.log` 为 **3183 jobs**，`/tmp/carleman-t168-physical-qclass-target3.log` 为 **3054 jobs**，均完成对应模块。根日志 `/tmp/carleman-t168-physical-finite-lp-build.log` 为 **4091 jobs** 成功。`-axioms.log` 是零字节 stderr，不当作成功证明。Lean pin 为 4.35.0，CI 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 与实际干净本机 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 独立同 SHA CI 及原始工件

本 Agent 独立查询 [run 39258043795 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39258043795/attempts/1)，确认 main、精确 head SHA，最终 run 为 `completed/success`，updated_at=`2026-10-19T13:15:28Z`。实际三个作业均最终成功：

| job | 实际 ID | 最终状态 |
|---|---|---|
| state-check | `118078204109` | completed / success |
| lean | `118078203761` | completed / success |
| dashboard / snapshot | `118079998594` | completed / success |

本 Agent 自行以 gh run download 下载同 run 的 `lean-ci-result`（artifact **12189645544**，API 归档大小 492 bytes）及 `lean-declaration-evidence`（artifact **12189670528**，232728 bytes）；二者未过期，工件元数据 head_sha 均与本次 proof SHA 一致。未使用主执行者的下载副本替代独立下载。

实际 `/tmp/carleman-t168-physical-finite-lp-main-ci/result.json` 为 **537 bytes**，SHA256 `8de38642d29283959c2b7331c84b6a819ef25fa98ad4d578deb940d54a7f6f69`。status=PASS，checked_sha=source_head_sha=`30a03e32af45ef82baacbbfe6917cd7ceff234f3`，targets=[Carleman]，finished_at=`2026-10-19T13:14:14.201431+00:00`，ci_url 指向同一 run/attempt，实际工具链与固定 pin 一致。下载时作业尚在收尾，已继续等待并实际查询全部作业最终成功后才签发。

独立下载的 `/tmp/carleman-t168-physical-finite-lp-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t168-physical-finite-lp-local-axioms.txt` **逐字节完全相同**：各 **2500807 bytes**，SHA256 均为 **`e863de2761a426968e2b4c1ba0180df999dad559409c347282927d0bb5e571f1`**。完整实际类型、公理输出和 8062 项递归审计 PASS 一致；压缩工件大小与 raw 文件大小分别记录。

## 签发

**16/16 PASS，C184 可在 AUXILIARY 范围登记 REVIEWED。** 真实质量、全节点等距满射、节点势/权交换及同 M 界、原物理权两阶区间导数和三个端点条件均通过，未发现阻断性数学、量词或对象身份问题。本批没有完成新的物理观测/控制命题，覆盖保持 17/26。正文与 reviewed_at 冻结，仅提交本报告，不 push。
