# T189 / C205 独立本机验收：原差分方程的完整时空弱恒等式

- `checked_sha`: `b92214e1ee49124122e54ed76dc7bb734792b157`
- `base_commit`: `32711e6669f223eba5851b43e9ec886a40c45b6e`
- `reviewed_at`: `2026-10-20T01:03:47+00:00`
- `reviewer`: 独立本机 Agent `/root/accept_spatial_lemma`；只审查固定 Git 对象、实际完整类型和证据，未参与本批数学实现。
- `result`: **PASS，13/13 显式声明**；`axiom_check`: **PASS**；`scope`: **AUXILIARY**。
- 结论：C205 可以按该精确版本登记独立验收通过。没有发现需要修复的数学缺陷。原文覆盖保持 **17/26**；不能由本报告提升整个 P021 / `prop:control-convergence` 或声称极限 PDE、连续端点已经完成。

## 版本、原文与审查方法

独立读取固定版本的 `AGENTS.md`、`governance/PROJECT_OPERATIONS.md`、`state/README.md`，复核既有里程碑/覆盖规则；读取 `governance/analysis/T189-weak-testing.md`、`governance/MATH_SPEC.md` 的 T189 段落及 `state/progress.json` 中 T189/C205 的实际记录。以 `git show checked_sha:path` 读取全部五个新模块的全部证明，以及固定原始审计中全部十三个 `#check @...` 的完整类型与递归公理信息，不用执行者说明或 CI 成功替代语义检查。五模块名单与声明名单分别为 `/tmp/carleman-t189-weak-testing-modules.json`、`/tmp/carleman-t189-weak-testing-declarations.json`。

原文定位为 `paper/main.tex:2385–2400`：以 `dt φ_h^(n−1)` 测试原隐式方程，非周期分部求和，随后才通过一致性和终态衰减传到极限。另对照原方程 `1731–1735`、物理质量和控制时间指标 `1749`、附录真实刚度 `2901–2905`、势配对 `2923–2925` 及测试强一致性 `2928` 起的内容。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，本批没有修改原稿。

固定治理文件 SHA256：`AGENTS.md` 为 `d1feeda8ff298ba06b223d79f5a5d6ea4fd5846f6a7410b9843f37098122a398`；`PROJECT_OPERATIONS.md` 为 `0a60d40e67eaf7449c8903e0c560dbccd6e74c5f81e288dec8a7e098857fb155`；`state/README.md` 为 `6e4f3f4573eb8bb9073bc787b088c100721c894e3667767c2bae578047bdcc7e`。实际核对其固定版本；本次 API 三作业已经最终成功，无需使用“摘要迟滞时以独立完整作业日志确认”的替代路径。

## 十三项实际声明逐项结论

下表源码路径均相对于固定提交的 `Carleman/Control/`；审计行号指独立下载且与固定本机副本逐字节相同的 `axioms.txt`。每一项均检查完整展开类型和实际证明；每一项的递归公理仅为 `propext`、`Classical.choice`、`Quot.sound`。

| 完整声明 | 固定源码 / 审计起始行 | 实际结论与前提检查 | 结论 |
| --- | --- | --- | --- |
| `Carleman.Physical.physical_summation_by_parts` | `PhysicalWeakTesting.lean:13` / 35913 | 任意两份 `Fin (N+1) → X` 序列的真实内积求和恒等式；保留 N、0 两端，测试在 `castSucc`，状态差在 `succ−castSucc`。允许 N=0。 | PASS |
| `Carleman.Physical.forward_equation_weak_identity` | `PhysicalWeakTesting.lean:29` / 35918 | 仅从原 `ForwardEquation dt L B u y` 与 `dt ≠ 0` 推出完整弱恒等式；L/B 为实际 CLM，φ 遍及全部状态序列，无伴随测试条件。 | PASS |
| `Carleman.timeCellReconstruction_difference_inner` | `TimeWeakTesting.lean:14` / 35926 | 实际线性等距 E、真实 Bochner 时间重构与 `dt⁻¹ • Δφ` 的内积等于原物理差分和；时间质量 dt 精确抵消。 | PASS |
| `Carleman.fixedTimeCellReconstruction_inner` | `TimeWeakTesting.lean:23` / 35933 | 沿 `g.period=T` 将实际时间内积运输到固定 `Lp H 2 (volume.restrict (Ioc 0 T))`，仍恰为 `dt Σ⟨uᵢ,vᵢ⟩`。 | PASS |
| `Carleman.fixedTimeCellReconstruction_difference_inner` | `TimeWeakTesting.lean:30` / 35939 | 固定 T 的同一差商配对，运输没有产生额外因子、端点项或更换 E。 | PASS |
| `Carleman.cartesianPhysicalLaplacian_gradient_pairing` | `CartesianWeakTesting.lean:18` / 35946 | 对独立任意 f、z 的原物理 Laplacian 双线性配对等于真实 Kuhn 弱 jet 的全部一阶字段 L² 内积。 | PASS |
| `Carleman.cartesian_forward_reconstructed_weak_identity` | `CartesianWeakTesting.lean:28` / 35952 | 原完整 FD 方程推出六项真实空间/Bochner 配对身份；E、G、P、K 均在结论内部指定为实际对象，非抽象配对前提。 | PASS |
| `Carleman.cartesianBoxCellControl` | `FixedBoxWeakTesting.lean:14` / 35980 | 实际 CLM 定义：固定盒 E 的 CLM 与原控制节点零延拓 B 复合，确为 K=EB。 | PASS |
| `Carleman.cartesianBoxReconstructedPotential` | `FixedBoxWeakTesting.lean:21` / 35989 | 同一真实时间—对偶胞元平均势乘子沿盒边界等式运输，输出为固定盒上的实际 `BoundedMultiplier`。 | PASS |
| `Carleman.cartesianBoxReconstructedPotential_commute` | `FixedBoxWeakTesting.lean:28` / 36001 | 对全部原节点状态 z，固定盒的 `P.map(E z)=E(Vavg z)`；没有把该交换身份作为假设。 | PASS |
| `Carleman.cartesian_fixed_forward_reconstructed_weak_identity` | `FixedBoxWeakTesting.lean:42` / 36013 | 同一 lo/hi、T 上的六项精确身份；仅使用几何等式 hbox、时间等式 hT 和原状态方程。所有物理状态/控制、测试均完整保留。 | PASS |
| `Carleman.timeCellReconstruction_multiplier_inner` | `TimePotentialPairing.lean:12` / 36045 | 任意测度 ν、真实实值有界乘子 aᵢ 及任意 L² 的 uᵢ/vᵢ，真实 Bochner 内积中乘子可以从状态移到测试。 | PASS |
| `Carleman.fixedTimeCellReconstruction_multiplier_inner` | `TimePotentialPairing.lean:20` / 36051 | 同一乘子在固定时间空间中的精确移项；无光滑、势小量、共同收敛或抽象自伴假设。 | PASS |

这是 **11 个 theorem + 2 个 def**，不是十三个新的原文定理。五模块均由固定 `Carleman.lean` 实际导入；每项均在固定 `tools/CheckAxioms.lean` 有 `#check @...` 及 `#print axioms ...`。从数学基线到证明提交，`Carleman/` 下的变化恰是上述五个新模块。

## 时间指标、符号及原完整方程

`ForwardEquation` 的实际定义是对每个 `i : Fin N`，`dt⁻¹ • (y i.succ−y i.castSucc)+L i (y i.succ)=B(u i)`。本批直接对该等式施加 `dt*inner ℝ · (φ i.castSucc)`，再求和；并未改成弱方程作为输入，也没有调用伴随方程。一般辅助定理不要求 L 对称、正性或势预算，原时间网格的 `dt_pos` 在内部给出所需 `dt ≠ 0`。

点态代数式实际为 `⟨y⁺−y⁻,φ⁻⟩+⟨y⁺,φ⁺−φ⁻⟩=⟨y⁺,φ⁺⟩−⟨y⁻,φ⁻⟩`；证明由内积加减展开，之后用 `Fin.sum_univ_succ` 和 `Fin.sum_univ_castSucc` 做真正的有限和望远镜消去。最终移项后的时间项为负，右侧初值项为正、终值项为负。没有用周期性把端点认同，也没有假设终值为零。φ 的初末值都是任意完整状态；初态数据在此由 y⁰ 本身表示，实例化原初值条件时自然恢复原 y₀,h。

时间重构是有限个真实 `indicatorConstLp` 的和，单元为 `(tᵢ,tᵢ₊₁]`；真实互不相交和受限 Lebesgue 体积 dt 供应 `timeCellReconstruction_inner`。测试差商确为 `dt⁻¹ • (φ⁺−φ⁻)`；E 的真实等距内积身份和实数双线性性使 `dt·dt⁻¹=1`。因此离散差分和进入 Bochner 内积后没有丢掉 dt，也没有多出一个 dt。一般求和允许 N=0；实际 `TimeGrid` 的正时间步资格负责物理实例，不需要额外手工排除端点。

## 物理质量、完整梯度、平均势与控制

实际 E 是 `cartesianCellIsometry`：原内部对偶单元的指示重构，在 `volume.restrict openCoordinateBox` 的真实 L² 空间中等距。原 `PhysicalFiniteSpace` 的质量为 `∏ⱼδⱼ`。重读 `FiniteCellReconstruction` 的真实指标函数 Gram 矩阵证明，确认互不相交胞元、体积恰为质量，供给实际物理内积等式；这不是把重构范数另行定义成物理范数。未覆盖边界条带仍取零，证明没有假设对偶单元覆盖整个域。

刚度证明先展开 `cartesianPhysicalState_inner`，再调用原 FD Laplacian 的双线性弱刚度身份，最后展开 `weakGradientPairing_apply`。其中 f、z 是独立任意完整节点状态，结果不是仅有 f=z 的能量公式。实际 `field 1` 取值于原 `DerivativeFiber d 1` 的 L² 类；`GradientPairing` 经 `Sym.oneEquiv` 展开为每个坐标恰一次的真实弱梯度内积。因此时间梯度项就是所有空间分量的 `∇R_h y⁺` 与 `∇R_h φ⁻` 配对，没有遗漏坐标、坐标缩放或替换为胞元常数重构的梯度。

P 是 `cartesianReconstructedPotential`，其胞元系数为原 b 在实际时间胞元与内部对偶胞元上的平均，即 `(dt·∏ⱼδⱼ)⁻¹` 乘实际迭代积分。重读其 `FiniteCellMultiplier` 依赖：可测指示函数有限和给真实有界乘子，互不相交保证胞元上等于原平均值，所有胞元之外为零，界仍为 b.bound；真实 Lp a.e. 等式给出 `P.map(Ez)=E(Vavg z)` 及物理配对。这里 b 是原有界可测实势，未要求光滑，也未把任意乘子冒充原平均规则。

K 的实际定义为 E 与原控制节点零延拓 B 的 CLM 复合。主恒等式中的控制配对经同一 E 的内积等距直接回到 `⟨B uᵢ,φᵢ⟩`；空间物理质量与时间质量由真实内积承担。ω 只用于原控制节点子类型，允许任意集合、空控制索引、空内部节点。没有在本批声称 K 的支撑全部落在 ω；胞元重构的几何支撑问题属于已单列的分析，不能由节点属于 ω 自动推出。

真实六项身份为

`−⟨E y⁺,E D_tφ⟩time + ⟨∇R y⁺,∇R φ⁻⟩time + ⟨P(E y⁺),E φ⁻⟩time`

`= ⟨E y⁰,E φ⁰⟩ + ⟨K u,E φ⁻⟩time − ⟨E yᴺ,E φᴺ⟩`。

全部括号是 Lean 中实际物理空间或 Bochner L² 的 Hilbert 内积，具真实可积性；不存在未清偿的“这些配对等于积分”的新增假设。主定理仍把势写在状态侧，最后两个公开 helper 可以以**同一个 P**将它精确移到测试侧；报告不把这个可重写的组合说成已经声明了另一条极限方程。

两个乘子 helper 调用的是 `BoundedMultiplier.inner_map_left`：实际 `map_ae`、`L2.inner_def` 和实数乘法交换给出空间自伴配对，再应用实际时间内积公式。该接口对任意测度 ν 成立，不要求空间有限体积、域上光滑或额外逐点代表。`WeakProduct` 中其他光滑乘积规则的前提没有泄入此处。有限时间数据每项已经是实际 L² 类，配对可积性由 L² 内积实现内部供应。

## 固定域、量词、边界与范围

固定盒版本的 hbox 是 `lo j + (N j:ℝ)*δ j = hi j`，固定时间版本的 hT 是 `g.period=T`；实际证明用函数外延与 `subst hi`、`subst T` 消去这些等式。E、Kuhn jet、K、P、时间测度均运输同一对象，没有逐网格再选择一个不同的同构或附加范数常数。输入 b 的类型仍写在由网格表达的同一个盒和周期上，通过 hbox/hT 恰是所固定的物理域与 T；不是允许更换原连续势。

最终类型对全部 d、正步长向量 δ、网格 N、集合 ω、TimeGrid、原 b、完整控制 u 和完整 y/φ 量化，只输入上述域/时间等式与原 ForwardEquation。没有形状正则、长宽比、嵌套、h–dt 耦合、CFL、`dt M≤1/2`、小势、状态/控制/梯度预算、终态衰减或伴随测试前提。本批是精确恒等式，因而没有待选择的隐含网格或 T 依赖估计常数；实际 T 只决定共同积分区间。一般 helper 的等距 E 前提在最终实例内部由原 E_h 清偿。

原稿在 2387 行后还使用终态衰减、测试强一致性和共同子列传极限。本批只完成其有限网格方程身份及真实配对接口，不证明测试及时间差商强逼近，不证明产品测度 L² 与 Bochner 势乘积桥，不把 b 的强收敛自动升级成乘积收敛，也不删除终端配对。沿共同状态/控制子列传每一项、终端衰减、V′ 时间导数、连续初末迹和整个 P021 仍须后续证明；这与本批 AUXILIARY 范围一致。

## 依赖版本与前置验收

对五模块递归解析所有 `Carleman.*` 导入，实际闭包共 **356 个模块**，其中本批新增 5 个、旧模块 **351 个**。逐字节比较固定证明与数学基线，351 个旧模块全部相同。另将关键入口的完整导入闭包逐字节比较到独立接受版本，结果如下；不是只比较入口文件名或引用旧结论。

| 入口 | 已接受的固定版本 | 闭包模块数 | 差异 |
| --- | --- | --- | --- |
| `Control/TimeReconstructionEstimates` | `69cee61bd440c386c2ac20af6104f72e98b3563c` | 24 | 0 |
| `Spatial/FixedBoxKuhnConsistency` | `69cee61bd440c386c2ac20af6104f72e98b3563c` | 344 | 0 |
| `Control/PhysicalEquations` | `1aa9b1f253dd759ccc18d92d151aa7c81646f51c` | 6 | 0 |
| `Spatial/CartesianCellReconstruction` | `7c2ceacf62d42b168879106b8c6d6fc246c45794` | 326 | 0 |
| `Control/CartesianPotentialReconstruction` | `ffa5a6f8061e5b13aa96a7f77081aa4f8482e2e5` | 333 | 0 |
| `Spatial/CartesianPhysicalStiffness` | `7d1cc86d3c0a01b524f099ba90baaf59784f159d` | 316 | 0 |
| `Spatial/GradientPairing` | `3d5aa9cec281974bef7da9d37ffa11a8f9f75670` | 50 | 0 |
| `Spatial/WeakProduct` | `604328efce1cc28e4d6fe6cadcdaa039ee0e76a3` | 22 | 0 |

已完整读取 T188 冻结报告 `governance/reviews/T188-local-acceptance.md`，报告提交 `4e753a25217da7db59cbf5dc6e1c65bf33c966be`，checked SHA 为本批 base，reviewed_at 为 `2026-10-20T00:53:09+00:00`，23/23 PASS、AUXILIARY。再次核对报告工作区字节与冻结提交完全相同：20140 bytes，SHA256 `0ac99159c6ef822b9c5b46ff5e78a6706e39e8b44042a8d742fe9e8d2d0490df`。T188 的真实状态弱子列结果是已接受的后续组合前置，但本批恒等式不需要调用其紧致性定理；本报告没有虚称已经完成二者的极限组合。

## 构建、公理与独立远端证据

固定本机最终定向日志 `/tmp/carleman-t189-target6.log` 为 **3547 jobs 成功**；完整 `/tmp/carleman-t189-weak-testing-build.log` 为 **4167 jobs 成功**；相应 `-axioms.log` 无错误输出。先前 `target2/3/4` 的开发失败日志没有被当作最终证据。没有在变化中的工作区重跑未来版本来替代本批固定远端构建。

独立访问 GitHub run、完整分页 jobs 和 artifacts API，并独立查询 main 分支；读取到 main 精确为 checked SHA。正式 [Lean CI run 39350616369](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39350616369/attempts/1) 的 `head_sha`、`head_branch=main` 与本批一致；run 实际字段为 **completed/success**，updated_at `2026-10-20T01:00:01Z`。三个实际 job 及所有返回步骤均为 success，包括测试、构建、结果/声明上传、同次快照生成和最终 Complete job：

| 实际 job | ID | 最终状态 | completed_at UTC |
| --- | --- | --- | --- |
| state-check | `118393663790` | completed / success | `2026-10-20T00:56:52Z` |
| lean | `118393664191` | completed / success | `2026-10-20T00:59:50Z` |
| dashboard / snapshot | `118394608266` | completed / success | `2026-10-20T01:00:00Z` |

自行调用 `gh run download 39350616369` 下载以下两份原始工件到本审查路径，两个命令实际 exit 0；没有使用 root 的下载副本作为独立下载：

| 工件 | artifact ID | ZIP bytes / GitHub digest |
| --- | --- | --- |
| `lean-ci-result` | `12232464796` | 492 / `sha256:da9729380e168ac2340823d74fa45641e9e9de9fab5c3f02eaae019c96fecb73` |
| `lean-declaration-evidence` | `12232967188` | 254053 / `sha256:72e6f8550683fd21654871608ba642957bdee30fbd1fc5ab5fd7eb754aa30204` |

`/tmp/carleman-t189-weak-testing-main-ci/result.json` 实际为 537 bytes，SHA256 `c833e88ddce9bb855b33bebf7aff9dcf510eebcccff70cdeaef630786031bfbd`；status PASS，`checked_sha=source_head_sha=b92214e1ee49124122e54ed76dc7bb734792b157`，ci_url 精确指向上述 run/attempt，finished_at `2026-10-20T00:58:49.783770+00:00`，targets 为 `Carleman`。

`/tmp/carleman-t189-weak-testing-main-axioms/axioms.txt` 与 `/tmp/carleman-t189-weak-testing-local-axioms.txt` 独立逐字节比较相同：**2753457 bytes**，SHA256 **`d9688ed0af3f9583f3cfb615110597b1f7ce005f8971b39b301afa586becbb49`**。逐项找到十三个完整类型及公理记录；全 raw 中 3318 条带公理记录和 9 条无公理记录合计 3323 个不同显式名称，重复打印按名称去重，均无非标准基础公理。此显式打印数量与环境递归总数是不同口径。

同时读固定 `CheckAxioms` 的实际 `run_cmd`：遍历环境中所有 `Carleman` 前缀（含 privateToUserName 还原后的名称），逐项 `collectAxioms` 并拒绝白名单外公理。原始工件末行实际为 **`Axiom audit passed for all 8516 Carleman declarations.`**。没有 sorryAx、未授权数学公理或未证明目标身份被包装成假设。Lean 为 **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，实际本机 mathlib HEAD 相同且工作树干净，remote result 亦一致。

独立 API 原始 JSON 留存于 `/tmp/carleman-t189-weak-testing-review-run.json`（15326 bytes，SHA256 `2b3b7a14b56ebfb0092b3538fc5b70364dab4abf1868e9563d9e6e0a0d5c4521`）、`-review-jobs.json`（11819 bytes，`57daf9f296cb19ccf72f3c5f2b58383dce511dae16447d189eb88858df38e93f`）、`-review-artifacts.json`（2701 bytes，`65c72d9ff9d41fa08788833aa390991d24fccbf358d04bdf5b88206269204bb7`）。工件摘要描述 ZIP，展开文件摘要描述 result/raw，未混淆两者。

## 正式判定与冻结

**T189/C205：PASS，AUXILIARY，13/13；axiom_check PASS。** 非周期前一时间层测试、初终端点符号与 dt、原物理等距重构、全梯度刚度、真实平均势、K=EB、固定盒/时间运输和真实 Bochner 势移项均已通过固定版本语义及远端证据核验。没有阻断缺陷，也没有需要执行者修复后重验的条目。P021 及原文覆盖不因这批辅助身份自动提升。

报告仅修改并单独提交本文件，不修改证明、总台账、根导入、原稿或其他报告，不推送。以上签发时间与正文定稿后冻结；后续数学与动态审计不属于此次验收。
