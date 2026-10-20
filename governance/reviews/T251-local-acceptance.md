# T251 / C267 独立本机验收

- checked_sha: `80b4f9a934f15a60281b7d5abf3f9a04c486eb41`
- mathematical_base: `49168d2536a37eebacf348295cdeb46a8a3f5a90`
- reviewed_at: `2026-10-20T09:44:29+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，9/9 定理，未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；原指数和光滑内域上的经典 Miranda–Talenti 估计，精确常数 1。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/ClassicalConvexHessian.lean`、全部 raw 完整类型及公理记录、analysis/MATH_SPEC/台账，对照原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 要求 Dirichlet 算子域为 H²∩H¹₀ 以及完整椭圆正则性；本批解决其辅助路线中的经典统一 Hessian 估计，没有把光滑状态结论等同于该原命题。

## 数学、量词与范围

1. **真实紧致坏点集给薄层正性。** 对 S={g<a}，取 K=closure(S)∩{F≤0}。连续性使后者闭，实际 hK 给 K 紧；S 由连续 g 开。任意 K 中的点若不在 S，则按真实 `frontier_eq` 属于 frontier(S)，与所给严格 F>0 冲突。因此 K 中 g<a。非空时在 K 上实际取 g 的最大点 c，选择 r=(a−g(c))/4>0；若 g(x)≥a−2r，便有 g(x)>g(c)，不可能仍是坏点。空 K 分支直接取 r=1。没有把仅靠近某个水平的点未经证明视为靠近边界，也没有假定所有 {g=a} 点都是 frontier。
2. **扰动真实通量，不假定整层通量非负。** 定义连续函数 F=原 `levelBoundaryFlux u g`+δ‖∇g‖²。真实 Dg≠0 经欧氏 Riesz 坐标身份给 ‖∇g‖²>0，所以 δ>0 与边界通量≥0 给严格 F>0。对 κ≠0 的任意点，实际完整 tsupport 结论给 a−2ε≤g≤a−ε；ε>0 使点属于 S，ε≤r 则给 g≥a−2r，薄层正性遂适用。由 κ≥0 得 `κ·flux≥−δκ‖∇g‖²`，κ=0 分支逐点为等式。r 可以依赖 g、u、δ；并未声称所有状态或所有内域共享层宽。
3. **统一层质量来自精确积分身份。** 同一真实 ηε、κε 满足 `∫κ‖∇g‖²=∫ηΔg`。比较时使用 0≤η≤1、S 外 η=0，得到 `ηΔg≤1_S|Δg|`，不要求 Δg≥0。Δg 在紧 closure(S) 连续，故真实 `IntegrableOn |Δg| S` 和 indicator 的全空间可积性内部成立；ηΔg 由 η 光滑紧支可积。右端 M=∫S|Δg| 是有限实数，独立于 ε、δ，但可以依赖 g 及内域。没有假定 κ 的统一 L∞ 界、表面积界或 coarea 公式。
4. **积分比较及符号。** κ‖∇g‖² 和 κ·flux 均由实际 κ 光滑紧支、其余因子连续/光滑给整个乘积可积。先积分逐点下界，得 `−δ∫κ‖∇g‖²≤∫κ·flux`。质量上界乘以负数 −δ 后正确反向，得到 `−δM≤∫κ·flux`，再使用 T250/T249 的同一 η、κ 精确 Hessian 恒等式。没有把实数积分的非可积默认值用于比较，没有删掉权导数项或错置通量负号。
5. **真实支配收敛，包含边界点。** 对任意连续 F 和任意正序列 εₙ→0，积分函数 ηₙF 连续，故实际 AE 强可测。支配函数是 `1_S|F|`，其可积性来自紧闭包和真实 volume；S 内用 η∈[0,1]，S 外用 η=0，得到全部点的范数支配。T250 的真实逐点 indicator 极限乘以 F，正是极限函数 `1_S F`。特别 g=a 时每个 ηₙ 都为零，不需要边界零测，也没有不可数 AE 交换或仅在子列上收敛的替换。mathlib DCT 的可测性、可积支配及 AE 极限三个实质条件全部供应，最后由 `integral_indicator` 识别原 S 上积分。
6. **两次极限的次序合法，最终常数确为 1。** 先固定 δ>0，εₙ=1/(n+1) 最终小于该 δ 对应的 r，以上下界遂沿该完整尾段成立。由真实积分收敛得 `−δM≤L`，L=∫S[(Δu)²−HessSq(u)]。此结论对每个 δ>0 成立，再取 δₙ=1/(n+1)→0，由同一个固定有限 M 得 0≤L。没有把依赖 δ 的 r 当成统一值，没有交换两个未经证明一致的极限，也不需要 M 对内域编号统一。最后先证明 (Δu)² 与 HessSq(u) 各自在 S 上可积，再合法拆开 integral_sub，得到精确常数 1 的估计。
7. **实际最终域与所有几何前提内部供应。** 最后取 g=`halfspaceExpSum ℓ b n`、a=1/2。原有限严格半空间交有界，已有真实 closure 内含关系给该内域紧闭包；真实内点 z 与原凸支撑不等式给 frontier 上 Dg≠0。原 C∞ u 的真实 frontier 零值经实际水平图梯度/Hessian 身份和指数和 Hessian 非负给通量≥0。特别 whole-level 零值不是额外输入：先前实际凸性论证把每个 g=1/2 的点放入真实 frontier，才调用水平图身份。最终类型只保留原有界严格半空间域、编号 n、实际内点、全局 C∞ u 及真实 frontier 零值；没有薄层界、通量条件、候选 Hessian、图册、截断或目标估计输入。
8. **精确统一性及边界。** 原 `smoothHessianSq` 是全部有序坐标对 ΣᵢΣⱼ(DᵢDⱼu)²；Laplacian 与梯度也都是实际经典导数。常数 1 不含 n、d、几何斜率、u 或中间 M/r。最终定理适用于每个给定实际内点的内域，没有声称所有早期 n 都非空；泛型定理的空 S 分支合法。d=0 时坐标和为空，结论在相容前提下退化为 0≤0，没有除以 d。全局 C∞ 及经典 frontier 零值依旧是明确前提，未变成一般弱 H²∩H¹₀ 类的边界值。保持边界的强 H² 密度、经典/弱 Hessian 识别后的估计传递及原多面体穷竭仍待，未将本批描述为完整 P023。

## 全部声明逐项结论

名称统一带前缀 `Carleman.`；源码行为固定 `ClassicalConvexHessian.lean`，raw 行为固定完整类型起点。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 12 / 43923 | `exists_positive_level_layer` | PASS；紧致坏点集的真实最大值，含空集分支。 |
| 41 / 43927 | `levelLayer_flux_lower_bound` | PASS；实际通量扰动、真实闭层支撑及 κ 非负给全点下界。 |
| 70 / 43940 | `continuous_integrableOn_bounded_sublevel` | PASS；连续函数在原紧闭包可积并限制到 S。 |
| 75 / 43943 | `levelCutoff_integral_tendsto` | PASS；真实可测性、indicator 支配和包括边界的全部点极限。 |
| 106 / 43949 | `levelCutoff_mass_bound` | PASS；同一权的精确质量恒等式和与 ε 无关的有限 M。 |
| 129 / 43954 | `levelCutoff_defect_lower_bound` | PASS；乘积可积性、负系数比较方向和原 Hessian 身份。 |
| 153 / 43967 | `classical_level_hessian_defect_nonneg` | PASS；先固定 δ 令 ε 趋零，再令 δ 趋零，完整尾段合法。 |
| 176 / 43975 | `classical_level_hessian_le_laplacian` | PASS；两个真实可积平方项拆分，完整有序 Hessian 常数 1。 |
| 187 / 43982 | `halfspaceSmoothInner_classical_hessian_bound` | PASS；原指数和内域及真实边值内部清偿全部几何/通量条件。 |

## 固定依赖与本地证据

实际 Carleman 导入闭包 **226 文件**，其中 **225 旧文件**相对 mathematical_base 逐 Git blob 不变，唯一新增数学模块为本批模块。本次完整读取 `SmoothLevelCutoff`，核对同一 η、κ 的真实微分、完整支撑、紧性、indicator 极限以及两个积分调用；直接读取 `ConvexBoundaryFlux`、`HalfspaceSmoothExhaustion`、`LevelBoundaryHessian` 的实际实现，核对原通量、原内域、真实边界正规性与零数据来源。T249 的完整有序平方和和两次分部积分闭包相对已验收版本未变。另直接核对 mathlib DCT 与连续函数在紧集可积的实际类型/测度前提，未把抽象收敛或积分资格当成原问题输入。

T250 冻结报告全文已读；单文件提交 `748e173a8693b7ad9cf3db536b36ce5c1983ab87`，checked_sha 为本报告 base、reviewed_at=`2026-10-20T09:39:00+00:00`，20/20 PASS。固定 proof 中的报告与该提交逐字节相同（10885 bytes，SHA256 `275abcbe9476d8c3e5fa5878dca808eff58cc33f5ffa39417a6b6e377ff2c98e`）。正式依赖报告没有代替本次实际调用及新增极限的审查。

源码、独立清单、T251/C267 台账和 raw 的 9 项精确匹配；实际均为 theorem。Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入及全部 9 项 `#check`/`#print axioms` 齐全；AGENTS、PROJECT_OPERATIONS、state/README 与此前已读协议摘要一致。

- `/tmp/carleman-t251-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T09:40:00.115214+00:00`；实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 的执行记录均 exit 0。
- `/tmp/carleman-t251-local-source-manifest.txt`：**1048 项、113751 bytes**，SHA256 `f58d58b585284be37be71d4b5db704a2ecf9ba315642f21062a7b3f5906c092a`。独立枚举固定提交全部 tracked `.lean` 和三个工具链配置，路径集合、唯一性与逐项 SHA256 全部匹配真实 Git blob。
- `/tmp/carleman-t251-target-build.log`：**3411 jobs** 成功，111 bytes，SHA256 `bbfaf783980e4222de0c8f4be94edd877bc05c9516de36b3005d2c3479640210`。`/tmp/carleman-t251-build.log`：**4290 jobs** 成功，80 bytes，SHA256 `406eaf5a4d858e929497a9a36c86de971c03ff606a66db4d5a7bcc39bccfaf32`。`/tmp/carleman-t251-axioms.log` 为 0 bytes。
- `/tmp/carleman-t251-classical-convex-hessian-local-axioms.txt`：**3381069 bytes**，SHA256 `4669ca7bfc253f2e8f989d0bb8a4be4265b6e228ac0accb0b77a627b0a118e23`。9 项完整类型和公理逐项核对；全文件 4033 个公理列表均仅含 `propext`、`Classical.choice`、`Quot.sound`，另有 10 个无公理记录。实际尾部确认 **10061 声明递归审计 PASS**；全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，无 sorryAx 或新增数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，未重跑全库、未查询远端 CI/看板，未把本地成功称为 CI 成功。

无修复项。接受 **AUXILIARY 原光滑内域的经典统一 Miranda–Talenti 估计**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、公理工具或其他报告，不 push。
