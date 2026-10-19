# T157 / C173 独立本机验收

- `checked_sha`: `5eb3c89b2d38b27beedd3ce5e9192704def15e00`
- `base_commit`: `b65d78fa150ea0cc5c0cd7d7b3342e7498b1bc50`
- `reviewed_at`: `2026-10-19T11:27:44+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：逐坐标反射平均的真实全偶空间核、局部奇性条件下的平面卷积零值，以及全部全空间实值 L² 状态的实际卷积强收敛。**P024 / prop:continuousCE 不提升，原文覆盖保持 17/26。**

本 Agent 独立读取固定 Git 对象中五模块全部证明、29 项完整展开类型、原 `paper/main.tex:2672–2731`、T157 分析、MATH_SPEC、固定 C173/T157 清单及关键依赖。AGENTS、PROJECT_OPERATIONS、state/README 与此前已读协议逐字节相同。自行查询同 SHA 的正式 CI，独立下载原始 result/raw 并与固定产物逐字节比较。后续 EvenLocalMollification、CoordinateOddPart、DoubleOddSlab、OddPoissonExtensionValue、BoxPoissonExtensionValue 草稿及动态 `.ci/axioms.txt` 排除。历史验收、CI 及执行者说明不替代本次实际数学判断。

## 原稿对应与明确局限

原连续 CE 的最终范围是全部 v∈H¹(0,T;H)∩L²(0,T;D(A))、周期迹、原 qclass 和两个时间方向；原证明2696行先取光滑状态，2704行使用 H²∩H¹₀ 的面通量，2730行再以密度推广。本批针对这一密度步骤提供空间卷积工具，并非已证明原完整密度。

`evenSpatialMollifier_convolution_zero` 明确输入：在当前核从某个平面点 x 所见的球中，f 关于该平面 **a.e. 为奇**。本批没有为任意原盒 H²∩H¹₀ 状态构造满足该条件的全空间延拓，也没有证明保持边界的 H² 收敛、全部时间轨道或一般多面体密度。强收敛结论是每个原全空间实值 L² 类的卷积值误差；一、二阶弱导数的局部卷积身份及其同时收敛仍属后续。不能将局部奇性当作已经由原零边界假设清偿。

## 全部 29 项公开声明

名称省略 `Carleman.`，源位置相对于 Carleman。源行来自固定提交，完整类型行来自与固定本机产物逐字节相同的独立下载 raw；清单与交付 manifest、固定 C173 和 T157 完全一致。

| # | 声明 | 固定源位置 / 完整类型行 | 独立结论 |
|---|---|---|---|
| 1 | `coordinateReflection_zero` | `Spatial/LocalOddConvolution.lean:15` / 31129 | PASS；过原点的实际仿射坐标反射等于该坐标符号翻转。 |
| 2 | `coordinateSignFlip_involutive` | `Spatial/LocalOddConvolution.lean:20` / 31132 | PASS；逐坐标检查真实线性等距翻转的自反性。 |
| 3 | `coordinateReflection_sub_fixed` | `Spatial/LocalOddConvolution.lean:26` / 31134 | PASS；x_r=c 时精确有 x−R_c(y)=R_0(x−y)，偏移和符号正确。 |
| 4 | `convolution_zero_of_local_odd` | `Spatial/LocalOddConvolution.lean:40` / 31139 | PASS；真实保测换元、局部 a.e. 奇性和核全偶性给 I=−I，从而平面点卷积严格为零。 |
| 5 | `coordinateSignFlip_commute` | `Spatial/EvenCoordinateKernel.lean:12` / 31148 | PASS；任意两坐标翻转交换，包含相同坐标。 |
| 6 | `SpatialTest.evenCoordinate` | `Spatial/EvenCoordinateKernel.lean:30` / 31151 | PASS；实际测试函数 (κ+κ∘R_r)/2，结构内部保留 C∞ 和紧支性。 |
| 7 | `SpatialTest.evenCoordinate_value` | `Spatial/EvenCoordinateKernel.lean:34` / 31153 | PASS；实际值精确等于原核与反射核的平均。 |
| 8 | `SpatialTest.evenCoordinate_invariant` | `Spatial/EvenCoordinateKernel.lean:41` / 31157 | PASS；由 R_r²=Id 得当前坐标偶性。 |
| 9 | `SpatialTest.evenCoordinate_preserves_invariant` | `Spatial/EvenCoordinateKernel.lean:47` / 31161 | PASS；反射交换性保证已有其他坐标偶性不被平均破坏。 |
| 10 | `SpatialTest.evenCoordinate_nonneg` | `Spatial/EvenCoordinateKernel.lean:53` / 31166 | PASS；两项真实非负核平均仍非负。 |
| 11 | `SpatialTest.evenCoordinate_integral` | `Spatial/EvenCoordinateKernel.lean:59` / 31170 | PASS；两项都实际可积，保测反射使积分精确保持。 |
| 12 | `SpatialTest.evenCoordinate_support` | `Spatial/EvenCoordinateKernel.lean:73` / 31173 | PASS；线性等距反射保持原点球，平均不会扩大原球形支集。 |
| 13 | `SpatialTest.evenCoordinates` | `Spatial/EvenSpatialMollifier.lean:15` / 31176 | PASS；对给定有限坐标列表真实 foldr 平均，不是外加对称核。 |
| 14 | `SpatialTest.evenCoordinates_invariant` | `Spatial/EvenSpatialMollifier.lean:19` / 31179 | PASS；列表内全部坐标均不变；归纳处理新坐标和已有坐标两种情形。 |
| 15 | `SpatialTest.evenCoordinates_nonneg` | `Spatial/EvenSpatialMollifier.lean:31` / 31184 | PASS；任意有限列表迭代保持非负性。 |
| 16 | `SpatialTest.evenCoordinates_integral` | `Spatial/EvenSpatialMollifier.lean:38` / 31188 | PASS；任意有限列表迭代精确保持原积分，无基数因子。 |
| 17 | `SpatialTest.evenCoordinates_support` | `Spatial/EvenSpatialMollifier.lean:46` / 31192 | PASS；整个迭代保持同一个球半径。 |
| 18 | `evenSpatialMollifier` | `Spatial/EvenSpatialMollifier.lean:55` / 31195 | PASS；对真实 shrinkingBump 归一化核按全部 Fin d 坐标平均。 |
| 19 | `evenSpatialMollifier_invariant` | `Spatial/EvenSpatialMollifier.lean:58` / 31197 | PASS；最终核对每个实际坐标翻转逐点不变。 |
| 20 | `evenSpatialMollifier_nonneg` | `Spatial/EvenSpatialMollifier.lean:62` / 31201 | PASS；全部维数、全部 n、全部空间点的核非负。 |
| 21 | `evenSpatialMollifier_integral` | `Spatial/EvenSpatialMollifier.lean:66` / 31204 | PASS；真实 Lebesgue 积分精确为1。 |
| 22 | `evenSpatialMollifier_support` | `Spatial/EvenSpatialMollifier.lean:69` / 31207 | PASS；支集仍在半径2/(n+1)的原点开球，随 n 收缩。 |
| 23 | `evenSpatialMollifier_convolution_zero` | `Spatial/EvenSpatialMollifier.lean:74` / 31210 | PASS；内部供应同一实际核的偶性与支持界，保留所需局部 a.e. 奇性输入。 |
| 24 | `SpatialTest.reflected_kernel_convolution` | `Spatial/EvenKernelConvolution.lean:14` / 31219 | PASS；真实反射核卷积等于反射 L² 状态的卷积再反射，代表替换仅在合法 a.e. 换元后进行。 |
| 25 | `SpatialTest.evenCoordinate_convolution` | `Spatial/EvenKernelConvolution.lean:34` / 31226 | PASS；两个真实可积卷积精确平均，系数1/2正确。 |
| 26 | `SpatialTest.evenCoordinates_converges` | `Spatial/EvenMollifierLimit.lean:12` / 31234 | PASS；对全部 L² 状态的基础 a.e. 收敛，通过真实反射类与有限平均传至任意有限坐标列表。 |
| 27 | `evenSpatialMollifier_converges` | `Spatial/EvenMollifierLimit.lean:44` / 31248 | PASS；内部使用真实初始 mollifier 收敛清偿第26项前提，覆盖任意全空间 L² 类。 |
| 28 | `evenSpatialMollifier_square_error_tendsto` | `Spatial/EvenMollifierLimit.lean:52` / 31256 | PASS；实际 MemLp、单位质量核收缩与 a.e. 极限给真实平方误差积分趋零。 |
| 29 | `evenSpatialMollifier_L2_error_tendsto` | `Spatial/EvenMollifierLimit.lean:65` / 31266 | PASS；误差 MemLp 内部供应，平方积分等于真实 L² 范数平方，再取非负平方根。 |

## 对称化核的真实几何与质量

通用 ContDiffBump 的中心反演对称性不足以推出每个坐标单独偶对称；本批没有作此推断。`coordinateSignFlip r` 是实际 Euclidean 坐标翻转的线性等距同构；`coordinateReflection r c` 是再平移2c e_r的仿射同胚。已重读坐标公式、保测证明和自反性：Lebesgue 测度由线性等距同构及平移精确保持，无额外 Jacobian 因子。

`SpatialTest` 的 value、ContDiff ℝ ∞、HasCompactSupport 和 tsupport 条件是真实结构字段。反射使用实际仿射 pullback；addTest 和 smulTest 直接在函数值上相加、乘实数，并证明对应光滑和紧支性质。每次平均的值因此确为 (κ(x)+κ(R_r x))/2。反射交换性证明了已有坐标的偶性在后续平均中保留，任意列表归纳也容许重复项；最终 Finset.univ.toList 确实含全部 Fin d 坐标。

κ 与反射核均由 C∞ 紧支性给实际可积性，因此拆分积分合法；保测换元给每次质量不变。归一化初始核真实质量为1，反射平均不引入2^d或列表长度的损失。非负性逐步保持。支持证明在原点球外同时使原核及反射核为零，使用真实等距范数身份；保持的是同一半径2/(n+1)，并非放大的球或仅某个未知紧集。开球边界上核值也为零，故后续局部奇性只需开球内。全部 n 包含0；d=0时坐标列表为空，质量及强收敛结论仍适用，涉及 r:Fin d 的平面语句自然无实例。

## 局部奇性与平面零值

先把真实卷积写成 I=∫κ(x−y)f(y)dy。若 x_r=c，则 x−R_c(y)=R_0(x−y)。使用实际 R_c 保测且为可测嵌入的换元，得到 I=∫κ(x−R_c(y))f(R_c(y))dy。核的逐坐标偶性把第一因子还原为κ(x−y)。若该因子非零，支持界精确推出y∈ball(x,δ)，此时所给 a.e. 奇性才用于第二因子；若核为零则被积函数两边均零。于是 I=−I，得到严格点态零值。

这里没有假设 f 在整个空间奇、没有把实际盒或其他域认作关于每个边界面全局对称。一般第4和第23项不要求 f 可测或可积：它们是 mathlib 总定义 Bochner 积分的合法恒等式，**并不输出任意 f 的可积性**。在后面的 L² 应用中，光滑紧支核与 L² 状态的局部可积性另行保证卷积在每个 x 实际可积；零值结论因此可用于真实卷积，而非利用默认零积分替代所需边界逼近。尚未构造所需局部奇延拓这一限制不能省略。

## 真实 L² 反射、a.e. 代表及有限平均

`coordinateReflectionLp` 是保测仿射拉回得到的实际 Lp 类，具有真实范数保持和 a.e. 代表身份 u_r=u∘R_r；不是任意指定的函数。已重读相应定义及代表证明。在反射核卷积恒等式中，先作实际反射换元，再经 s↦R_r x−s 的保测变换拉回代表的 a.e. 身份，结合线性反射的减法公式及自反性得到精确结果。因此对每个固定 x，两个实际积分相等；没有把 Lp 的 a.e. 代表相等直接升级为处处相等。

平均卷积公式在拆分积分前分别证明原核及反射核乘 u(x−s) 可积，使用 Lp2⇒LocallyIntegrable 与紧支连续核。有限平均的收敛归纳同时用于 u 和真实反射类 v，分别取得 a.e. 极限，再把 v 的收敛和代表身份经保测反射拉回。三个满测集上 v(R_r x)=u(x)，两项极限的平均即u(x)。此处基础假设必须是对全部 L² 状态成立，类型确实将 ∀u 放在其中；最终第27项用已证初始核的真实 a.e. 收敛内部清偿，不假定目标全偶核已经收敛。

基础 `spatialMollifier_converges` 使用半径趋零和外/内半径恒比2，配合任意 L² 状态的局部可积性调用 mathlib Lebesgue 微分型卷积定理；其原卷积顺序与本批顺序通过真实实乘法卷积交换律连接。没有假定状态连续、紧支、非负或具有 Sobolev 正则性。异常零测集可依赖状态及有限坐标列表，这与最终 ∀u、a.e. x 的量词一致。

## 全状态 L² 强收敛

已独立重读实际 `convolution_memLp_norm_le`：取真实 sqrt(κ)，由加权 Cauchy–Schwarz 给 (κ*u)²≤κ*u²；κ及u²实际可积，卷积可测，Fubini 的积分乘积公式和质量1给卷积的 MemLp2 与范数不增。最终全偶核确实满足该引理全部条件，因此每个近似都满足 ∫u_n²≤∫u²，收缩常数始终是1。

实际 `l2_square_tendsto_zero_of_ae_of_energy_le` 将此能量界与 a.e. 收敛组合。它使用可积的平行四边形恒等式，并对可能保持正误差的子列应用 Fatou 于 u_n+u→2u，得到4∫u²≤4∫u²−b的矛盾。没有额外的统一点态支配函数，也没有把仅有一般有界能量当成足以推出强收敛。

平方误差由真实 MemLp 差保证可积，等于 `bochnerL2Norm` 的平方。后者虽定义为 eLpNorm.toReal，但本批在所有使用点先证明 MemLp2，排除把无穷范数转换为0的漏洞；它等于该函数真实 toLp 类的范数。非负平方根连续性给最终范数误差趋零。这就是所有原全空间实值 L² 状态的强收敛，无有限维、光滑代表、紧支或维数相关范数等价前提；当前没有输出 H² 或时空图范数收敛。

## 固定依赖、公理及构建

五模块声明数4+8+11+2+4=29，全部由固定 `Carleman.lean` 导入，在固定 `tools/CheckAxioms.lean` 中有实际完整类型和公理记录，无漏列的新公开或私有辅助声明。新源码无 sorry、admit、新数学 axiom 或 native_decide。

实际 Carleman import 闭包为 **135** 模块，其中 **130** 个旧模块均与数学基线逐字节相同。关键接受版本已逐字节核验整个闭包：CoordinateReflectionLp 的27模块与 C155 `b60153e14ed7085f5828aea582fbc74ade8286aa` 相同；ReflectionTest 的110模块与 C156 `e1774a58f1c57c8a3305173b5195beea5ffd53b7` 相同；StrongMollifierLimit 的72模块与 C131 `f134750df6b8ef03c639f50dd5084d4c42d49272` 相同；FullSpaceInterpolation 的49模块与 C031 `9f8e351a71cbcd8943db0d9056afdd2bc0a1ffe7` 相同。以上关键实际证明已重读，旧验收仅作版本追溯，见 [T139](T139-local-acceptance.md)、[T140](T140-local-acceptance.md)、[T115](T115-local-acceptance.md)。治理前序 C172 已在基线接受，见 [T156](T156-local-acceptance.md)；本批空间核证明不依赖待完成的边界密度或 CE，没有循环。

Lean pin为4.35.0，mathlib pin及本机实际HEAD均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，依赖工作树干净。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。实际读取 `/tmp/carleman-t157-even-mollifier-limit-target3.log` 的3300 jobs成功，以及 `/tmp/carleman-t157-even-spatial-mollification-build.log` 的4044 jobs成功。`-axioms.log` 为空，不能作为PASS证据。

实际审计主体按 privateToUserName 遍历全部 Carleman 常量并递归 collectAxioms，仅允许 propext、Classical.choice、Quot.sound。固定 raw 末行实报 **7652** 项递归PASS；另扫描2897条非空公理打印及9条无公理打印，未见其他公理，未混同打印数与全量递归数。29项本批声明均有完整类型，所列公理均恰为上述三项正常基础公理。CI、构建脚本及依赖配置与此前已核版本相同。

## 独立正式 CI 与原始工件

本 Agent 实际查询 [main CI run 39244043403 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39244043403/attempts/1)：event=push、head_branch=main、head_sha=`5eb3c89b2d38b27beedd3ce5e9192704def15e00`，顶层 completed/success，updated_at=`2026-10-19T11:27:36Z`。最终三项 job 均 completed/success：

| job | 实际 ID | 最终结果 |
|---|---:|---|
| state-check | 118031506247 | success |
| lean | 118031506448 | success |
| dashboard / snapshot | 118033857698 | success |

本 Agent 从同 run 自行 gh run download 两份原始工件，两下载进程 exit 0；实际 artifact 元数据均绑定同 SHA：

| 工件 | 实际 artifact ID | 归档 bytes | 归档 SHA256 |
|---|---:|---:|---|
| lean-ci-result | 12183410600 | 492 | `9f0200ec63aae06087461778e695736048516dfaef93f0651d234ae9c45f5f29` |
| lean-declaration-evidence | 12182154983 | 221595 | `008e7722354a915da028b947c3da347a70990e4d9f26fa6cf47ec19b42aca878` |

实际读取 `/tmp/carleman-t157-even-spatial-mollification-main-ci/result.json`：status=PASS，checked_sha 与 source_head_sha 均等于本报告固定 SHA，ci_url 为同 run/attempt，finished_at=`2026-10-19T11:25:08.723670+00:00`，targets=[Carleman]；Linux Lean4.35.0 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 与上述 pin 一致。

实际下载 `/tmp/carleman-t157-even-spatial-mollification-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t157-even-spatial-mollification-local-axioms.txt` **逐字节相同**，均 **2389934 bytes**，原始 SHA256 **`d5c5692d75c335625cba58e18415045a63ae25a3cfd32853453fcc241479d588`**。原始文件 hash 与 ZIP 归档 hash 分开记录；远端 raw 含全部29项完整类型及7652项递归公理 PASS。

## 签发结论

**T157 / C173 可在该固定版本登记 REVIEWED，scope 保持 AUXILIARY。** 29项声明的语义、公理及实际同版本证据均 PASS，未发现需修复缺陷。局部奇性仍是明确输入；实际盒奇延拓、保持边界的 H² 密度、全部弱周期轨道及一般多面体尚未由本批清偿。完整 P024 不提升、原文覆盖保持17/26。签发后冻结正文及 reviewed_at，仅单独提交本报告，不改数学、台账、root/audit 或原稿，不推送。
