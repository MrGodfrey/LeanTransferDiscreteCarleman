# T148 / C164 独立本机验收

- `checked_sha`: `a3a39eadfe9f18fee3bdd0a60b07cd5856bd3dbb`
- `base_commit`: `e3a9cd6fa7134bdb9d924c56686a14d0bb64029d`
- `reviewed_at`: `2026-10-19T10:06:40+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：任意正维正坐标盒上，同一真实光滑热通量的闭面符号、真实体面散度积分公式及原开盒上 ∫div V≤0。**P024 / prop:continuousCE 不提升，原文覆盖保持 17/26。**

本 Agent 直接读取固定 Git 对象中四模块全部证明与 15 项完整展开类型，核对原稿、T148 分析、MATH_SPEC、C164/T148 清单、治理协议、关键依赖及 pinned mathlib 的实际散度定理和保测定理。另行查询正式 main CI，独立下载同次原始工件并逐字节核验。执行者说明、旧验收和 CI 未替代数学判断。后续 T149 工作树与动态 `.ci/axioms.txt` 不纳入本次证据。

## 原文对应与严格范围

固定 `paper/main.tex:2696–2704` 设置同一 z=exp(L)u，并使用真实面通量 2q∂νφ|∂νz|²≤0 及空间 Green 积分。本批清偿其中**盒域、全空间 C∞ 输入、经典逐点零边值**下的实际空间散度积分步骤。原 `2672–2675` 的全域类、全部弱轨道、原允许 C² 时间权和最终时空估计，以及 `2711–2730` 的系数估计、吸收、密度和时间反射，均不是本批结论。

输入 a,b 是任意实端点，最终要求各边 aᵢ<bᵢ，中心 c 位于该原开盒；没有单位盒、原点或固定长宽比限制。λ 对应 Lean `l`，只要求 λ≥0；固定时刻要求 q(t)≥0，允许 λ=0、q(t)=0。L、u、k、p 是任意全时空 C∞ 实函数，L(s,y)=q(s)ρ(y)，ρ(y)=exp(−λ‖y−c‖²)−2，且 u 对原 frontier 在全部时间为零。此 C∞ 与全时间经典边值是辅助阶段的公开适用条件，未把它们冒充原 C² q 或 H²∩H¹₀ 资格。

p 对应原 Ψ，k 是原通量的同一系数输入；最终定理允许任意光滑 k、p。它涵盖后续将指定 k、Ψ 代入的光滑情形，但本批不负责该实例的原低正则性清偿。原中心还需在观察区域内以完成后续吸收；本批的边界符号只需要中心在盒内，因此更广的中心条件不会削弱本辅助结论。

## 全部 15 项声明

名称省略 `Carleman.`；源码位置相对于该目录。源行来自固定提交，完整类型行来自本次独立下载并逐字节比对的原始 `axioms.txt`。顺序与固定两处台账及交付清单完全一致。

| # | 声明 | 固定源位置 / 完整类型行 | 独立结论 |
|---|---|---|---|
| 1 | `coordinateBoxFunctional` | `Geometry/CoordinateBoxHalfspaces.lean:12` / 29889 | PASS；真实坐标基的 Riesz 对偶；上侧取负、下侧取正。 |
| 2 | `coordinateBoxThreshold` | `Geometry/CoordinateBoxHalfspaces.lean:16` / 29891 | PASS；真实阈值为上侧 −bᵢ、下侧 aᵢ。 |
| 3 | `coordinateBoxFunctional_apply` | `Geometry/CoordinateBoxHalfspaces.lean:19` / 29893 | PASS；逐点证明泛函等于上侧 −xᵢ、下侧 xᵢ。 |
| 4 | `openCoordinateBox_halfspaces` | `Geometry/CoordinateBoxHalfspaces.lean:28` / 29896 | PASS；全部严格半空间精确等于原开盒；双向包含，无额外域限制。 |
| 5 | `closedCoordinateBox_halfspaces` | `Geometry/CoordinateBoxHalfspaces.lean:44` / 29900 | PASS；全部弱半空间精确等于原闭盒；双向包含。 |
| 6 | `coordinateBoxFunctional_normal` | `Geometry/CoordinateBoxHalfspaces.lean:60` / 29904 | PASS；真实归一化 Riesz 外法向为上侧 eᵢ、下侧 −eᵢ。 |
| 7 | `coordinateBox_face_witness` | `Geometry/CoordinateBoxHalfspaces.lean:67` / 29908 | PASS；内部构造指定坐标取端点、其余坐标取中点的见证，全部其它不等式严格。 |
| 8 | `box_face_gaussian_heat_flux` | `Spatial/BoxHeatBoundary.lean:13` / 29915 | PASS；原 frontier 上全时间零值推出同一 V 的上侧 Vᵢ≤0、下侧 −Vᵢ≤0，覆盖闭面含棱角。 |
| 9 | `coordinateDivergence` | `Spatial/SmoothBoxDivergence.lean:15` / 29942 | PASS；实际 Euclidean 基方向上的真实 Fréchet 导数分量和。 |
| 10 | `coordinateDivergence_contDiff` | `Spatial/SmoothBoxDivergence.lean:18` / 29945 | PASS；同一实际散度的 C∞，由方向求导与有限和内部给出。 |
| 11 | `smooth_closed_box_divergence` | `Spatial/SmoothBoxDivergence.lean:22` / 29948 | PASS；实际连续线性换元、真实链式导数及保测体积分，满足 mathlib 散度定理全部前提。 |
| 12 | `openCoordinateBox_ae_closed` | `Spatial/SmoothBoxDivergence.lean:64` / 29960 | PASS；有限坐标端点零测和真实保测拉回给开闭盒 a.e. 相等。 |
| 13 | `smooth_open_box_divergence` | `Spatial/SmoothBoxDivergence.lean:74` / 29963 | PASS；由同一 integrand 的集合 a.e. 同一性得到原开盒的精确体面公式。 |
| 14 | `coordinateFacePoint_mem_closed` | `Spatial/BoxHeatFluxIntegral.lean:13` / 29975 | PASS；真实 insertNth 面参数点在整个闭盒中，含端点及横截面边缘。 |
| 15 | `box_gaussian_heat_flux_integral` | `Spatial/BoxHeatFluxIntegral.lean:23` / 29981 | PASS；同一真实 V 的固定时间切片可微且可积，精确散度公式和上下侧符号给原开盒 ∫div V≤0。 |

## 实际盒几何、面见证与同一闭面通量

对 j=(i,upper)，定义域统一采用 bⱼ<Lⱼx。因此上侧 Lⱼx=−xᵢ、阈值 −bᵢ，下侧 Lⱼx=xᵢ、阈值 aᵢ；实际双向证明分别给开盒和闭盒，未更换边界集合。外法向由 −‖Lⱼ‖⁻¹Riesz(Lⱼ) 构造，坐标对偶范数为1，故恰为上侧 eᵢ、下侧 −eᵢ，无额外比例因子或方向翻转。

`coordinateBox_face_witness` 内部选 wᵢ 为指定端点，其余坐标为 (aⱼ+bⱼ)/2。不同坐标的不等式由真正中点严格性给出；同坐标另一侧由 aᵢ<bᵢ 给出。故 T147 的实际相对内部见证输入已在本批盒实例中清偿，未把存在见证作为最终外部前提。

`box_face_gaussian_heat_flux` 将实际原 frontier 零值转换到精确相等的半空间域，再调用固定 T147 闭面结果。已重读该依赖：面内部的真实局部平面零值由域几何推出，真实切向/时间导数为零、法向梯度表示由实际导数证明；闭面含棱角通过同一 V 的连续性和真实相对内部逼近传递符号。这里是在每个指定面的法向下取 V·n，不给角点强加唯一法向。标准基收缩严格得到上侧 Vᵢ≤0、下侧 −Vᵢ≤0，且 z 始终是同一 exp(L)u。

## 真实坐标换元和 Bochner 散度定理

`coordinateDivergence F` 是 Σᵢ fderiv(Fᵢ)(x)eᵢ。证明令 e 为实际 `PiLp.continuousLinearEquiv` 的逆，从函数坐标 Fin(d+1)→ℝ 到 Euclidean 空间，设置 gᵢ=Fᵢ∘e、gᵢ′(x)=DFᵢ(e x)∘e。实际 `HasFDerivAt.comp` 给该导数，且逐坐标证明 e(Pi.single i 1)=Euclidean 标准基 eᵢ，因此 g 的真实散度恰等于 coordinateDivergence F∘e。

独立读取 pinned mathlib `MeasureTheory/Integral/DivergenceTheorem.lean:297–308` 的 `integral_divergence_of_hasFDerivAt_off_countable'`，逐项确认调用条件：

1. a≤b 由给定逐坐标弱不等式供应；一般散度公式因此也允许退化边长。
2. 例外集取空集并提供 countable_empty。
3. 每个 gᵢ 在闭盒连续，由 hF 的真实连续性与 e 的连续性构造。
4. 所有内部点的真实 Fréchet 导数由上述链式法则供应，实际更强地在全空间成立。
5. 散度在闭盒上的可积性，由同一实际散度的 C∞、e 的连续性以及紧 Icc 上的连续可积性内部证明。

没有将目标散度公式或候选导数作为假设。体积分换元调用实际 `PiLp.volume_preserving_toLp` 与 e 的 measurableEmbedding，并证明 e⁻¹(closedCoordinateBox a b)=Icc a b。已直接核对 `Measure/Haar/InnerProductSpace.lean:134–140`：toLp 与 ofLp 两个方向均保持各自的真实 Lebesgue volume。此处依赖的是保测性；并未把函数空间的 sup 范数与 Euclidean 范数误认相同，也没有使用带未知常数的范数等价代替体积身份。

所得面公式严格是 Σᵢ[∫Fᵢ(insertNth bᵢ y)dy−∫Fᵢ(insertNth aᵢ y)dy]，横截面为 Icc(a∘succAbove,b∘succAbove)。这是原实际侧长区间上的标准坐标参数化，没有先缩放到单位盒，故无遗漏侧长乘子。插入固定端点的切向坐标基就是剩余 Euclidean 标准基，面积因子为1；上侧减下侧的方向来自同一散度公式。代码使用这些精确参数面 Lebesgue 积分，未另外宣称一般 Hausdorff 面测度或任意多面体的 Green 定理。

原维数写成 d+1，故最终积分定理覆盖所有正维，包括一维盒。d=0 横截面是 Fin 0→ℝ，其 Lebesgue 测度为单点单位质量，面项正确成为端点值；不是被误作零测度。坐标几何及开闭盒 a.e. 定理本身也允许零维；最终入口不声称零维 PDE。

## 开闭盒 a.e. 身份、可积性及最终符号

`openCoordinateBox_ae_closed` 先用有限乘积测度上每个 Ioo 与 Icc 的端点零测得到集合 a.e. 身份，再经真实 `volume_preserving_ofLp` 拉回 Euclidean 体积。它不把开闭盒说成逐点相等，也不遗漏角点；任意端点顺序都能使用这条 a.e. 定理。`smooth_open_box_divergence` 对**同一真实散度**用 setIntegral_congr_set 转移精确公式。

最终令 Fᵢ(y)=Vᵢ(t,y)，V 正是固定点态热恒等式中的 `pointwiseHeatFlux`。光滑性由 L、u、k、p 和 z=exp(L)u 内部给出，再通过真实时间切片嵌入得到 Fᵢ 的 C∞。`spaceTime_spatialD` 逐项证明原时空空间方向微分之和等于 coordinateDivergence F；没有换成另一个代数命名的通量或散度。

`coordinateFacePoint_mem_closed` 用 insertNth 的同坐标和 succAbove 两个分支证明横截面每个参数点确在原闭盒中，端点等式由实际插入坐标给出，故前述闭面符号适用于面参数域的每一点。上侧面积分≤0，下侧面积分≥0，每个上减下≤0，再有限求和得到原开盒上的 ∫div V≤0，方向准确。

这里积分不是依靠不可积函数的默认 Bochner 值而变成零：体散度的可积性已在调用散度定理时构造；每个面复合函数连续，横截面 Icc 紧，故面函数也实际可积。最终体散度在开盒的可积性亦由同一闭盒可积性及上述集合 a.e. 身份传递。符号引理本身的较弱前提没有掩盖这些实际可积性事实。

本批没有除以 λ、q(t) 或盒边长，也未引入未知常数、单元数、网格、周期 T 或目标估计作为前提。它是固定时间的空间结论；尚未经过时空 Fubini 消去时间通量，不能从本报告推出原任意 T 的完整时空 Carleman 估计。

## 固定依赖、公理与构建

四模块为 7+1+5+2=15 项，均由固定 `Carleman.lean` 导入，均在固定 `tools/CheckAxioms.lean` 中有完整类型和公理检查。声明清单与实际源码、C164/T148 两处台账一致；新代码没有 sorry、admit、新数学 axiom 或 native_decide。

递归项目 import 闭包共 **102** 模块，其中 **98** 个旧模块全部与基线逐字节相同。`HalfspaceHeatBoundary` 的 **95** 模块闭包与 C163 的已验收版本 e3a9cd6f… 全同；`PlaneHeatFlux` 的 **87** 模块闭包与 C162 的 `c598090a2e592f2e2a5441e5d05eaec994e9b1b3` 全同；`SpacetimeHeatIdentity` 的 **81** 模块闭包与 C161 的 `ccbd7a887ed37afbc4d4e530d06b885350e74b3a` 全同。已另行重读实际半空间面几何、Riesz 法向、光滑平面导数、通量收缩、Gaussian 法向符号及坐标盒定义；旧验收仅作为版本追溯，见 [T147](T147-local-acceptance.md)、[T146](T146-local-acceptance.md)、[T145](T145-local-acceptance.md)。

Lean pin 为 4.35.0，mathlib pin 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`；本机实际 mathlib HEAD 匹配、工作树干净。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。实际读取定向日志 `/tmp/carleman-t148-box-flux-integral-target2.log`：3260 jobs 成功；`/tmp/carleman-t148-box-divergence-build.log`：4005 jobs 成功；`-axioms.log`：7476 项递归审计成功。

固定公理审计主体与基线一致，对所有 privateToUserName 属于 Carleman 的环境常量递归 collectAxioms，只允许 propext、Classical.choice、Quot.sound。原始产物末行实报 **7476** 全量递归声明 PASS；其 2747 条非空公理打印记录与 9 条无公理打印记录是另一个计数，不混同。全部 15 项有实际类型、公理记录且仅含正常基础公理。固定 CI 脚本校验实际 mathlib HEAD 后构建 Carleman，再实际执行完整 CheckAxioms。

## 独立正式 CI 与原始工件

本 Agent 实际查询 [main CI run 39234467863 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39234467863/attempts/1)：event=push，head_branch=main，head_sha=`a3a39eadfe9f18fee3bdd0a60b07cd5856bd3dbb`，顶层 completed/success，updated_at=`2026-10-19T10:06:07Z`。三项 job 均 completed/success：

| job | 实际 ID | 最终结果 |
|---|---:|---|
| lean | 118000080025 | success |
| state-check | 118000080342 | success |
| dashboard / snapshot | 118001687886 | success |

本 Agent 以 gh run download 从同次 run 独立下载两原始工件，两个进程 exit 0。实际工件元数据绑定同 SHA：

| 工件 | 实际 artifact ID | 归档 bytes | 归档 SHA256 |
|---|---:|---:|---|
| lean-ci-result | 12177184264 | 492 | `e41a07f2ac4ef9606a0e5ba01bebe37a09880377bbb76dded1bc445ea718d0d8` |
| lean-declaration-evidence | 12177104672 | 213452 | `50c64f83f981a2794b9c983b4993c44e8a636657522dd2a15273b0c1b2c1c468` |

实际读取 `/tmp/carleman-t148-box-divergence-main-ci/result.json`：status=PASS，checked_sha 与 source_head_sha 均等于本报告固定 SHA，ci_url 为同 run/attempt，finished_at=`2026-10-19T10:04:50.938484+00:00`；targets=[Carleman]；Linux Lean 4.35.0 编译器提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 与上述 pin 一致。

实际下载 `/tmp/carleman-t148-box-divergence-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t148-box-divergence-local-axioms.txt` **逐字节相同**，均为 **2297803 bytes**，原始文件 SHA256 **`cf8815c27e3e2095263233d1ea809d5668e41e9270b7fd22d26560d2d7ea39b6`**。原始文件与 ZIP 归档的 hash 分开记录。远端文件含全部 15 项实际完整类型及 7476 项递归公理 PASS。

## 签发结论

**T148 / C164 在本固定版本可登记为 REVIEWED，scope 保持 AUXILIARY。** 全部 15 项实际语义及依赖公理 PASS，未发现需修复的实现缺陷。原一般多面体、弱 Green/法向迹、原 C² 时间权与完整弱轨道、完整时空积分、heatcross 控制/吸收、密度与时间反射仍未由本批清偿。P024 不提升，原文保持 17/26。报告定稿后冻结内容与 reviewed_at；仅提交此报告，不修改实现、台账、root/audit 或原稿，不推送。
