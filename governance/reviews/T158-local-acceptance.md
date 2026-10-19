# T158 / C174 独立本机验收：实际全盒奇延拓与零边界平滑

- checked_sha / source_sha: `9cc8c5f57aec03ca11ce58ffe86fa6b0ae8f87a8`
- mathematical_base: `5eb3c89b2d38b27beedd3ce5e9192704def15e00`
- reviewed_at: `2026-10-19T11:36:19+00:00`
- reviewer: 独立本机 Agent `/root/accept_spatial_foundations`
- result: **PASS**；axiom_check: **PASS**；scope: **AUXILIARY**。
- 七模块二十五声明通过固定版本验收。C174 可以升级为 REVIEWED 并保持 AUXILIARY；本批不完成原域 H² 图范数密度、完整弱周期轨道 CE 或一般凸多面体情形。P024 不提升，原文完整结果覆盖保持 **17/26**。

## 固定原文和验收范围

逐项读取固定 Git 对象中的实现、二十五项完整展开类型及关键旧依赖，对照原 `paper/main.tex:2657–2664` 的 Dirichlet 实现、`2672–2675` 的完整连续 CE 量词、`2696–2704` 的光滑零边界计算和 `2730` 的密度步骤。原 CE 要求全部 `H¹(0,T;H) ∩ L²(0,T;D(A))` 周期轨道；本批仅提供空间盒的边界保持逼近基础，不能据此声称该密度步骤已经全部完成。

已读取固定 `governance/analysis/T158-odd-box-boundary.md`、`governance/MATH_SPEC.md` 对应段、C174 台账，以及根 AGENTS 与适用治理约定。规格和 CI 仅作范围及证据核对，不代替真实证明审查。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未修改。后续工作树的 WeakH2EvenLocalSmoothing、LocalSmoothingRestriction、BoxDirichletSmoothDensity、BoxCompactSmoothDensity 及动态 `.ci/axioms.txt` 均排除。

## 二十五项声明逐项验收

下表位置全部指 checked_sha。顺序与固定 `/tmp/carleman-t158-odd-box-boundary-declarations.json` 及 C174 的 `lean_declarations` 一致。七模块均进入固定 `Carleman.lean`，二十五声明均进入固定 `tools/CheckAxioms.lean`，已读取每项真实展开类型。

| # | 显式声明 | 固定源码位置 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.evenSpatialMollifier_tsupport_subset` | `Carleman/Spatial/EvenLocalMollification.lean:13` | PASS。实际全偶核的拓扑支集包含于原 spatialMollifier 的拓扑支集；由真实支持闭包和原正半径闭球身份推出。 |
| 2 | `Carleman.evenSpatialMollifier_L2_error_restrict_tendsto` | `Carleman/Spatial/EvenLocalMollification.lean:20` | PASS。任意全空间 L² 状态及任意 K 上，真实卷积误差的限制 L² 范数趋零；真实全空间 MemLp 供应 ENNReal 转实数单调性所需有限性。 |
| 3 | `Carleman.IsWeakSpatialDerivative.local_even_mollification_strong_first` | `Carleman/Spatial/EvenLocalMollification.lean:32` | PASS。开 S、紧 K⊆S、真实局部弱一阶链，给实际 Fréchet 方向导数在 K 上的 L² 强收敛。 |
| 4 | `Carleman.IsWeakSpatialDerivative.local_even_mollification_strong_second` | `Carleman/Spatial/EvenLocalMollification.lean:46` | PASS。两条真实弱导数链给实际二阶张量在 `![e₀,e₁]` 上的 L² 强收敛；未假设全空间 H² 零延拓。 |
| 5 | `Carleman.coordinateReflection_commute` | `Carleman/Spatial/CoordinateOddPart.lean:11` | PASS。不同坐标、任意平面位置的实际仿射反射逐坐标交换。 |
| 6 | `Carleman.coordinateOddPart` | `Carleman/Spatial/CoordinateOddPart.lean:23` | PASS。定义为实际全空间 Lp 差 `u−coordinateReflectionLp r c u`。 |
| 7 | `Carleman.coordinateOddPart_ae` | `Carleman/Spatial/CoordinateOddPart.lean:28` | PASS。由 Lp 减法与保测拉回的 a.e. 代表身份得到原点函数差公式。 |
| 8 | `Carleman.IsOddInSlab` | `Carleman/Spatial/CoordinateOddPart.lean:36` | PASS。真实全空间体积 a.e. 的带内反射反号关系，不是对 Lp 等价类赋予点值。 |
| 9 | `Carleman.coordinateOddPart_odd` | `Carleman/Spatial/CoordinateOddPart.lean:41` | PASS。同面反射自反及 a.e. 拉回使实际奇部分在任意所述带内为奇。 |
| 10 | `Carleman.IsOddInSlab.oddPart_other` | `Carleman/Spatial/CoordinateOddPart.lean:51` | PASS。新反射保留旧坐标与旧带，实际反射交换给旧面局部奇性保持。 |
| 11 | `Carleman.IsZeroOutsideSlab` | `Carleman/Spatial/DoubleOddSlab.lean:13` | PASS。真实全空间 Lp 代表在开坐标区间外 a.e. 为零的明确条件。 |
| 12 | `Carleman.zeroExtend_box_zero_outside_slab` | `Carleman/Spatial/DoubleOddSlab.lean:17` | PASS。实际盒零延拓的示性函数公式内部供应区间外零值。 |
| 13 | `Carleman.IsZeroOutsideSlab.lower_oddPart` | `Carleman/Spatial/DoubleOddSlab.lean:26` | PASS。a<b 时下端奇部分在 `(2a−b,b)` 外为零，原点与反射点均在原带外的条件逐一证明。 |
| 14 | `Carleman.IsZeroOutsideSlab.double_oddPart_lower` | `Carleman/Spatial/DoubleOddSlab.lean:40` | PASS。上端第二次奇化后，下端宽度 b−a 的局部带内仍保留下端奇性。 |
| 15 | `Carleman.double_oddPart_both_faces` | `Carleman/Spatial/DoubleOddSlab.lean:66` | PASS。下端使用第 14 项，上端使用最后一次奇部分的全局反号；不假设双端全局奇性。 |
| 16 | `Carleman.zeroExtend_restrict_of_zero_outside` | `Carleman/Spatial/OddPoissonExtensionValue.lean:12` | PASS。T 可测且实际 u 在 T 外 a.e. 零，才由真实限制/零延拓恢复同一 Lp 元素。 |
| 17 | `Carleman.oddExtendLp_zero_outside` | `Carleman/Spatial/OddPoissonExtensionValue.lean:24` | PASS。S 及反射原像 S 均包含于 T，内部证明实际 oddExtendLp 在 T 外零。 |
| 18 | `Carleman.exists_odd_dirichlet_extension_value` | `Carleman/Spatial/OddPoissonExtensionValue.lean:37` | PASS。构造同一实际 oddExtend jet 和右端的限制，输出原 Poisson 扩展全部字段及精确零延拓 Lp 奇部分等式。一般域几何/测试前提明确保留。 |
| 19 | `Carleman.exists_lower_box_extension_value` | `Carleman/Spatial/BoxPoissonExtensionValue.lean:11` | PASS。任意正边长盒和下侧面，内部供应一般域的全部几何与边界测试前提；常数 2 与真实值公式保留。 |
| 20 | `Carleman.exists_upper_box_extension_value` | `Carleman/Spatial/BoxPoissonExtensionValue.lean:26` | PASS。任意正边长盒和上侧面，内部供应同样前提；原状态、右端和常数 2 不变。 |
| 21 | `Carleman.exists_finite_odd_box_extension` | `Carleman/Spatial/FiniteOddBoxExtension.lean:14` | PASS。任意有限坐标集的真实盒扩展保留 H¹₀、弱负 Laplacian、整个原 jet 恢复、三项 `4^card` 范数界及所有已处理原面局部奇性。 |
| 22 | `Carleman.IsOddInSlab.even_mollification_zero` | `Carleman/Spatial/OddSlabSmoothing.lean:13` | PASS。半径不超过带宽时，实际全偶卷积在对应平面每一点严格零；使用欧氏距离控制坐标差。 |
| 23 | `Carleman.frontier_box_has_coordinate_face` | `Carleman/Spatial/OddSlabSmoothing.lean:28` | PASS。由真实盒闭包和 frontier 非内部性质，得到每个边界点落在至少一个上下坐标面。 |
| 24 | `Carleman.even_mollification_eventually_zero_boundary` | `Carleman/Spatial/OddSlabSmoothing.lean:43` | PASS。有限个正带宽给同一 eventual n，随后量化整个 frontier；包括边与角。 |
| 25 | `Carleman.exists_box_poisson_extension_smooth_boundary` | `Carleman/Spatial/OddSlabSmoothing.lean:58` | PASS。原任意 H¹₀ 弱 Poisson 解内部产生实际全盒扩展、`4^d` 界，以及同一零延拓的全局 C∞ 卷积序列，最终在原整个 frontier 严格零。 |

## 同一实际 Lp 对象与两端局部奇性

`coordinateReflection r c` 是真实坐标仿射反射，保持全空间体积且自反。`coordinateReflectionLp` 是该保测映射的 L² 拉回，奇部分因此是实际 Hilbert 空间减法。第 7–10 项显式使用 `Lp.coeFn_sub`、真实拉回 a.e. 身份及保测反射传递 a.e. 命题；没有把任意选取的 Lp 代表在零测平面上的值当作已定义的迹。

对原零延拓 U，`IsZeroOutsideSlab U r a b` 由实际盒指示公式给出。令 `v=(I−R_a)U`，实际坐标不等式给 v 在 `(2a−b,b)` 外零。再令 `w=(I−R_b)v`。当 `|x_r−a|<b−a` 时，`R_b x` 与 `R_b R_a x` 的第 r 坐标均在上述带外；证明分别从该绝对值不等式的上、下界推出，故两处上端反射项均为零。于是 `w(R_a x)=v(R_a x)=−v(x)=−w(x)`。上端奇性则来自最后一次 `(I−R_b)` 的自反代数。这是真实有限支持下的下端局部带证明，未错误要求一个非零紧支函数关于两平面同时全局奇。

不同坐标的反射保持旧坐标值，因此旧面的带宽不变；实际反射交换使新奇部分仍满足旧面的局部反号关系。证明先拉回各 a.e. 身份，随后在同一个满测集运算，反射代表关系的使用合法。

第 16 项严格以域外零为前提，才证明 `E₀,T(restrict_T U)=U`。第 17 项用 `S⊆T` 和 `R⁻¹S⊆T` 保证实际奇部分在 T 外为零。第 18 项直接令 `V=WeakSobolevJet.oddExtend hS u hu r c`、`F=oddExtendLp hS f r c`，取 v、g 为它们在 T 上的实际限制；继而得到

`E₀,T(value v) = (I−R)(E₀,S(value u))`。

这不是从任意存在性扩展猜出的身份，而是利用真实弱 jet 的 value、实际反射及第 16–17 项逐步证明。后面的局部奇性和卷积使用的正是该零延拓 Lp 元素。

## 原弱方程、全部状态恢复及有限迭代

固定 `IsPoissonExtension hST C u f v g` 实际包含：`v∈dirichletJetSpace T`、`IsWeakNegativeLaplacian v g`、`restrictSubdomain hST v=u`，以及 g、value v、完整一阶 field v 的范数分别不超过原相应范数的 C 倍。原值与所有一阶弱字段通过 jet 等式一起恢复；这里的 H¹₀ 是原测试函数在 H¹ 图范数中的闭包。未将仅有 value 恢复或任意替身状态视为整个弱解恢复。接口并不单独列出 `g|S=f` 字段，本报告亦不把它冒充接口输出；构造本身明确使用实际奇延拓右端。

已复核旧 `BoxPoissonExtension`、`FiniteBoxPoissonExtension`、`PoissonExtensionComposition`、`ExpandedCoordinateBox` 的实际类型与调用。原弱方程由真实全测试反射配对和 H¹₀ 闭包步骤取得，负 Laplacian 的符号未变；两项盒包装内部供应开、有界、凸、非空、反射包含、原/反射内部不交及全部 frontier 测试零值，不将这些作为盒调用者额外前提。值、全梯度和右端各自每次至多乘 2，限制范数至多为全空间范数。

第 21 项从空坐标集的原 u、f 和常数 1 起，按有限集归纳。新 r 尚未处理，因此当前盒在 r 上仍为原 `(a_r,b_r)`，第 12 项的零带条件真实适用。先下反射、再上反射，利用两次精确值身份得到同一 `(I−R_b)(I−R_a)`；新面的局部奇性由第 15 项给出，旧面的局部奇性由异坐标保持引理连续两次给出。几何更新精确为下端 `2a_r−b_r`、上端 `3b_r−2a_r`；依赖类型通过实际域相等运输，没有改换原状态。组合范数常数准确为 `2·(2·4^card)=4^(card+1)`。

常数 `4^card` 只由被处理坐标数量确定，先于所有 u、f 选择；全坐标结果为 `4^d`。没有隐藏的状态相关常数或时间长度因子。d=0 时有限坐标集为空，归纳基例有效，盒 frontier 为空；涉及某一 `r : Fin d` 的辅助定理自然只在该坐标存在时调用。一般限制收敛结论也允许空 K、空 S 的合法输入，不偷加非空紧集条件。

## 实际卷积、严格边界零值与局部导数极限

已读取固定 `EvenSpatialMollifier`、`EvenMollifierLimit`、`LocalOddConvolution`。全偶核来自实际逐坐标反射平均，具有 C∞ 紧支、非负及单位质量，不假设一般 bump 自带径向对称。真实反射换元在平面点 x 上把卷积积分变成其负值；局部带只需覆盖卷积核看到的球。这里输入为真实全空间 L² 元素，核为 SpatialTest，卷积的可积性及光滑性由实际核/Lp 定理供应，不是借用不可积积分的默认零值。

第 22 项用 `|y_r−c|≤‖y−x‖`，把球内点变成带内点；半径≤带宽即足够。第 23 项从 `closure(openBox)=closedBox` 和边界点不属内部推出某个坐标等于 a 或 b，没有把边界零测性当作逐点零值依据。第 24 项先以有限全称的 eventual 合并取得同一 n，使所有坐标半径均小于正边长；之后才对任意 frontier 点选取其坐标面。故量词确为 `∀ᶠ n, ∀ x∈frontier Ω, convolution_n(x)=0`，而不是每个点各有不可统一的序号。棱边和角点只需任选一个已有坐标面即可，全部覆盖。

第 2 项先使用真实全空间 L² 收敛，再用限制测度单调性夹逼；卷积减原函数是实际 MemLp，保证 `ENNReal.toReal_mono` 使用时总范数有限。K 不需被另加可测性或有限体积假设。第 3–4 项则明确要求 K 紧、K⊆开 S；原紧缓冲引理保证足够小的真实核支持在 S 内，全偶核的 tsupport 包含性使同一资格成立。已读取 `DomainConvolution` 和 `LocalHessianConvolution`：它们在真实反射核测试上应用局部弱分部积分，得到实际 Fréchet 导数及二阶张量与对应字段卷积相等；二阶方向顺序通过实际 `iteratedFDeriv_two_apply` / CLM 作用身份核对。随后对 v 或 z 使用第 2 项，得到所写 L² 强收敛。没有假设原域零延拓具有全空间 H² 弱链。

**非阻断范围界限：** 第 25 项只把同一真实 Poisson 扩展接到全偶卷积的 C∞ 性和最终整个 frontier 零值。第 3–4 项是局部导数收敛工具，尚未在该最终结论中与扩展的 H² 正则性、原域全部二阶字段恢复组装。因此本报告不认证原盒 H² 图范数密度，也不认证原弱周期轨道 CE；这是固定声明与规格共同保留的后续工作，不构成本批辅助声明缺陷。

## 固定依赖、公理和实际构建

七模块递归 Carleman import 闭包共 207 个文件，其中 200 个旧文件与 mathematical_base 逐文件内容完全一致。另按相关已接受 declaration_version 比较关键入口的整个 Carleman 闭包，均无内容变化：

| 依赖 | declaration_version | 实际比较入口 / 闭包文件数 |
|---|---|---|
| C173 | `5eb3c89b2d38b27beedd3ce5e9192704def15e00` | `EvenMollifierLimit` / 135 |
| C157 | `b818f314b275265490aa9b797779f7db0005ddb9` | `FiniteBoxPoissonExtension` / 170 |
| C156 | `e1774a58f1c57c8a3305173b5195beea5ffd53b7` | `BoxOddPoisson` 与 `OddReflectionBounds` 联合 / 163 |
| C131 | `f134750df6b8ef03c639f50dd5084d4c42d49272` | `LocalStrongMollification` / 93 |
| C130 | `a5c68e2aaa4da98efe42da31ed0c1da04ba99952` | `LocalHessianConvolution` / 53 |
| C089 | `c99262c4a0d65a4d23f2efb57748bda490e971d7` | `InteriorWeakPoincare` / 67 |
| C036 | `cfd7d038d322779b1e9bc1cdd076af65e0e829d1` | `DomainConvolution` / 26 |

固定 Lean 为 `leanprover/lean4:v4.35.0`；CI 实际版本 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。固定 mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 mathlib checkout HEAD 同值且工作树干净。本批未增加外部依赖或新的数学公理。

实际读取 `/tmp/carleman-t158-odd-slab-smoothing-target2.log`：`Carleman.Spatial.OddSlabSmoothing` 定向 **3378 jobs** 成功；读取 `/tmp/carleman-t158-odd-box-boundary-build.log`：根目标 **4051 jobs** 成功。`-axioms.log` 实际为 0 bytes，不据此单独声称公理验证成功；证据来自固定完整 raw 中的逐项类型/axioms 及末行 `Axiom audit passed for all 7690 Carleman declarations.`。

固定 raw 包含 2931 个公理打印记录、2927 个不同显式名称；递归审计覆盖 **7690** 个 Carleman 声明，两个数量概念不混同。全部打印记录的依赖公理仅为正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理；未见 sorryAx 或新增非基础公理。二十五项新声明的完整类型和正常公理集合均在该固定 raw 中逐项核实。

## 独立远端 CI 与原始证据

独立通过 GitHub API 查询 [run 39245008692 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39245008692/attempts/1)：`head_sha=9cc8c5f57aec03ca11ce58ffe86fa6b0ae8f87a8`，run 为 `completed / success`，最后更新 `2026-10-19T11:32:52Z`。实际三个作业均为最终成功：

| 作业 | job ID | 实际结果 |
|---|---|---|
| state-check | `118034702514` | completed / success |
| lean | `118034702830` | completed / success |
| dashboard / snapshot | `118035965002` | completed / success |

验收者自行使用 `gh run download` 下载同 run 的两个原始产物，没有使用主执行者的下载副本代替：

| 产物 | artifact ID | 本机独立下载位置 |
|---|---|---|
| lean-ci-result | `12183116259` | `/tmp/carleman-t158-odd-box-boundary-main-ci/result.json` |
| lean-declaration-evidence | `12183560879` | `/tmp/carleman-t158-odd-box-boundary-main-axioms/axioms.txt` |

实际 result.json 为 `status=PASS`，`checked_sha=source_head_sha=9cc8c5f57aec03ca11ce58ffe86fa6b0ae8f87a8`，目标 `Carleman`，`finished_at=2026-10-19T11:31:40.540768+00:00`；Lean/mathlib 版本与固定 pin 一致。artifact 元数据的 workflow head SHA 也同值。

独立读取并逐字节比较远端 `axioms.txt` 与固定 `/tmp/carleman-t158-odd-box-boundary-local-axioms.txt`：**完全相同**，均 **2404009 bytes**，SHA256 均为 `2075233434715e3046f2ff8127f5b1ef60912ac516c4be6d56bf01efbbcdada2`。比较使用固定 local 副本，未使用后续阶段正在变化的 `.ci/axioms.txt`。

## 签发

**C174：PASS / AUXILIARY。** 未发现阻断本批二十五项真实声明的数学、量词、范数、对象身份或公理问题。精确弱 Poisson 扩展与实际局部奇性连接已证明，整个原盒边界的同一 eventual 平滑零值已证明；原 H² 图密度、弱时间轨道和完整 P024 仍不属于本次完成范围。报告仅签发上述固定 SHA；正文和 reviewed_at 随本报告提交冻结，不修改实现或全局台账，不推送。
