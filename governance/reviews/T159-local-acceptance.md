# T159 / C175 独立本机验收：盒域 H²∩H¹₀ 的光滑零边界逼近

- checked_sha / source_sha：`5923dbf398166a48ddf42f98585ff54a10545b0f`
- mathematical_base：`9cc8c5f57aec03ca11ce58ffe86fa6b0ae8f87a8`
- reviewed_at：`2026-10-19T11:46:23+00:00`
- reviewer：独立本机 Agent `/root/accept_spatial_lemma`，未参与本批实现。
- result：**PASS**；axiom_check：**PASS**；全部 **4/4** 显式声明通过。
- scope：**AUXILIARY — 完整盒域空间 H² 光滑零边界密度**。C175 可登记 REVIEWED；**P024 / prop:continuousCE 不提升，原文覆盖保持 17/26**。

本 Agent 从固定 Git 对象读取三模块全部实际源码、四项完整展开类型、原稿、T159 分析、MATH_SPEC、台账、治理协议及关键依赖，独立查询同 SHA 的三个真实 CI job，自行下载同 run 的原始 result/raw 并与固定本机副本逐字节比较。规格、既有报告、执行者说明和 CI 均未替代数学判断。动态 `.ci/axioms.txt` 及未来 BoxCompactSmoothDensity / SmoothLaplacianL2Limit / SmoothDirichletGraph / BoxSmoothGraphDensity / HarmonicGraphContinuity 工作树增量均排除。仅新增并单独提交本报告，不修改实现、根导入、审计、台账或原稿，不 push；签发后冻结正文及时间。

## 原文对应、输入及边界

固定 `paper/main.tex:2657–2664` 的 Dirichlet 实现以真实 H²∩H¹₀ 为算子域；`2672–2731` 的完整连续 CE 面向原弱周期轨道，并在 `2730` 使用密度步骤。本批清偿其中**坐标盒的空间 H² 逼近**：输入任意正边长盒 S 和任意原 `WeakSobolevJet d 2 (volume.restrict S) S`，只要求其 H¹ 截断属于原测试闭包 `dirichletJetSpace S`。输出同一全空间 C∞ 序列，每项在整个 frontier S 上严格为零，且值、全部一阶、全部二阶实际坐标导数分别在原域 L² 中强收敛到原 jet 字段。

输入没有连续代表、光滑性、额外零迹、切片、已给定扩张、H² 扩张正则性、导数收敛或目标逼近误差前提。`d : ℕ` 没有 d≤3 限制；所有正维数盒均包含，d=0 时导数指标为空、盒为全空间且 frontier 为空，值的 L² 逼近仍是实际结论。调用的是允许 d=0 且右端保留下阶项的 H² lifting，未错误调用只适于正维数的 Poincaré 型全范数估计。

该结论按实际有限维全部导数组分表述，足以给空间 H² 强密度；本批没有把它包装成已经完成的周期时空图范数密度。没有时间导数或周期逼近构造，没有弱 CE 极限传递，没有一般凸多面体密度，也未在本批输出全空间紧支性。**空间密度通过不等于原 prop:continuousCE 通过。** 原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未改写原命题。

## 四项声明逐项核对

下表路径前缀为 `Carleman/`，行号均指 checked_sha；名单和顺序与固定 C175 / T159 及 `/tmp/carleman-t159-box-h2-density-declarations.json` 完全一致。四项均是已证明定理，不含待填字段。

| # | 完整声明 | 固定源码位置 | 独立数学核查结论 |
|---|---|---|---|
| 1 | `Carleman.WeakSobolevJet.local_even_mollification_strong_h2` | `Spatial/WeakH2EvenLocalSmoothing.lean:15` | PASS。任意原弱 H² jet 在紧内集上，同一个实际全偶核卷积的值、全 fderiv 坐标和全部二阶 iteratedFDeriv 坐标强 L² 收敛；通过真实零延拓 a.e. 身份恢复原字段。 |
| 2 | `Carleman.local_L2_error_restrict_tendsto` | `Spatial/LocalSmoothingRestriction.lean:14` | PASS。T⊆K⊆S、K 紧、实际 Lp 原像及 a.e. 限制身份下，K 上实际 L² 误差极限限制到 T。连续近似项和 Lp 弱项在 K 上的 MemLp 均内部供应，范数单调合法。 |
| 3 | `Carleman.WeakSobolevJet.restrictSubdomain_component_ae` | `Spatial/LocalSmoothingRestriction.lean:30` | PASS。任意阶真实弱 jet 限制等式给任意阶任意 Sym 导数组分的限制测度 a.e. 身份，不把不同 Lp 类的代表当逐点相等。 |
| 4 | `Carleman.exists_box_dirichlet_smooth_h2_approximation` | `Spatial/BoxDirichletSmoothDensity.lean:16` | PASS。任意原 H² jet 的 H¹ 截断属于原 H¹₀ 闭包，即内部得到同一 C∞ 序列的严格全边界零值及原域值、全部一二阶强 L² 极限；不存在额外正则性或逼近假设。 |

## 同一个真实卷积与全部弱导数

第 1 项输入 `IsOpen S`、`IsCompact K`、`K⊆S` 和任意原弱 H² jet u。实际序列为 `U n = zeroExtendLp(value u) ⋆ (evenSpatialMollifier d n).value`，使用真实 Lebesgue 卷积及标量连续双线性乘法。U 先于所有一、二阶坐标量词给出，每项确实全空间 C∞；并非给每个坐标分别选择不相容的序列。

一阶微分调用原 jet 的 field₀→field₁ 弱身份；二阶再调用 field₁→field₂ 的完整弱链。核导数交换使用真实紧支反射测试，核支持最终位于 S 内。`IsWeakSpatialDerivative.zeroExtend` 只保留 S 上的局部弱身份，**没有宣称任意 H² 函数零延拓后全空间仍 H²**。全空间 Lp 零延拓仅用于卷积和真实 L² 收敛。

二阶输出为 `iteratedFDeriv ℝ 2 (U n) x ![basis i,basis j]`，对应原 `derivativeComponent (j ::ₛ i ::ₛ Sym.nil) (field 2 u)`；已沿 LocalHessianConvolution 核对实际 CLM 导数、两方向次序及 iteratedFDeriv 身份。遍历全部 i,j，包含全部混合项；没有以 Laplacian 收敛替代 Hessian 收敛。最终 `coordinateDerivative` 一、二阶公式是真实 Fréchet 导数公式，不受其所在模块其他 d≤3 连续代表定理的前提限制。

卷积局部强极限先针对真实零延拓 Lp 类成立，再由 `zeroExtend_ae_restrict` 和 K⊆S 的限制测度单调性换回原字段。这里仅使用 a.e. 身份；不在任意 Lp 类上添加节点值或边界点值。第 3 项同样通过 `derivativeComponent_subdomain` 与 `subdomainLp_ae` 逐字段恢复限制身份，适用于所有阶而非只值字段。

第 2 项的范数比较核对了可积性：每个连续 Fₙ 在紧 K 上属于 L²；w 本来属于 L²(S)，限制到 K 仍属于 L²。因此误差具有有限 eLpNorm，`bochnerL2Norm_mono_measure` 中 ENNReal.toReal 的单调性有合法有限性前提。随后用原真实 w=z a.e. 于 T 改写并夹逼到 0。不存在以不可积函数范数默认 toReal 值为 0 的漏洞。

## 原 H²∩H¹₀ 状态、扩大盒及边界恢复

设原盒为 S=(a,b)，扩大盒 T=(2a−b,3b−2a)。实际正边长假设内部给 S⊆T、closure S 紧且 closure S⊆T。取 `f := negativeLaplacian u`，它是原 field₂ 纯二阶分量和之负的实际 Lp 类。`negativeLaplacian_isWeak u` / `negativeLaplacian_test` 给 H¹ 截断对**全部原 SpatialTest S** 的弱 Poisson 恒等式，故 RHS 没有被当作额外输入，也没有假设原解已经满足另一条目标 PDE。

调用已验收的 `exists_box_poisson_extension_smooth_boundary` 得到同一扩大盒 H¹₀ 弱解 v 和 L² 右端 g，具有真实弱 Poisson 方程、原域限制 `restrictSubdomain v = truncate¹ u`，并且其同一全偶卷积最终在全部原 frontier 上严格为零。该奇扩张只要求相应局部奇条带；未用不可能同时成立的全局双面奇性或忽略角点。随后在扩大盒调用已验收 `exists_box_dirichlet_H2_bound`，得到实际 H² jet w，且 `truncate¹ w=v`、真实负 Laplacian 为 g。原状态的 H² 扩张由该正则性结论构造，不是输入前提。

`truncate¹ w=v` 给扩大盒上的实际 Lp 值类相等，而 v 的原域限制给原 u 的值类相等。源码调用开放原域上的 `WeakSobolevJet.value_injective`，通过完整弱导数唯一性证明 **`restrictSubdomain w=u` 作为整个 H² jet 的等式**。因此原域上的全梯度和全 Hessian 都由值身份与弱链恢复，没有额外假设它们与扩张逐字段吻合。

对 w 的同一实际全偶卷积应用第 1 项，紧内集取 **closure S**。扩大盒上的值 Lp 等式 value w=value v 将 C174 的严格边界零值结论转移给这个完全相同的序列；仅有原域 a.e. 等式不足以做这一步，而此处源码确实使用扩大盒整体的 Lp 等式。然后由第 2、3 项将 closure S 上所有实际 L² 极限限制回 S，识别为原 u 的值及一二阶字段。平滑导数的连续性由真实 coordinateTensorEval CLM / C∞ 导数供应，保证每次限制所需 MemLp。

边界条件是 `∀ᶠ n, ∀ x∈frontier S, F n x=0`，有限个正边长给同一个核半径阈值，已经统一所有面、边、角及边界点。取一个固定 N 后定义 `U n = F (n + N)`：每项严格零于整个 frontier，且 `tendsto_add_atTop_nat` 同时保持值和全部导数极限。统一尾序列在所有坐标前选择，没有非法交换不可数边界点量词。

## 量词、依赖和版本闭包

最终定理仅要求任意有限维正边长盒、原全弱 H² jet、其 H¹ 截断属于原 H¹₀ 闭包。输出一个 U 先于 n、所有边界点以及全部一二阶方向；同一 U 满足全部结论。没有新增统一逼近速率或常数估计，扩张、核阈值和尾序列可依赖盒与状态。没有把成员资格证明中选出的量误报为原 CE 的统一常数。有限维各导数组分的强收敛可合成空间 H² 强收敛，但尚未供应随时间可用的图空间稠密算子或周期光滑轨道。

独立递归读取新模块的实际 Carleman 导入闭包，共 **253** 个文件，其中 **250** 个既有文件与 mathematical_base 逐字节相同。进一步核对以下实际调用依赖及其完整导入闭包版本：

| 依赖 | 既有固定证明 SHA | 实际使用与闭包比对 |
|---|---|---|
| C174 / T158 | `9cc8c5f57aec03ca11ce58ffe86fa6b0ae8f87a8` | OddSlabSmoothing 起始闭包 207 个文件未改；真实局部奇 Poisson 扩张、全偶卷积、全部 frontier 统一尾阈值。已读 T158 独立报告并重新核对关键证明。 |
| C157 / T141 | `b818f314b275265490aa9b797779f7db0005ddb9` | BoxPoissonRegularity 起始闭包 222 个文件未改；实际扩大盒 H² lifting，truncate 精确等于原弱解；未将正则性作为未经清偿的假设。 |
| C173 / T157 | `5eb3c89b2d38b27beedd3ce5e9192704def15e00` | EvenMollifierLimit 起始闭包 135 个文件未改；真实全偶近似恒等与 L² 极限，支持条件通过局部微分链使用。 |

另直接核对 DomainConvolution、LocalHessianConvolution、WeakJetLocality、SobolevRealization、WeakLaplacian、DirichletDistribution、BoxPoissonExtension 与 coordinateDerivative 的一二阶实际展开。采用原完整 SpatialTest 测试族及原闭包，未换成较小光滑数据空间。既有验收作为依赖门槛，不替代本批对实际调用和假设清偿的检查。

## 编译、公理及同 SHA 原始 CI 证据

实际读取定向 `/tmp/carleman-t159-box-smooth-density-target4.log` 的 **3433 jobs** 成功和 `/tmp/carleman-t159-box-h2-density-build.log` 的 **4054 jobs** 成功。同前缀 `-axioms.log` 为 0 字节，**不把该空日志当作审计成功证据**；审计结论来自以下实际固定 raw 与独立下载 raw。

- 固定本机：`/tmp/carleman-t159-box-h2-density-local-axioms.txt`。
- 独立下载远端：`/tmp/carleman-t159-box-h2-density-main-axioms/axioms.txt`。
- 两文件逐字节相同，各 **2409730 bytes**，SHA256 均为 **`28ca7dedc08ad0e5e373b86965314816f78110157ea915249496f3bc2f57b8d3`**。
- 实际末行：`Axiom audit passed for all 7695 Carleman declarations.` 四项新声明均在完整类型打印及公理记录中；逐项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。全文 2926 条非空公理打印记录及 9 条无公理记录均未见其他公理；此打印记录数不是递归审计声明数。
- 三个新增源码没有 `sorry` / `admit` / 新增 `axiom`，实际 root 和 CheckAxioms 包含三模块及四项显式声明；不是只运行孤立测试或遗漏主入口。
- CI Lean 为 **4.35.0**，编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定 manifest 及本机实际依赖一致。

独立通过 GitHub API 查询 [run 39246261383 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39246261383/attempts/1)，确认 main、精确 head SHA 为 checked_sha，run `completed/success`，且三个 job 均最终成功：

| job | 实际 ID | 最终状态 | completed_at UTC |
|---|---|---|---|
| lean | `118038810086` | completed / success | `2026-10-19T11:43:08Z` |
| state-check | `118038810429` | completed / success | `2026-10-19T11:40:02Z` |
| dashboard / snapshot | `118040104265` | completed / success | `2026-10-19T11:43:22Z` |

同 run 的 `lean-ci-result` artifact ID **12183207633**（API 报压缩大小 493 bytes）及 `lean-declaration-evidence` ID **12183062857**（223845 bytes）均未过期；本 Agent 分别自行执行 `gh run download` 下载到上述唯一 main-ci / main-axioms 目录。没有使用执行者另存的 root 文件替代独立下载。

实际 `/tmp/carleman-t159-box-h2-density-main-ci/result.json` 为 **537 bytes**，SHA256 **`4cd0064cc76798fcb87ab3a02498dae0af22d89978a4ad67150081e3db87696c`**；status=`PASS`，checked_sha 与 source_head_sha **均精确等于 `5923dbf398166a48ddf42f98585ff54a10545b0f`**，targets=`["Carleman"]`，finished_at=`2026-10-19T11:42:04.652222+00:00`，ci_url 指向上述同 run/attempt。压缩 artifact 大小与解压 raw 大小分开记录，没有混淆。

## 最终判定

**4/4 PASS，C175 可在 AUXILIARY 范围登记 REVIEWED。未发现新增数学缺陷、隐含目标估计、遗漏混合导数或边界量词缺口。** 原任意盒域 H²∩H¹₀ 状态的空间光滑零边界密度已经清偿。周期时空图密度、原弱 CE 及一般凸多面体仍未完成；P024 不提升，原文覆盖保持 17/26。报告正文和 reviewed_at 签发后冻结；仅本报告单文件提交，不 push。
