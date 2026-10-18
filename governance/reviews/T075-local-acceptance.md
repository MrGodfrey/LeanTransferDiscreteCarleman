# T075 / C091 独立本机验收

- `checked_sha`: `a4d0f062b3a3d32e166af481ed93e38096a992c2`
- `base_commit`: `55dbf36858608cc7ff9300ef61430e18fa0bdadf`
- `reviewed_at`: `2026-10-18T23:07:05+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：全部Hilbert值弱区间H¹图的实际连续代表、CLM迹及FTC，标量双端点积分公式，真实乘积L²端点函数及在明确弱切片前提下的端点识别。原空间弱测试到切片、坐标拆分、物理面零迹和仿射核校正尚待；原文完整结果保持 **12/26**。

独立从固定提交导出快照，读取五新模块全部证明、25项实际展开类型及关键依赖，对照原 `paper/main.tex` Appendix B 的Lemma B.1（`lem:fd-boundary-affine`，TeX 2796–2836）及其使用迹定理消去仿射核的步骤。执行者规格与CI未代替数学判断；后续工作区增量不属本次审查。

## 全部25项声明

名称均以前缀 `Carleman.` 开始，下表省略该前缀。固定位置以 `Carleman/` 为根，顺序与交付JSON完全一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `HasWeakTimeDerivative.congr_value` | `Continuous/WeakIntervalRepresentative.lean:15` | PASS；值代表a.e.变更保留每个原紧支光滑测试的向量积分身份。 |
| 2 | `HasWeakTimeDerivative.exists_continuous_representative` | `Continuous/WeakIntervalRepresentative.lean:24` | PASS；真实du原函数加分布常数产生连续代表，不预设原u连续，且保留原du。 |
| 3 | `TimeGrid.continuous_representative_unique` | `Continuous/WeakIntervalRepresentative.lean:53` | PASS；正长度Lebesgue区间上的连续代表由a.e.类唯一确定，包含双端点。 |
| 4 | `TimeGrid.pathL2_injective` | `Continuous/WeakIntervalRepresentative.lean:60` | PASS；真实闭区间连续路径到L²的映射单射，由clamp限制身份和第3项推出。 |
| 5 | `TimeGrid.exists_tracePath` | `Continuous/WeakIntervalRepresentative.lean:70` | PASS；对完整弱图任意元素构造闭区间路径，pathL2精确还原原值L²类。 |
| 6 | `TimeGrid.weakTracePath` | `Continuous/WeakIntervalTrace.lean:13` | PASS；从已证存在性选择真实TracePath，不凭选择公理添加性质。 |
| 7 | `TimeGrid.weakTracePath_value` | `Continuous/WeakIntervalTrace.lean:16` | PASS；选择路径的实际pathL2等于输入第一分量。 |
| 8 | `TimeGrid.weakTracePath_ae` | `Continuous/WeakIntervalTrace.lean:19` | PASS；原L²代表与clamp后的路径a.e.相同。 |
| 9 | `TimeGrid.weakTracePath_weak` | `Continuous/WeakIntervalTrace.lean:24` | PASS；同一路径满足全部原弱测试，导数正是输入第二分量。 |
| 10 | `TimeGrid.weakTracePath_point_bound` | `Continuous/WeakIntervalTrace.lean:28` | PASS；所有闭区间点有L^(−1/2)‖u‖+L^(1/2)‖du‖界，实际toLp值与导数已识别。 |
| 11 | `TimeGrid.weakTracePath_norm_bound` | `Continuous/WeakIntervalTrace.lean:41` | PASS；取连续路径sup范数，以产品max图范数得到L^(−1/2)+L^(1/2)常数。 |
| 12 | `TimeGrid.weakTracePathCLM` | `Continuous/WeakIntervalTrace.lean:52` | PASS；加法、数乘由pathL2线性与单射证明，连续性来自第11项。 |
| 13 | `TimeGrid.weakTracePathCLM_value` | `Continuous/WeakIntervalTrace.lean:65` | PASS；打包为CLM后仍精确还原原L²值。 |
| 14 | `TimeGrid.weakTracePathCLM_eq_of_representative` | `Continuous/WeakIntervalTrace.lean:68` | PASS；任意同值L²类的真实连续路径都等于所选路径，端点不依赖选择。 |
| 15 | `TimeGrid.weakIntervalTrace` | `Continuous/WeakIntervalTrace.lean:72` | PASS；实际连续路径在指定闭区间点的有界线性求值。 |
| 16 | `TimeGrid.weakIntervalTrace_bound` | `Continuous/WeakIntervalTrace.lean:75` | PASS；迹算子继承精确分量界，不添加未知迹常数。 |
| 17 | `TimeGrid.weakIntervalTrace_fundamental` | `Continuous/WeakIntervalTrace.lean:80` | PASS；任意a、b的实际迹差等于原第二分量的有向Bochner区间积分。 |
| 18 | `TimeGrid.weakIntervalTrace_affine_green` | `Continuous/ScalarIntervalTrace.lean:13` | PASS；对全部标量弱图由真实绝对连续性和a.e.强导数作积分分部，双端点系数与符号正确。 |
| 19 | `TimeGrid.weakIntervalTrace_zero_formula` | `Continuous/ScalarIntervalTrace.lean:42` | PASS；取c=L得到左端点L⁻¹∫[u+(t−L)du]，除法有L>0保障。 |
| 20 | `TimeGrid.weakIntervalTrace_end_formula` | `Continuous/ScalarIntervalTrace.lean:49` | PASS；取c=0得到右端点L⁻¹∫[u+t du]。 |
| 21 | `fiberEndpointIntegral` | `Spatial/FiberEndpointIntegral.lean:15` | PASS；定义真实切片积分E_c=L⁻¹∫[f+(t−c)v]，未把任意点值作为迹。 |
| 22 | `fiberEndpointIntegral_congr` | `Spatial/FiberEndpointIntegral.lean:19` | PASS；乘积a.e.相等经a.e.切片相等推出端点函数a.e.不变。 |
| 23 | `fiberEndpointIntegral_memLp_bound` | `Spatial/FiberEndpointIntegral.lean:28` | PASS；明确0≤c≤L及乘积L²前提，证明实际L²成员和(2/L)‖f‖²+2L‖v‖²界。 |
| 24 | `fiberEndpointIntegral_eq_weak_trace` | `Spatial/WeakSliceEndpointTrace.lean:14` | PASS；给定真实弱图及两个分量的a.e.切片身份，精确识别E_L为左迹、E_0为右迹。 |
| 25 | `weak_slices_actual_endpoint_traces` | `Spatial/WeakSliceEndpointTrace.lean:34` | PASS；Fubini供应a.e.切片L²资格，明确保留a.e.完整弱切片前提，同一个连续代表满足两端点等式及原弱身份。 |

## 全部Hilbert弱图与真实连续代表

原 `HasWeakTimeDerivative` 对每个全实线C∞、紧支且tsupport严格包含于(0,L)的标量测试φ要求向量身份∫φ′u=−∫φdu。`IsWeakTimeClass`以全部该类测试和全部H方向的真实L²配对定义；其双向等价通过合法Bochner积分与所有内积方向分离向量，未把测试集缩到有限维或有限谐波。`weakTimeSubmodule`是这条真实分布关系在L²(H)×L²(H)中的完整图，没有连续性、端点相等或方程解条件。

已直接复核原函数依赖：du∈L²且区间有限给实际Bochner可积性，F(t)=∫₀ᵗdu在[0,L]连续，且满足相同完整弱导数身份。Hilbert值原函数的弱身份由每个连续内积泛函与Bochner积分交换，从真实标量原函数积分分部推出；没有用标量替身替换H值状态，也没有要求H有限维或给H增加可分性假设。

第2项对u−F逐测试相减。代码先证明φ′u和φ′F的实际可积性，再使用积分差，从而得到弱导数为零。所调用分布常数引理利用真实归一化紧支测试ψ和每个零均值测试的紧支原函数，证明u−F等于常向量c a.e.；最后以向量分布唯一性得出结论，并非对不可数H方向分别取a.e.集合后非法相交。U=c+F因此连续、等于原u a.e.且具有原du的弱身份。

TimeGrid只在这里提供L=period>0和Lebesgue|(0,L)。图和路径均无periodic_trace字段；任意正长度可由steps=1、dt=L表示，未限制空间切片必须周期或长度来自某一固定网格。证明不使用next、prev、节点数或时间方向。原始函数在端点的任意代表值不参与迹定义。

## 双端点唯一性、pathL2与CLM

timeMeasure与Lebesgue|[0,L]因端点零测而相同；L>0使闭区间为其内部的闭包。已核对所用mathlib `Measure.eqOn_Icc_of_ae_eq`：在每个非空开集有正测度的Lebesgue测度下，两个闭区间连续函数a.e.相等即处处相等，包括0和L。这并非声称任意L²代表可逐点相等。

TracePath实际是C([0,L],H)，clampPath由真实投影projIcc作全实线连续延拓，pathL2是该有界连续函数的真实L²类。新单射性先转为clamp路径a.e.相等，再限制回[0,L]。第5项将新构造U限制到闭区间，逐a.e.核对pathL2精确等于原u。选择weakTracePath后，全部a.e.身份和弱导数都从该精确等式恢复。

选择函数本身的线性没有被默认：证明将所选(u+v)路径与两所选路径之和送入pathL2，使用原pathL2的线性、还原身份和单射性推出相等；数乘同理。因此mkContinuous的LinearMap字段是真实证明。任意同L²值的连续代表由同一单射性等于所选路径，迹与非计算选择无关。

逐点界来自FTC给出的‖U(t)−U(a)‖≤∫‖du‖，再对a在整个长度L的区间积分并用真实L² Cauchy–Schwarz：

\[
\|U(t)\|\le L^{-1/2}\|u\|_{L^2}+L^{1/2}\|du\|_{L^2},\qquad 0\le t\le L.
\]

本图继承产品的max范数max(‖u‖,‖du‖)，不能误写成平方和Hilbert范数。取sup后算子上界为L^(−1/2)+L^(1/2)，代码以norm_fst_le、norm_snd_le分别控制两项。它是显式区间长度依赖，未声称L或T一致。FTC对所有a、b∈[0,L]成立，a>b由有向区间积分的符号处理，a=b和双端点同样包含。

## 标量绝对连续性和双端点公式

第18项作用于全部标量弱图。所选真实路径U由原FTC得到绝对连续性；依赖证明以∫‖du‖的绝对连续原函数控制U的点间距离，并由Bochner积分微分定理得到U′=du a.e.，没有反过来把经典导数资格设为输入。

对α(t)=t−c和U使用实际绝对连续函数积分分部。α′=1，U′=原第二L²分量a.e.，U=原第一L²分量a.e.，故

\[
\int_0^L\bigl[u(t)+(t-c)du(t)\bigr]\,dt=(L-c)U(L)+cU(0).
\]

右端加号来自−α(0)U(0)=cU(0)，并未交换左右端。c在此可为任意实数；取c=L、c=0分别得到左迹和右迹。所有除法均以L>0消去，不用零分母约定。绝对连续性保障积分分部中的真实导数可积，有限区间上的有界系数与原L²分量也给原表达式可积；没有利用不可积Bochner积分默认值。

## 真实乘积端点函数、平方常数和代表不变性

E_c的输入是任意实际函数f、v，但成员与估计定理明确要求两者在μ×Lebesgue|(0,L)中属于L²，且0≤c≤L。μ只需SFinite，不要求有限总质量。系数t−c在该乘积测度上a.e.满足绝对值≤L，由实际可测系数及支配界证明w=(t−c)v∈L²；随后f+w、其平方和比较上界都具有真实可积性。

已直接复核 `l2_average_square_le`：a.e.切片由Fubini取得L²资格，有限区间Cauchy–Schwarz给(∫h)²≤L∫h²；切片积分的a.e.强可测性、平方可积性和全乘积积分交换均在证明中供应。故端点L⁻¹缩放后，独立重算为

\[
\|E_c(f,v)\|_{L^2(\mu)}^2
\le L^{-1}\int |f+(t-c)v|^2
\le (2/L)\|f\|_{L^2(\mu\times\nu)}^2+2L\|v\|_{L^2(\mu\times\nu)}^2.
\]

两个2来自平方三角界，L²系数界经平均与L⁻²缩放恰留下2L；不存在漏乘体积、μ总质量或节点数。该定理也实际返回MemLp，而非只给可能退化的扩展实数范数不等式。

乘积代表不变性使用 `Measure.ae_ae_of_ae_prod` 的正确单向：乘积a.e.身份推出a.e.外变量上的内变量a.e.身份，再用实际积分的a.e.不变性。因此E_c确定一个真实L²类；没有将其解释为任意代表在零测端面的逐点限制。此不变性定理不需要额外SFinite μ，实际展开类型与依赖定理允许该一般性。

## 弱切片前提与原Lemma B.1的边界

第24项针对给定x和一个真正的弱图z，要求z的值及导数分别与f(x,·)、v(x,·)在区间内a.e.相同；用标量双端点公式即可识别E_L、E_0，不需要取原f在0或L的点值。

第25项从乘积L²条件先取得a.e.切片的强可测性与平方可积性，再利用明确的 `∀ᵐ x, HasWeakTimeDerivative g (f(x,·)) (v(x,·))` 构造该切片的真实弱图。两次toLp代表变更分别按值和导数的a.e.身份传输。最终所选同一个连续U同时满足原值a.e.身份、以原v为导数的全部弱测试，以及两个实际端点等式；不分别选择无法同时兼容的代表。结论仅为a.e. x存在这样的路径，没有额外宣称一族联合连续或联合可测路径；端点函数的L²资格已由独立积分公式保证。

原Lemma B.1需要长方体H²函数在真实物理面的零迹，再用这些面迹控制仿射核并回缩得到统一逼近。当前25项没有把原多维SpatialTest身份自动转换成切片弱身份，也未完成坐标拆分、长方体限制测度的识别、面迹与零边界条件的连接或有限维仿射核校正。它们提供所需的一维及乘积迹基础，不单独证明原Lemma B.1、B.2或P1命题；该剩余范围在真实类型中明确，非隐藏假设。

## 固定依赖、构建与公理

五模块的Carleman导入闭包共62模块，其中57旧模块与base完全不变，新增恰为本批五模块。另核对关键依赖的闭包与旧验收版本：C025 WeakTimeSpace/TimeInterval共21模块对 `58660cbe195e6af699e0b2edeec93153b1cd3f6d`，C026 TimeTraceBound/WeakTimeEnergy共28模块对 `ec0848a447fb0a8a03e544ce453da43c90299ba0`，C036 L2Averaging共46模块对 `cfd7d038d322779b1e9bc1cdd076af65e0e829d1`，均无变化。上述关键旧证明及所用mathlib端点唯一性、a.e.切片、分布唯一性和绝对连续积分分部定理已直接读取。

原稿、已读治理协议、工具链pin及CI工作流未由本批改变。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入五模块，CheckAxioms包含全部25项的完整类型及公理输出。

25项实际展开类型逐一核查，仅依赖 `propext`、`Classical.choice`、`Quot.sound`。固定本机1568条显式公理记录也无其他公理，无sorryAx。检查器通过privateToUserName遍历所有Carleman声明并递归collectAxioms。固定 `/tmp/carleman-weak-trace-full.log` 实际包含 `Build completed successfully (3695 jobs).` 和 `Axiom audit passed for all 5341 Carleman declarations.`。

已独立通过GitHub connector读取 [main CI 39174830242 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39174830242/attempts/1)：main/push，head SHA精确匹配固定版本，run为completed/success。state-check（117815244769）、lean（117815244929）、dashboard / snapshot（117815833906）三项jobs全部completed/success；实际工具链准备、构建、checked source记录、两份证据上传及同次快照步骤均success。同run的lean-ci-result artifact（12153917294）和lean-declaration-evidence artifact（12154301048）均绑定固定SHA。

已实际读取 `/tmp/carleman-weak-trace-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=a4d0f062b3a3d32e166af481ed93e38096a992c2`，targets为Carleman，`finished_at=2026-10-18T23:04:38.260153+00:00`，ci_url与上述run/attempt一致。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-weak-trace-main-axioms/axioms.txt` 与固定 `/tmp/carleman-weak-trace-local-axioms.txt` 已独立逐字节比较，完全相同：**1,569,327 bytes**，SHA256 **`0bc0f8872e36716157957420f5d82eaf77d2fb0388c5601485490cbb1aa43c13`**。另逐名核对远端25/25完整展开类型及其基础公理，1568条显式记录无其他公理；实际末行为 **`Axiom audit passed for all 5341 Carleman declarations.`**。未混用其他SHA或后续工作区产物。

## 验收决定

**C091：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定25项未发现弱测试范围、原类还原、端点唯一性、选择路径线性、图范数、FTC方向、双端点系数、可积性、乘积代表或常数方面需要修复的缺陷。完整同SHA正式CI与原始公理证据均已独立核实。

原空间弱测试到切片、坐标拆分及物理面零迹／仿射核校正仍待，原文计数保持12/26。本次只写本报告，没有修改数学实现、台账、原稿或root导入，没有commit/push。
