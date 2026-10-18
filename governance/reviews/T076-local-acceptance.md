# T076 / C092 独立本机验收

- `checked_sha`: `101b95e1b988d17332c7106c2be2aa945b213b3a`
- `base_commit`: `a4d0f062b3a3d32e166af481ed93e38096a992c2`
- `reviewed_at`: `2026-10-18T23:16:22+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原乘积域完整弱导数推出全部测试共同满测集上的真实弱切片；构造实际双端点 L² 面迹并保留 `2/L`、`2L` 缩放。原长方体坐标拆分、物理面零迹连接及仿射核校正仍待，原文完整结果保持 **12/26**。

直接以 `git show` 读取固定版本的五个新模块、全部16项展开类型及关键依赖，核对原 `paper/main.tex` Appendix B 的 Lemma B.1（`lem:fd-boundary-affine`，TeX 2796–2836）、治理协议和本阶段规格。没有以执行者说明、已有验收报告或构建成功代替数学核对；后续工作树增量不属本次范围。

## 全部16项声明

下列名称省略共同前缀 `Carleman.`；固定位置以 `Carleman/` 为根，顺序与交付清单及 C092/T076 的声明清单一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `ae_forall_continuous_zero_on` | `Spatial/CountableWeakTests.lean:12` | PASS；在实际可分子集内取可数稠密子集，取可数 a.e. 交后利用每个函数零集闭性扩展到全子集。 |
| 2 | `scalar_weak_interval_iff` | `Spatial/CountableWeakTests.lean:23` | PASS；标量 L² 空间弱导数与原全紧支光滑测试的时间弱身份双向等价，方向为正1。 |
| 3 | `ae_weak_interval_of_ae_tests` | `Spatial/CountableWeakTests.lean:32` | PASS；测试对是实际 `(derivativeLp ψ 1, toLp ψ)`，以 L² 内积和的连续性应用第1项，未非法交换不可数全称与 a.e.。 |
| 4 | `SpatialTest.tensor_tsupport_subset` | `Spatial/TensorSpatialTest.lean:16` | PASS；真实乘积函数的闭支撑包含于两个闭支撑的乘积，先对普通支撑判断两个因子非零再取闭包。 |
| 5 | `SpatialTest.tensor` | `Spatial/TensorSpatialTest.lean:23` | PASS；实际值为 φ(x)ψ(t)，全局光滑、紧支撑及支撑位于原乘积域三字段均内部证明。 |
| 6 | `SpatialTest.tensor_interval_derivative` | `Spatial/TensorSpatialTest.lean:29` | PASS；真实 Fréchet 乘积法则及坐标投影导数给 D_(0,1)(φψ)=φψ′，横向项确为 Dφ(0)=0。 |
| 7 | `product_weak_marginal` | `Spatial/ProductWeakMarginal.lean:17` | PASS；原全部乘积测试身份经实际张量测试、可积 Fubini 与横向基本引理给每个固定 ψ 的 a.e. 弱切片身份。 |
| 8 | `intervalSliceLp` | `Spatial/ProductWeakSlices.lean:13` | PASS；有真实 MemLp 资格时取对应切片类，否则为零；定义未伪设所有切片可积。 |
| 9 | `intervalSliceLp_ae` | `Spatial/ProductWeakSlices.lean:17` | PASS；乘积 L² 的实际 a.e. 强可测切片和平方可积性给 MemLp，故零分支只在零测例外使用。 |
| 10 | `scalar_interval_test_pairing` | `Spatial/ProductWeakSlices.lean:25` | PASS；两个实际 L² 内积分别等于 ψ′u、ψu 的真实积分，通过测试类的 a.e. 代表身份识别。 |
| 11 | `product_weak_slices` | `Spatial/ProductWeakSlices.lean:42` | PASS；第7项转为切片类配对后调用可数化，最后同时还原原 f、v 代表，输出原全测试弱身份。 |
| 12 | `product_weak_endpoint_representatives` | `Spatial/ProductWeakSlices.lean:71` | PASS；已清偿旧 T075 的弱切片前提；同一个连续 U 还原值、保持原导数并满足双端点积分公式。 |
| 13 | `fiberEndpointLp` | `Spatial/ProductFaceTrace.lean:12` | PASS；先用真实端点积分的 MemLp 定理，再构造横向 L² 类；不是任意 L² 代表的边界求值。 |
| 14 | `fiberEndpointLp_ae` | `Spatial/ProductFaceTrace.lean:17` | PASS；所构造真实 L² 类与原端点积分函数 a.e. 相同。 |
| 15 | `fiberEndpointLp_norm_sq` | `Spatial/ProductFaceTrace.lean:21` | PASS；将已有真实 Bochner L² 范数精确识别为三个 Lp 范数，得到 `(2/L)‖f‖²+2L‖v‖²`。 |
| 16 | `product_weak_face_trace_representatives` | `Spatial/ProductFaceTrace.lean:36` | PASS；有限个 a.e. 集合相交，同一连续切片 U 的 U(0)、U(L) 分别等于两面 L² 类的代表。 |

## 原数据、全测试族与真实张量导数

最终入口的实际展开类型对任意自然数 d、开集 S⊆SpatialCoordinates d、有限测度 `volume.restrict S`、任意 TimeGrid g 及任意原乘积 L² 类 f、v 量化。唯一弱正则条件是在 S×(0,L) 上沿 (0,1) 的 `IsWeakSpatialDerivative`，其中 L=g.period>0。该定义要求每一个全局 C∞、紧闭支撑包含于原开域的 SpatialTest 的真实 L² 配对身份，并非只假设有限测试、张量测试或光滑原函数。输入不要求连续代表、预先成立的弱切片身份、边界值、H² 正则性或周期端点。

TimeGrid 在本链中仅提供正长度和 ν=Lebesgue|(0,L)；它没有向切片附加周期条件。任意 L>0 均可用一步网格表示。横向有限体积是本定理明确的适用范围，而不是最终估计或正则性假设；原长方体横截面具有该性质。S 可以为空或零测，不要求正体积，也不排除 d=0。常数和证明未除以横向体积。

张量测试 Φ(x,t)=φ(x)ψ(t) 的支撑证明先在乘积值非零时推出两因子非零，再用两个闭支撑乘积为闭集取闭包。紧性来自两个紧闭支撑的乘积，最后分别应用 φ、ψ 的原支撑条件。因此 Φ 是原完整测试族内的实际元素。导数证明使用 `hasFDerivAt_fst`、`hasFDerivAt_snd` 的复合和真正乘积法则；代入 (0,1) 后横向项为零，轴向项为 φ(x)·fderiv ψ(t)(1)=φ(x)ψ′(t)。没有独立定义“轴向导数”来冒充真实导数，也没有负号或坐标系数遗漏。

## 固定测试的 Fubini 与横向基本引理

对固定 ψ，代码先证明 ψ′(t)f(x,t)、ψ(t)v(x,t) 在 μ×ν 上属于 L¹，其中 μ=volume|S。ψ、ψ′ 是真实紧支光滑测试的 L² 函数，`MemLp.comp_snd` 的实际类型明确需要横向 μ 有限；与原 f、v 的 L² 相乘后通过 L²×L²→L¹ 获得 Integrable。横向边缘函数

`M(x)=∫[ψ′(t)f(x,t)+ψ(t)v(x,t)] dν(t)`

因而真正可积。对任意横向紧支光滑 φ，两项 φ(x)ψ′(t)f(x,t) 和 φ(x)ψ(t)v(x,t) 的可积性另外由实际 Φ 的导数及 Φ 自身的 L² 资格证明；没有要求 φ 有全局统一上界，也没有未经证明直接将可积函数乘以任意函数。

在这些可积性已成立后，积分和、Fubini 与提取 φ 才将原弱身份变为 ∫φM=0。实际调用 mathlib `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`，其参数是全部原紧支光滑横向测试，要求真实 LocallyIntegrableOn，输出 a.e. x∈S⇒M(x)=0。这里从 M 的 Integrable 获得局部可积性，再与 `ae_restrict_mem` 相交得到原限制测度下 M=0。最后再次使用两项实际 a.e. 切片可积性拆分积分，得到 ∫ψ′f=−∫ψv。未利用非可积 Bochner 积分的默认零值，也没有遗漏横向全测试族。

## 对全部测试统一零测例外

一般可数化引理的前提是子集 B 本身可分，取到 D 可数、D⊆B、B⊆closure D。对 D 使用 `ae_ball_iff` 取得一个共同满测集。在该集中的每个 x，函数 z↦F(x,z) 连续，其零集为闭集，包含 D 因而包含 B。证明不要求将不可数个满测集相交，也不需要 x↦F(x,z) 额外可测：已给逐 z 的 a.e. 条件，加上可数滤子运算即可。

实际应用中 B 是全部测试对 `(ψ′,ψ)` 在 `Lp ℝ 2 ν × Lp ℝ 2 ν` 中的像，两个分量均为已证明的真实 L² 类。已读取固定 mathlib 的实例链：实线 Borel 可数生成、ν 有限从而 SFinite，使 ν 为可分测度；实数可分且 1≤2<∞，给 L² 的第二可数性，其有限乘积及子空间继续第二可数，故 B 可分。这是内部实例供应，不是最终定理中新添的可分性假设。B 不需要闭或非空，也没有假定全部光滑测试本身可数。

对每个 x，连续函数是 `〈u_x,p₁〉+〈v_x,p₂〉`；实际 L² 内积对第二分量连续，乘积投影和求和保持连续。稠密性只用于真实测试对的闭包，因此 ψ′与ψ的关联不会丢失。恢复任意 ψ 后，由第2项的双向等价得到原 `HasWeakTimeDerivative`，其范围仍为全部 C∞ 紧支测试。标量空间 Fréchet 导数在方向1与 deriv 的识别为真实定义上的一致，积分分部负号保留。

## 原切片 L² 类及同一连续代表

`intervalSliceLp` 没有对原 Lp 类任意求点迹。它先在每个横向 x 检查 t↦f(x,t) 的真实 MemLp，成立才取该函数的 toLp。乘积 L² 的 a.e. 强可测切片和实际平方积分 Fubini 共同证明该资格在满测集成立，并由 `coeFn_toLp` 还原切片代表。对 v 同样处理。无资格时设零仅提供全域定义，不被用于证明正测度上的虚假弱身份。

先对每个 ψ 将原固定测试积分身份转换为这些实际切片类的内积身份，再调用上述可数化得到同一个满测集上全部 ψ 成立。最后与 f、v 的代表还原集合相交，分别通过 `congr_value` 和 `congr_derivative` 将完整弱身份传回原 f(x,·)、v(x,·)。输出不是未经识别的替代函数或较小状态空间。

已直接复核所调用 T075 依赖：乘积 L² 资格与新得到的弱切片身份构造真实一维弱图；真实弱 H¹ 连续代表存在性由原函数加分布常数证明，不假设原 f 连续；连续代表在 [0,L] 由 a.e. 类唯一确定。第12项结论只显式量化存在 U，但既有唯一性可直接适用，且同一 U 同时还原原 f、保持原 v 为弱导数并实现双端点公式。没有额外宣称整族 U 对 x 联合连续或联合可测；所需面函数的可测性及 L² 资格由独立的积分公式保证。

## 真实两面 L² 类、端点次序与尺度

实际端点函数为

`E_c(f,v)(x)=L⁻¹∫[f(x,t)+(t−c)v(x,t)] dν(t)`。

对 c∈[0,L]，依赖证明先从 |t−c|≤L a.e. 得到系数乘积属于 L²；切片积分的真实 L² Cauchy–Schwarz 给平均平方界，再使用 `(a+b)²≤2a²+2b²`。独立重算其尺度为

`‖E_c(f,v)‖² ≤ L⁻¹∫|f+(t−c)v|² ≤ (2/L)‖f‖²+2L‖v‖²`。

两个2来自平方三角估计；平均因子 L、外部 L⁻² 及导数系数 L² 相乘后分别留下 L⁻¹、L，没有漏掉区间长度或额外横向体积因子。新 `fiberEndpointLp_norm_sq` 将这个实际 Bochner 范数界逐项识别为 Lp 范数，而非替换范数定义。该组构造及界在一般 SFinite 横向测度上成立；只在从完整空间弱身份推出切片的入口需要横向开集与有限体积。

对于真正弱切片，标量积分分部给 `∫[f+(t−c)v]=(L−c)U(L)+cU(0)`。所以 c=L 对应左端点 U(0)，c=0 对应右端点 U(L)，不是把 c 当作求值位置。第16项仅将第12项和两个 `fiberEndpointLp_ae` 的满测集作有限交，故在同一横向满测集上同一个 U 满足两个面类等式。原 L² 代表在端面上的任意值完全不参与定义；既有 `fiberEndpointIntegral_congr` 也确保乘积 a.e. 代表变更不改变端点函数的横向 a.e. 类。

## 与原 Lemma B.1 的对应和剩余范围

原 B.1 对长方体 B_K 中全部 H² 状态、原物理面集合的零迹，要求在所有这些面上消失的仿射 p_K，并给 h² Hessian 误差和网格比较统一常数。其证明中用实际面 L² 迹控制仿射核补空间，再对有限面集合统一并缩放。本阶段已清偿旧 T075 明确保留的“原乘积域完整弱导数到 a.e. 全弱切片”义务，并给出该迹论步骤所需的真实乘积域单轴面迹与显式长度缩放。

当前实际类型仍没有把 SpatialCoordinates(d+1) 长方体通过坐标拆分及体积测度识别到这里的乘积空间，没有连接任意物理面零迹条件，也没有完成多面仿射核校正与网格统一估计。它不单独证明 B.1、B.2 或 P1 命题；不能把这16项或 T074 的无边界仿射逼近合计为完整 B.1。保持 AUXILIARY 和原文12/26正确。

## 固定依赖、本机构建与公理

五模块的 Carleman 导入闭包共67模块，其中62个旧模块与基线逐字相同，新增恰为本批五模块。直接依赖 C091 的全部25项已在 [T075独立验收](T075-local-acceptance.md) 对同一基线 PASS；本次另直接读取关键弱区间代表、完整弱图、端点积分、弱切片端点、SpatialTest/弱导数定义及实际 mathlib 可分性、基本引理和 Fubini 依赖，核对它们在新证明中满足适用条件。既有依赖验收不扩展本阶段的原文范围。

原稿、Lean/mathlib pin 和 CI 工作流未由本批改变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；Lean 为4.35.0，本机 mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root 显式导入全部五模块；CheckAxioms 增量仅增加本批16项的完整类型及公理输出，原递归检查器未削弱。

已逐名核对固定产物的16/16完整展开类型与公理记录，每项只依赖 `propext`、`Classical.choice`、`Quot.sound`。产物全部1584条显式公理记录均无其他公理；检查器对所有 Carleman 声明递归 collectAxioms，包括定义生成的辅助声明，无 sorryAx 或无依据数学公理。五个新源文件也无 sorry/admit/axiom/unsafe。

固定 `/tmp/carleman-weak-slices-full.log` 实际含 `Build completed successfully (3700 jobs).` 和 `Axiom audit passed for all 5367 Carleman declarations.`。固定 `/tmp/carleman-weak-slices-local-axioms.txt` 为 **1,578,083 bytes**，SHA256 **`84784dea3328224363fcfc6d88d35e337ae740d23e0afdb537f80391312c523f`**。

## 同 SHA 远端证据

已独立通过 GitHub connector 读取 [main CI 39175437967 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39175437967/attempts/1)：main/push，head SHA 精确匹配固定版本，run 为 completed/success。state-check（117817014533）、lean（117817014705）、dashboard / snapshot（117817781103）三项 jobs 均 completed/success；工具链准备、实际构建、checked source 记录、两份证据上传及同次快照步骤均 success。同 run 的 lean-ci-result artifact（12154371904）和 lean-declaration-evidence artifact（12154022956）均绑定固定 SHA 且未过期。

已实际读取 `/tmp/carleman-weak-slices-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=101b95e1b988d17332c7106c2be2aa945b213b3a`，targets 为 Carleman，`finished_at=2026-10-18T23:13:43.911967+00:00`，ci_url 与上述 run/attempt 一致。实际 Lean 4.35.0 提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 为上述固定 pin。

原始远端 `/tmp/carleman-weak-slices-main-axioms/axioms.txt` 与固定本机文件已经独立逐字节比较，完全相同：**1,578,083 bytes**，SHA256 **`84784dea3328224363fcfc6d88d35e337ae740d23e0afdb537f80391312c523f`**。另逐名核对远端16/16项完整类型和公理记录，1584条显式公理记录均只有三项标准基础公理；末行为 **`Axiom audit passed for all 5367 Carleman declarations.`**。未混用其他提交、其他 run 或后续工作区产物。

## 验收决定

**C092：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 固定16项未发现测试族、量词、零测集统一、真实代表、导数符号、可积性、端点或尺度方面需要修复的缺陷。完整同 SHA 正式 CI 与原始公理证据均已独立核实。

长方体坐标拆分、物理面零迹连接与仿射核校正仍待，原文计数保持12/26。本次只写本报告，没有修改数学实现、台账、原稿或 root 导入，没有 commit/push。
