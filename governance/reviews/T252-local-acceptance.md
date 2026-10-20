# T252 / C268 独立本机验收

- checked_sha: `51c2b03bbc06cc44d7d55e9bb12a91bbb7971285`
- mathematical_base: `80b4f9a934f15a60281b7d5abf3f9a04c486eb41`
- reviewed_at: `2026-10-20T09:56:02+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，14/14 声明（11 定理、3 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；实际图剪切在完整 H² 弱 jet 图范数下的连续线性拉回、同一值/AE/H¹ 截断、H¹₀ 保持、强收敛和真实测试身份。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/StrongH2GraphTransport.lean`、14 项 raw 类型/公理、analysis/MATH_SPEC/台账，并对照原稿 `paper/main.tex:2659–2665`。本批提供原边界强逼近所需的固定图坐标连续性，不构造该逼近，不声称原凸多面体全部正则性或随域统一的估计。

## 实际数学与量词

1. **泛型提升的存在前提明确。** P 是两端真实限制体积上的标量 L² 连续线性映射；hl 要求每个原 m 阶弱 jet u 都有一个目标 n 阶弱 jet v，且其真实 value=P(value u)。该 helper 没有把目标成员资格凭空从 L² 连续性推出。目标 T 开放及限制测度集中于 T，使原分布弱导数唯一性对全部阶成立；故所选 v 唯一。两个原 jet 的和、数乘仍为合法 jet，P/value 的真实线性使候选目标的 value 相同，再由唯一性给提升的加法、数乘法则。选择函数因而确实成为线性映射，不是只给候选值的非线性选择。
2. **闭图位于完整 Sobolev 空间。** 实际 graph 严格等于
   `{(u,v) | value(v)=P(value(u))}`，
   正向用定义的 value 身份，反向用已合法目标 jet 的值唯一性。此集合在 `WeakSobolevJet(d,m,S) × WeakSobolevJet(d,n,T)` 的原乘积拓扑中，由两个连续 L² 值映射的等式闭性给出；没有将这两个 jet 空间重新赋予值 L² 诱导拓扑。
3. **Banach 资格来自全部弱字段。** 已直接读取 `SobolevJet`、`SobolevTopology`：载体是 k=0,…,m 的真实 L² 导数字段有限乘积，其中每阶是全部 Sym 多指标欧氏纤维；规范为有限乘积范数。每个原分布测试身份是连续 L² 配对的等式，所有 k/α/i/φ 的交集为闭子空间，所以两端均完备。`valueCLM` 只是该完整乘积的零阶连续投影。mathlib `ContinuousLinearMap.ofIsClosedGraph` 实际调用两个 Banach 空间间的闭图定理，保留同一线性函数；没有使用有限维自动连续性、value 嵌入有界逆、标量 L² 值域闭性、P 单射或 P 满射。泛型 S 无需开放，因为需要唯一性的是目标 T。
4. **值与唯一性保留整个提升。** `valueLiftLinear_value`、`valueLiftCLM_value` 都是所选真实 jet 的精确 L² 身份；`valueLiftCLM_unique` 对任意已经合法的目标 v 使用其 value=P(value u)，得到整个 jet 等于该提升。这里没有将未知梯度与同值函数直接等同：所有比较对象先已携带全部原弱导数链。
5. **具体 H² 存在在内部清偿。** 对真实 F(x)=x+ψ(x)e_r，目标是准确的 F⁻¹T，P 为已有保测度 homeomorphism 的实际 L² 复合等距。输入保持 T 开放、全局 C∞ ψ、法向平移不变、真实高度 Lipschitz C 及每个真实斜率 Lipschitz B_i。`graphShear_H2_value_exists` 调用 T239 的 `exists_graphShearPullback_H2`，从其完整 H¹ 截断身份取 value，内部得到泛型 hl。已完整重读 T239 的实际实现：原 H² 的弱链先给拉回梯度导数，真实斜率乘积法则保留两个交叉项、二次斜率项和曲率项；实际 L² 界及弱 Riesz/混合交换构造完整 H²。这里没有输入变换后 H²、候选 Hessian 或目标连续性。
6. **同一实际对象和测度。** `graphShearH2Pullback` 先由真实 homeomorphism 连续性使 F⁻¹T 开放，再用上述内部 hl 构造 H²→H² 的 CLM。其 value 严格为 P(value U)，AE 结论继承真实 `Lp.compMeasurePreserving` 代表公式，测度恰为 `volume.restrict(F⁻¹T)`。没有改用全空间零延拓、其他空间域、任意点值代表或仅形式上的函数复合。
7. **完整 H¹ 截断及真实 H¹₀。** 拉回 H² 后截断，与先截断 U 再作已有 H¹ 拉回，两边都是合法 H¹ jet；精确 value 身份相同后，开放域弱唯一性推出整个 H¹ 等式。因此原一阶导数也保持同一真实拉回。若原截断属于原 `dirichletJetSpace T`，调用已有 H¹ 闭包保持：实际测试的拉回仍为目标紧支光滑测试，真实 H¹ 拉回连续性传递其测试逼近。最终得到目标截断属于真正 H¹₀。这里仅保持 H¹₀，未宣称 H²₀ 或所有一阶边界导数为零。
8. **完整 H² 强收敛和全部测试字段。** `graphShearH2Pullback_tendsto` 对原完整 H² jet 范数收敛序列，使用同一固定 CLM 的连续性，给同一目标完整 H² jet 的范数收敛，含 0、1、2 阶字段；不是仅标量 L² 收敛。`graphShearH2Pullback_test` 比较原 φ 的 `allOrderJet 2` 与真实 φ∘F 的 `allOrderJet 2`。已读实际 allOrderJet：迭代光滑导数、置换一致性与真实弱测试链构造所有字段。实际 `pullbackSmoothHomeomorph` 通过 homeomorphism 保紧支和准确支撑原像构造合法目标测试，保测度 Lp 身份给两边相同 value，目标弱唯一性给完整二阶 jet 相等；没有只核对零阶函数而略去高阶资格。

闭图定理只证明每个固定 P/域/图数据所确定映射的连续性，未给跨高度、图册、穷竭域的统一算子范数。固定 C、B_i 位于全部状态与序列之前；本批没有新增与周期 T 有关的估计，代码中的 T 是空间集合。泛型提升允许任意 m/n 与空域；具体 shear 的 r:Fin d 要求真实坐标方向，没有虚构零维法向。所有空间可无限维且域无需有界。本批没有构造原域图、证明保持边界的强 H² 密度、把坐标局部常数当凸域统一常数或完成 P023。

## 全部声明逐项结论

名称统一带前缀 `Carleman.WeakSobolevJet.`；源码行为固定 `StrongH2GraphTransport.lean`，raw 行为固定完整类型的起点。清单从固定 C268/T252 台账提取并与源码和审计逐项核对。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 15 / 43990 | `valueLiftLinear` | PASS（定义）；真实存在前提与目标弱唯一性给线性选择。 |
| 36 / 44000 | `valueLiftLinear_value` | PASS；同一实际标量 L² 值身份。 |
| 43 / 44011 | `valueLiftLinear_closedGraph` | PASS；完整弱 jet 乘积中的真实闭等式集。 |
| 64 / 44021 | `valueLiftCLM` | PASS（定义）；两端完整 Banach 图范数与实际闭图定理。 |
| 71 / 44031 | `valueLiftCLM_value` | PASS；连续提升保留原值映射。 |
| 78 / 44041 | `valueLiftCLM_unique` | PASS；任意合法目标 jet 的全部字段唯一性。 |
| 93 / 44053 | `graphShear_H2_value_exists` | PASS；真实 T239 二阶弱链内部供应 H² 存在资格。 |
| 103 / 44061 | `graphShearH2Pullback` | PASS（定义）；准确原像域和真实 L² 复合的完整 H² CLM。 |
| 111 / 44069 | `graphShearH2Pullback_value` | PASS；实际 P 的精确 L² 身份。 |
| 117 / 44077 | `graphShearH2Pullback_ae` | PASS；真实目标限制测度下同一原值复合。 |
| 124 / 44087 | `graphShearH2Pullback_truncate` | PASS；完整 H¹ 截断等于原 H¹ 拉回。 |
| 131 / 44097 | `graphShearH2Pullback_dirichlet` | PASS；真实原 H¹₀ 闭包成员保持。 |
| 138 / 44109 | `graphShearH2Pullback_tendsto` | PASS；同一固定图映射传递完整 H² 强收敛。 |
| 144 / 44119 | `graphShearH2Pullback_test` | PASS；实际光滑拉回测试的完整 H² jet 身份。 |

## 固定依赖与本地证据

实际 Carleman 导入闭包 **214 文件**，其中 **213 旧文件**相对 base 逐 Git blob 不变；唯一新增数学模块为本批模块。除本批外，本次完整读取 `GraphShearHessianTransport`、`SobolevTopology`、`SpatialTestAllOrders`，重读 `SobolevJet`、`SobolevRealization` 的真实载体/值唯一性、`GraphShearWeakTransport` 的实际 H¹ 构造/连续性/测试闭包保持、`NonlinearGraphShear` 的测试支撑与实际 Lp 复合。mathlib `LinearMap.continuous_of_isClosed_graph` 和 `ContinuousLinearMap.ofIsClosedGraph` 的具体实现与完备性前提已直接读取。

T239 冻结报告全文已读：提交 `1ff2f759dc1ef22d08032d49f9312c17f22222a7`，proof=`5f61d27fd056feaadbafcf3363d7c25f88036481`，reviewed_at=`2026-10-20T08:07:12+00:00`，6/6 PASS；该提交的报告与当前固定 proof 中内容逐字节相同。其 **208 文件**依赖闭包从原已审 proof 到本批独立逐 blob 核对不变。没有以报告代替实际 H² 存在构造审查。

固定 C268/T252 台账、源码和 raw 的全部 14 项及顺序一致（11 theorem、3 def）。Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入和全部 14 项 `#check`/`#print axioms` 齐全。

- `/tmp/carleman-t252-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T09:52:00.771874+00:00`；实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 执行记录均 exit 0。
- `/tmp/carleman-t252-local-source-manifest.txt`：**1049 项、113861 bytes**，SHA256 `9358e4ebf337d55747ed434bdc55fd012baa0ea06850e8bdbcfc947c59de06a0`。独立枚举固定提交全部 tracked `.lean` 与三个工具链配置，路径集合、唯一性和各项摘要全部匹配固定 Git blob。
- `/tmp/carleman-t252-target-build.log`：**3394 jobs** 成功，111 bytes，SHA256 `1ea81edf416f695effe2282725010b554e7ff328a44a5cd61cb6eeb808f725b6`。`/tmp/carleman-t252-build.log`：**4291 jobs** 成功，80 bytes，SHA256 `52f7ad58543a379af55124e3469b2b47a660bb607f13f921d837bf74ad17a9e7`。`/tmp/carleman-t252-axioms.log` 为 0 bytes。
- `/tmp/carleman-t252-strong-h2-graph-transport-local-axioms.txt`：**3393148 bytes**，SHA256 `621a0aa454600cb753ed837e00dbb4dcce980e4e333f7287e47789f70d24014f`。14 项类型和公理逐项核对；全文件 **4057 个显式公理记录**仅含 `propext`、`Classical.choice`、`Quot.sound` 或无公理。实际尾部为 **10095 声明递归审计 PASS**；全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，无 sorryAx 或额外数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，未重跑全库、未查询远端 CI/看板，未把本地成功称为 CI。

无修复项。接受 **AUXILIARY 固定实际图剪切的完整 H² 连续线性传输**，保持 18/26，P023 不提升。正文与 reviewed_at 冻结后仅提交本报告，不改数学、台账、原稿、根导入、公理工具或其他报告，不 push。
