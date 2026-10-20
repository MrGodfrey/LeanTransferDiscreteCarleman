# T250 / C266 独立本机验收

- checked_sha: `49168d2536a37eebacf348295cdeb46a8a3f5a90`
- mathematical_base: `c159999f8e61e66bab2d2a7023bc23eb5aa64d0b`
- reviewed_at: `2026-10-20T09:39:00+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，20/20 声明（18 定理、2 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；真实光滑水平截断、边界层权、完整支撑及紧性、逐点 indicator 收敛和两个原加权积分身份。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Geometry/SmoothLevelCutoff.lean`、20 项 raw 完整类型与公理、analysis/MATH_SPEC/台账，核对原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 的全凸域正则性与统一椭圆估计并未由本批单独完成；实际积分极限、经典统一估计、保持边界的 H² 强逼近仍待。

## 实际数学与量词核对

1. **使用真实光滑过渡函数。** 已读取 mathlib `Real.smoothTransition` 的具体构造、正分母、全局 C∞、单调性、[0,1] 值域和两个闭平台。对 t≤0，函数在 t 处取真实全局最小值 0；对 t≥1，取真实全局最大值 1。代码以这些实际极值建立局部极值，再用 Fermat 定理推出真实 `deriv` 为零，包含 t=0 和 t=1。并未将端点误认成有邻域恒值点；过渡函数实际 C∞，所以也未依赖不可微时 `deriv` 的默认值冒充经典导数。
2. **原 η、κ 的准确尺度。** 两个定义实际为
   `ηε(x)=transition((a−g(x)−ε)/ε)`，
   `κε(x)=transition'((a−g(x)−ε)/ε)/ε`。
   对光滑 g，通过真实复合及常数除法给两者全局 C∞；κ 的光滑性使用真实 transition 导数的 C∞。η 的 [0,1] 界不需要 ε 正性；κ 的非负性则明确由实际单调函数导数非负及 ε>0 给出。没有额外假设一个权的光滑性或一个候选导数。
3. **两条闭平台的数值与导数。** 对 ε>0，g≥a−ε 使过渡变量≤0，故 η=0、κ=0；g≤a−2ε 使过渡变量≥1，故 η=1、κ=0。实际使用正分母的有序除法，系数 2 与偏移 −ε 准确。κ 的两个零值结论使用第 1 项闭平台导数，因此两端水平上的导数也为零。
4. **真实 Fréchet 链式，保留负号和 ε⁻¹。** 内层 A(x)=(a−g(x)−ε)/ε 的实际导数为 `ε⁻¹·(−Dg)`；真实一维 `HasDerivAt transition` 与它复合，逐方向给完整连续线性泛函等式 `Dηε=−κεDg`。没有把该链式身份作为输入。该等式和光滑性声明允许任意实 ε；ε=0 时 Lean 的总除法使 η、κ 及两侧导数都为零，数学上与其定义一致。所有使用正层宽的零值、支撑、κ 非负、紧性、收敛及积分应用均明确要求 ε>0，未借零分母情形作几何推理。
5. **完整拓扑支撑，而非仅普通 support。** 对非零函数值用第 3 项排除外平台，再利用连续 g 的闭子水平取 support 的闭包，得到 `tsupport η⊆{g≤a−ε}`。对 κ 同时排除两个平台，并对闭集合 `{a−2ε≤g≤a−ε}` 取闭包，得到整条闭层支撑。虽 κ 在两个端水平上本身为零，其拓扑支撑可以包含端水平，结论保留闭层正确。没有从普通 support 的严格不等式直接推断闭支撑仍满足同一严格不等式。
6. **紧支资格由真实原域紧闭包供应。** 泛型前提 `IsCompact(closure{g<a})` 保持明确。ε>0 将上一项的完整支撑放入 `{g≤a−ε}⊆{g<a}`，继而包含于其紧闭包；`isClosed_tsupport` 与实际紧集闭子集定理给两个 `HasCompactSupport`。证明不要求每个水平集单独紧，也未假定整个 g 或最终未截断函数紧支。它对空子水平域亦合法。具体原有界指数和内域已有紧闭包定理，但本批泛型接口没有伪称自动构造所有 g 的紧闭包。
7. **所有点的准确 indicator 极限。** 对任意正序列 εₙ→0、任意固定 x：若 g(x)<a，真实正间隙 a−g(x) 使 `2εₙ<a−g(x)` 最终成立，因而 ηₙ(x) 最终严格等于 1；若 g(x)≥a，每个 n 都满足外平台条件，ηₙ(x)=0。故极限是原 `{g<a}` 的真实 indicator，特别 g(x)=a 时也是 0。没有排除边界点、没有边界零测假设；该点态定理甚至不需要 g 连续、可测或紧闭包。未从点态收敛擅自推出积分或 Sobolev 收敛，亦未假设 εₙ 单调。
8. **两个原积分调用资格均内部清偿。** 最后两定理选择的正是上述同一 ηε 和 κε，以实际 η 光滑、真实紧支与完整 Dη=−κDg 调用 T249。得到全空间真实 Lebesgue 积分
   `∫ηε[(Δu)²−HessSq(u)]=∫κεF(u,g)` 和
   `∫κε‖∇g‖²=∫ηεΔg`。
   已完整重读 `WeightedHessianIdentity`：原 HessSq 是全部有序坐标对的平方和，F 为已识别的实际通量；分部积分与有限求和拆合有真实紧支乘积可积性，链式代入保留两个负号的准确抵消。当前 g/u 光滑、η/κ 紧支还直接保证相关整个乘积连续紧支，未利用非可积函数积分的默认值。无需给 u 加紧支、零边值或 PDE 假设；第一式中的 u 是任意全局 C∞ 函数，第二式只用原 g。

结论对任意 d、实 a 和上述原函数成立，无固定坐标、非零梯度或非空层前提。κ 可以随 ε 缩小而增大，本批没有声称统一 L∞/L¹ 层界。T248 给的是 frontier 上的通量符号，不能仅凭 κ 支撑靠近 frontier 就推断整层通量非负；本批只证明精确恒等式，没有作此推断。强边界逼近、边界层积分极限、统一 Hessian 估计及原多面体传递继续保留。

## 全部声明逐项结论

名称统一带前缀 `Carleman.`；源码行为固定 `SmoothLevelCutoff.lean`，raw 行为固定审计文件完整类型的起点。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 14 / 43858 | `smoothTransition_deriv_zero_of_nonpos` | PASS；真实全局最小值及 Fermat，含端点 0。 |
| 21 / 43860 | `smoothTransition_deriv_zero_of_one_le` | PASS；真实全局最大值及 Fermat，含端点 1。 |
| 28 / 43862 | `levelCutoff` | PASS（定义）；真实水平截断及准确偏移/尺度。 |
| 31 / 43864 | `levelLayerWeight` | PASS（定义）；真实 transition 导数除以同一 ε。 |
| 34 / 43867 | `levelCutoff_contDiff` | PASS；原 g 的光滑复合内部给 η 的 C∞。 |
| 38 / 43870 | `levelLayerWeight_contDiff` | PASS；实际 transition 导数与复合给 κ 的 C∞。 |
| 44 / 43873 | `levelCutoff_bounds` | PASS；真实全局 [0,1] 界。 |
| 48 / 43876 | `levelLayerWeight_nonneg` | PASS；单调导数及正层宽给 κ≥0。 |
| 52 / 43879 | `levelCutoff_zero` | PASS；g≥a−ε 的准确闭外平台。 |
| 57 / 43882 | `levelCutoff_one` | PASS；g≤a−2ε 的准确闭内平台。 |
| 64 / 43885 | `levelLayerWeight_zero_outer` | PASS；闭外平台上实际导数为零。 |
| 69 / 43888 | `levelLayerWeight_zero_inner` | PASS；闭内平台上实际导数为零。 |
| 75 / 43891 | `levelCutoff_fderiv` | PASS；真实完整链式 Dη=−κDg，符号/尺度正确。 |
| 90 / 43895 | `levelCutoff_tsupport` | PASS；连续性和 support 闭包给完整子水平支撑。 |
| 98 / 43898 | `levelLayerWeight_tsupport` | PASS；两平台与闭包给完整闭层支撑。 |
| 109 / 43901 | `levelCutoff_compact` | PASS；原紧闭包内部给实际 η 紧支。 |
| 120 / 43904 | `levelLayerWeight_compact` | PASS；原紧闭包内部给实际 κ 紧支。 |
| 130 / 43907 | `levelCutoff_tendsto` | PASS；全部点包括边界的原 indicator 极限。 |
| 144 / 43912 | `levelCutoff_hessian_identity` | PASS；内部清偿权资格和链式，实际 Hessian/通量积分等式。 |
| 152 / 43918 | `levelCutoff_gradient_mass` | PASS；同一 η/κ 的实际梯度质量积分等式。 |

## 固定依赖与本地证据

实际 Carleman 导入闭包 **225 文件**，其中 **224 旧文件**相对 base 逐 Git blob 不变；唯一新增数学模块为本批模块。本次完整读取本批、直接调用的 `WeightedHessianIdentity`，并核对已验收原通量/梯度/Hessian 定义。mathlib `SmoothTransition` 的实际构造与证明、`IsLocalMin/Max.deriv_eq_zero`、`Monotone.deriv_nonneg` 均直接读取。

T249 正式报告全文已读，并核对冻结单文件提交 `693e3dcbffa41ea9d1a3252d80b4898774e336e1`，checked_sha 为本报告 base、reviewed_at=`2026-10-20T09:30:30+00:00`，11/11 PASS。提交内容与已读报告逐字节相同（10304 bytes，SHA256 `edb193a9fa9e221cfa18eb403e7621d4ce64876e6992ad51e37158b6c130813c`）。该报告未替代本次实际积分调用审查。

源码、独立清单、T250/C266 台账和 raw 的 20 项顺序一致；实际 18 theorem、2 def。Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入和全部 20 项 `#check`/`#print axioms` 齐全。

- `/tmp/carleman-t250-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T09:33:37.494813+00:00`；实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 的执行记录均 exit 0。
- `/tmp/carleman-t250-local-source-manifest.txt`：**1047 项、113641 bytes**，SHA256 `59285f4ad2c8fcd14ab038916881c875675f9bc21cbc8d47b179ec66e51594f1`。独立枚举固定提交全部 tracked `.lean` 和三个工具链配置，路径集合、唯一性与逐项摘要全部匹配固定 Git blob。
- `/tmp/carleman-t250-target-build.log`：**3410 jobs** 成功，107 bytes，SHA256 `152ba5912dcd6f944fd4a61853230135f91082568fcd5d71c7ad0e40cdbe8822`。`/tmp/carleman-t250-build.log`：**4289 jobs** 成功，80 bytes，SHA256 `dc89810eea4a47012e9b9220c0ef321e6fadd43f2fb2d88d14734914de6ed3b4`。`/tmp/carleman-t250-axioms.log` 为 0 bytes。
- `/tmp/carleman-t250-smooth-level-cutoff-local-axioms.txt`：**3375375 bytes**，SHA256 `3a2de99a5182a125c017ef227dda032889e678a926f0885d100d2d067b5db681`。20 项完整类型及公理逐项核对；全文件 **4034 个显式公理记录**仅含 `propext`、`Classical.choice`、`Quot.sound` 或无公理。实际尾部为 **10052 声明递归审计 PASS**；全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，无 sorryAx 或额外数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地证据，未重跑全库、未查询远端 CI/看板，未把本地成功称为 CI。

无修复项。接受 **AUXILIARY 实际光滑水平截断与两个精确积分身份**，保持 18/26，P023 不提升。正文与 reviewed_at 冻结后仅提交本报告，不修改实现、台账、原稿、根导入、公理工具或其他报告，不 push。
