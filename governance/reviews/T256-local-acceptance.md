# T256 / C272 独立本机验收

- checked_sha: `10790206877d2b10b557b56430b8b0c4ec02b117`
- mathematical_base: `2b7dfa5b8dc39445682940c02d91c5bec5a747a0`
- reviewed_at: `2026-10-20T10:31:03+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，14/14 显式声明（12 定理、2 定义）；未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；给定全局光滑图的两侧、实际紧支值 H²∩H¹₀ 状态的完整 H² 光滑零边界逼近。保持 18/26，P023 不提升。**

完整读取固定 `Carleman/Spatial/CompactGraphDensity.lean`、全部原始展开类型及公理、analysis/MATH_SPEC/固定台账，并对照 `paper/main.tex:2659–2665` 原 Corollary A.2。原命题要求指定凸多面体/盒上的全部空间解析假设；本批提供图域强密度这一辅助步骤，没有证明原一般域的有限拼接、弱凸域统一 Hessian 估计或最终多面体穷竭。

## 实际数学核对

1. **逆剪切不是替代映射。** 原 F(x)=x+ψ(x)eᵣ，实际逆为 x−ψ(x)eᵣ。`graphShearInverseH2_value_exists` 对任意 T 上的原像域 S=F⁻¹T 的完整 H² 状态 V，取负高度剪切 G。`graphSlopeMultiplier_neg` 由真实 fderiv_neg 给出斜率逐点变负，原 C 与每个 Bᵢ 的 Lipschitz 资格因此保持；法向平移不变性也由原身份取负得到。T239 实际二阶弱链构造 U，并给整个 H¹ 截断等于负剪切的真实 H¹ 拉回。随后 G=F.symm 和 F.symm⁻¹S=T 的精确集合身份将目标还原为原 T；没有增加目标 Hessian、光滑状态、紧性或边界正则性假设。
2. **真实 H¹₀ 与完整 H² 连续性。** 上一步的 H¹ 截断身份配合原 `graphShearPullback_dirichlet`，把 S 的实际测试闭包送入 T 的实际测试闭包。该旧实现直接以原 H¹ 图闭包近似、全局剪切后的合法紧支测试及完整 H¹ 连续性证明，没有以点态零边界定义 H¹₀。新 inverse CLM 则调用 T252 的 `valueLiftCLM`：真实逆保测 L² 拉回提供连续值映射，上一步内部供应每个 V 的 H² 存在性，目标开放域弱导数唯一性给线性和闭图，源/目标完整 H² Banach 拓扑给连续性。所选 lift 的 Dirichlet 资格通过同值合法 jet 的唯一性识别回上述实际构造。该映射定义于全部 H² 状态，H¹₀ 是随后保持的性质；不把源空间预先缩成光滑或零法向导数状态。
3. **左右逆覆盖全部弱 jet。** 左逆先用实际 `homeomorphPullbackLp_inverse` 消去两次 L² 拉回，再由目标开放域 value_injective 恢复全部阶导数字段。右逆在 S 上使用同一弱唯一性，再把值等式送入实际逆拉回的等距单射，并应用同一真实 L² 逆恒等式。两者都是整个 H² jet 等式，不是只恢复一个代表、H¹ 截断或单向嵌入。`graphShearInverseH2_tendsto` 的源、目标都是完整弱 H² 图拓扑，直接由同一固定 CLM 连续性得出；这里无随图、高度、域或穷竭索引变化的统一范数结论。
4. **跨边界光滑函数合法。** 两个 globalTest 定理的 φ 是 `SpatialTest univ`，允许其支持遇到和跨过实际边界。`pullbackSmoothHomeomorph` 的 value 是真实复合，C∞ 由实际 F/F.symm 的光滑性给出，紧支由同胚的紧支复合定理给出；本次取的支持目标是 univ，没有要求 φ 在 T 或 S 内部紧支。实际 restricted-volume 保测拉回和 `pullbackSmoothHomeomorph_toLp` 给相同标量 L² 类，再由弱 jet 唯一性识别整个 `allOrderJetOn ... 2`。已核对该 toLp 身份在任意符合资格的原/目标测度下用真实 AE 运输证明，未将空间测试的支持域与积分域混淆。
5. **紧支值按正确测度运输。** 输入仅要求 value(u) 在 T 的限制体积下几乎处处于紧集 K 外为零；不要求连续代表、K⊆T、K 远离边界，或导数字段的点态支撑。F 是真实同胚，所以 F⁻¹K 紧。`hm.quasiMeasurePreserving.ae hu` 将该原条件沿实际 F 从 volume|T 拉回 volume|S；和同一 forward H² map 的 AE 值身份合并后，得到拉回状态 V 在 F⁻¹K 外的 AE 零值。此处没有在不同限制测度之间直接移动零集，也没有把任意 Lp 代表当成处处紧支函数。原非线性剪切的 Jacobian 确为 1，restricted measure-preserving 由真实换元建立，未遗漏密度因子。
6. **同一序列、全部 frontier、同一原状态。** 泛型逼近定理显式输入 hhalf:S=signedCoordinateHalfspace，借其改写 T255 后，给同一个实际 V 构造同一条 Aₙ：全空间紧支光滑、全部半空间 frontier 零值、每项真正 H¹₀、完整 H² 强收敛。设 Uₙ=Aₙ∘F.symm。对任意 x∈frontier T，真实同胚身份 `F⁻¹(frontier T)=frontier(F⁻¹T)` 和 F(F.symm x)=x 给 F.symm x∈frontier S，故每个 Uₙ 的真实点值为零。该论证既不依赖边界零测，也不对弱状态 u 求边界点值。逆向 globalTest 精确识别每项完整 jet，逆向 Dirichlet 保持给每项 H¹₀，完整 inverse 连续性给极限 inverse(V)，最后全 jet 左逆把它识别为原 u.val。结论不替换为别的同载荷解、截断状态或仅有相同值的未经证明导数数据，也没有按测试/方向另取子列。
7. **两侧及保留假设。** `graphCoordinateSide` 的 true/false 分别是严格上图域和严格下图域；开放性由实际连续坐标及 ψ 给出。原像公式分别调用真实 upper/lower 剪切代数身份，返回同号严格坐标半空间。最终定理因此内部清偿 hT 和 hhalf；原 C∞ψ、全局高度 Lipschitz C、实际各斜率 Lipschitz Bᵢ、法向不变性、紧集 K、原 H²∩H¹₀ 与 AE 支撑仍明确在类型中。没有假设逼近序列、全局 H² 零延拓、目标 H² 正则性或统一估计。r:Fin d 自带正维资格；此批不声称 d=0 的图域结论。K 允许为空或跨边界。每个近似函数确为全局紧支光滑，但结论不宣称所有支持都等于 K，也不要求近似函数在边界邻域消失，因此未偷换 H²∩H¹₀ 为 H²₀。

## 全部声明逐项结论

省略共同前缀 `Carleman.`。源码行指固定 `CompactGraphDensity.lean`；raw 行为完整类型起点。固定 T256 和 C272 的 14 项清单、源码种类/顺序及原始审计完全匹配。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 18 / 44437 | `WeakSobolevJet.graphShearInverseH2_value_exists` | PASS；负高度剪切内部构造真实逆拉回 H² jet，并保留原 H¹₀；域精确还原 T。 |
| 60 / 44453 | `WeakSobolevJet.graphShearInverseH2` | PASS（定义）；实际逆 L² 拉回经真实 H² 存在性与完整弱图闭图定理升为 CLM。 |
| 69 / 44461 | `WeakSobolevJet.graphShearInverseH2_value` | PASS；逆映射值精确等于原保测逆拉回 L² 类。 |
| 78 / 44471 | `WeakSobolevJet.graphShearInverseH2_dirichlet` | PASS；所选 lift 通过全 jet 唯一性等于具备真实 Dirichlet 资格的构造。 |
| 90 / 44485 | `WeakSobolevJet.graphShearInverseH2_left_inverse` | PASS；真实 L² 逆恒等式和开放域弱唯一性给整个原 H² jet 的左逆。 |
| 95 / 44495 | `WeakSobolevJet.graphShearInverseH2_right_inverse` | PASS；真实逆拉回等距单射及弱唯一性给整个 H² jet 的右逆。 |
| 107 / 44507 | `WeakSobolevJet.graphShearInverseH2_tendsto` | PASS；固定逆 CLM 对完整 H² 强收敛连续，不是仅值极限。 |
| 116 / 44522 | `WeakSobolevJet.graphShearH2Pullback_globalTest` | PASS；全局紧支光滑 φ 可跨边界；完整正向 jet 等于实际 φ∘F 的限制。 |
| 126 / 44532 | `WeakSobolevJet.graphShearInverseH2_globalTest` | PASS；完整逆向 jet 等于实际全局光滑 φ∘F⁻¹ 的限制。 |
| 139 / 44541 | `exists_compact_graphShear_strong_h2_approximation` | PASS；给定真实半空间原像，内部运输紧支值、H¹₀、半空间密度及真实 frontier，回到同一原状态。 |
| 190 / 44559 | `graphCoordinateSide` | PASS（定义）；明确两侧开图域：true 为 ψ(x)<xᵣ，false 为 xᵣ<ψ(x)。 |
| 193 / 44562 | `graphCoordinateSide_isOpen` | PASS；连续高度和真实坐标评价供应两侧开放性。 |
| 199 / 44565 | `graphCoordinateSide_preimage` | PASS；由法向不变性及真实剪切公式，分别得到正/负坐标半空间的精确原像。 |
| 208 / 44571 | `exists_compact_graphSide_strong_h2_approximation` | PASS；最终两侧实例内部清偿开放性及半空间原像，不输入逼近序列或目标正则性。 |

## 固定依赖与本地执行证据

Carleman 实际导入闭包 **297 文件**，其中 **296 个旧文件相对 mathematical_base 逐 Git blob 不变**；唯一新增数学模块为本批模块。直接核对新调用所用的 `CompactHalfspaceDensity` 全部实现，以及 `GraphShearHessianTransport` 的实际二阶弱链/负高度与斜率身份、`GraphShearWeakTransport` 的真实 H¹₀ 闭包保持、`NonlinearGraphShear` 的真实同胚/保测/测试复合/L² 逆、`StrongH2GraphTransport` 的完整闭图 lift。既有完整弱 jet、真实 H¹₀ 与 allOrderJetOn 定义在此前审查中已读，本固定闭包未修改；没有重新全量审计不变历史或以说明文字代替本批实际调用。

T255 正式冻结报告已全文读取，且固定 proof 中字节与提交 `e3323d1266fafb02105b718427ecaa604aa8ca59` 相同：checked_sha 为本报告 base，reviewed_at=`2026-10-20T10:23:07+00:00`，10/10 PASS；13792 bytes，SHA256 `a6026628df6b63fe5de291c5f7dd86177cf9abcd3f82bf64a11efbbff6474395`。T254 报告与实际调用也已接受；本批没有绕过其支撑条件，把两次截断未经证明地视为恒等。

固定根导入包含本模块，14 项 `#check`/`#print axioms` 完整；递归审计末段的命名空间收集及基础公理白名单逻辑相对 base 不变。Lean **4.35.0**、编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib lock 与本机无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。实际 Homeomorph frontier 恒等式与调用方向也已核对。

- `/tmp/carleman-t256-local-evidence.json`：source=local、PASS，checked/source 均为 `10790206877d2b10b557b56430b8b0c4ec02b117`；finished_at=`2026-10-20T10:26:19.876656+00:00`。实际根构建及完整公理审计命令记录均 exit 0；固定台账定向记录为 exit 0。
- `/tmp/carleman-t256-local-source-manifest.txt`：**1053 项、114295 bytes**，SHA256 `7352540971bf9c1be8010a1de6d7b99bc12752ca1f98309758c22a4460aac040`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置；路径集合、唯一性与每个摘要全部匹配固定 Git blob，未使用未来工作树代替。
- `/tmp/carleman-t256-target-build.log`：**3482 jobs** 成功，108 bytes，SHA256 `d82d1966dc80bc7f555d6e8e4796b34d98c6c3dca49ccb46492296771e68b3c3`。`/tmp/carleman-t256-build.log`：**4295 jobs** 成功，80 bytes，SHA256 `92bcf7ff8ac1ad5210a8881f1d23d979a682b34824aa827c12dae29a80daa966`。`/tmp/carleman-t256-axioms.log` 为 **0 bytes**。
- `/tmp/carleman-t256-compact-graph-density-local-axioms.txt`：**3432583 bytes**，SHA256 `38572815097163190eb16650ab982768e91d120c4f14efaf3accbb1a53643a3c`。14 项完整展开类型及依赖公理已逐项读取；全文件 **4110 个公理列表**仅含 `propext`、`Classical.choice`、`Quot.sound`，另有 **10 个无公理记录**。实际末行 **10238 声明递归审计 PASS**；无 sorryAx 或新增数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。以上为核实的固定本地执行证据；未重复全构建，未查询远端 CI/看板，未将本地验证称为 CI。

**无修复项；接受 T256/C272 的上述 AUXILIARY 范围，原文覆盖保持 18/26。** 原局部几何到全域有限拼接、弱状态统一凸域估计和最终原多面体结论仍在范围外。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、root、公理工具、其他报告或未来草稿，不 push。
