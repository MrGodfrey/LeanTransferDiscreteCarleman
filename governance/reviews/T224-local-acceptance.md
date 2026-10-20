# T224 / C240 独立本机验收

- checked_sha: `03f8c203f00dc90f126a44f9200c5ac56f645752`
- mathematical_base: `7413b28a97681bcf834d35701a7ca878ebac1b99`
- reviewed_at: `2026-10-20T05:54:29+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，15/15 显式声明（13 定理、2 定义），无阻断缺陷。**
- scope: **AUXILIARY；C240 可按本范围验收，原文 17/26 不变。**

已完整读取固定 Git 对象中两新模块、15 项 raw 类型/公理、所用原定义和关键依赖，核对固定分析、MATH_SPEC、C240/T224 清单与 `paper/main.tex:2618–2635`。本批识别实际一般弱系数微分表达式与原形式关联算子的图；一般椭圆正则性、允许权交换子界和完整 Proposition A.1 仍未由本批完成。

## 数学核对

1. **实际测试与有限弱链的符号。** `wordTest` 是原紧支 C∞ 测试的实际逐坐标导数，仍保留支撑；`wordTest_append` 的顺序为 D_l(D_rφ)，与递归定义一致。`wordTest_derivativeTest` 经列表拼接和原光滑测试混合导数交换得到 D_l(D_iφ)=D_{i::l}φ，没有预设状态或系数的经典混合导数。`weakWordChain_test` 只输入 U_l 到 U_{i::l} 的真实分布链，在 |l|≤n 内逐次对实际导数测试分部积分，得 ⟨U_l,φ⟩=(−1)^|l|⟨U_[],D_lφ⟩。归纳每步使用原弱导数的负号，空词符号为 1；不需要 U 的排序对称性或状态边界条件。
2. **系数微分项是完整真实 Leibniz 和。** `coefficientDifferentialTerm a u l r` 定义为 derivativeSplits(l) 列表上的 Σ (D^{p₁}a)D^{p₂++r}u。该列表每次分别把新坐标放在系数和状态侧，保留全部重复项和二项式重数，不去重。每项是实际有界乘子作用于原 L² 词字段，因此总和属于 L²。空 l 恰为 aD^r u；定义虽对所有词存在，导数结论明确限制 |l|+|r|≤n，并不把超阶默认字段当真实导数。
3. **全部阶数资格内部清偿。** 在 |l|+|r|<n 下，分裂长度恒等式给 |p₁|<n 和 |p₂++r|<n；状态和系数的下一阶最多为 n。`coefficientDifferentialTerm_weak` 对每项调用 T222 的真实弱有界系数乘积法则，再由有限和分部积分恢复下一阶完整列表。没有加入系数光滑性、外部乘后 jet 或目标微分公式。`coefficientDifferentialTerm_test` 使用 n−|r| 的有限链；其输入 |l|+|r|≤n 已保证 |r|≤n，故自然数减法不截掉合法阶数。得到 D^l(aD^r u) 的真实测试身份，未要求 aD^r u∈H₀^|l|。
4. **完整原形式的 α/β、符号与坐标身份。** `MultiDerivativeIndex d m` 是所有 k≤m 及全部 Sym(Fin d,k)，原所有低阶、零阶、混合和非对角系数均在双重求和内。`coefficientDifferentialOperator` 精确为 Σ_{α,β}(−1)^|α|D^α(a_{αβ}D^βu)，不是替代算子。对每项 |α|+|β|≤2m，因此上一项适用于原 H^{2m} 射流。分部积分产生第二个 (−1)^|α|，两符号相乘为 1。`coordinateVector_represents`、`wordField_vector`、新截断分量身份及 `allOrderJet_component` 将原词字段精确识别为 D^βu 与 D^αφ，没有排列或范数因子。右侧由 `coefficientJetForm_apply/integral` 正是 Σ∫a_{αβ}D^βu D^αφ；bounded multiplier×L² 与另一 L² 配对可积。此测试身份本身不需要对称性或 coercivity。
5. **原全部 H₀ᵐ 测试，没有闭包偷换。** `higherDirichletJetSpace_eq_closure` 已直接读取：测试集在加法/数乘下闭合，故其 span 的 Hᵐ 闭包确实等于原测试 jet 集的闭包。新 `coefficientDifferentialOperator_form` 固定 u，证明两侧关于 v 的等式集合闭合：左侧用真实零阶 valueCLM 和 L² 内积连续性，右侧用完整系数形式 CLM 的连续性。测试身份通过 `closure_minimal` 推广到整个原 H₀ᵐ 射流空间。闭包是全部弱字段的 Hᵐ 图拓扑，不是 L² 闭包；未输入所有 H₀ᵐ 测试上的目标等式。u 此处仍只需 H^{2m}，零边界资格仅在之后构造算子图时使用。
6. **真实原关联算子图由公式推出。** `higherCoefficientOriginalForm` 使用实际 H₀ᵐ 值域、Sobolev Hilbert 实现、原完整系数形式、a.e. 系数对称性及原 coercivity。已展开 `CoerciveForm.domainV/domain/operator` 与 `operator_isAssociated`：域由存在真实 L² 载荷、对全部能量空间测试满足变分式定义，载荷由真实稠密嵌入唯一识别，并非把新微分表达式定义成原算子。对任意 u∈H^{2m} 且其值∈H₀ᵐ，新证明从 truncate u 构造真实能量成员，以第 5 项供应全部测试变分身份，再经关联图等价得 z∈D(A)、z=u.value 和 Az=coefficientDifferentialOperator a u。H^{2m}∩H₀ᵐ→D(A) 因而是本批证明出的包含关系，没有附加算子域或图身份前提。
7. **已有域成员、域等式与 canonical jet。** 对既有 z∈D(A) 和同零阶 H^{2m} jet u，`OriginalForm.domain_le` 从原能量实现内部给 z∈H₀ᵐ；新图构造的 z′ 与 z 由相同 L² 值及 Subtype.ext 识别，故公式适用于同一个原 z。最后 `higherCoefficient_operator_domain_eq` 明确保留 hreg:D(A)⊆H^{2m}；正向使用 hreg 与 domain_le，反向使用已证图构造，得到原 D(A)=H₀ᵐ∩H^{2m}。`operator_canonical` 使用原 `domainSobolevJet` 的实际值恒等式，将公式绑定到同一 canonical 全弱射流。没有输出或隐含假定一般椭圆正则性的证明，也未使用/输出原定量 H^{2m} 图估计。hreg 是原论文域等式已蕴含的一向资格，不是额外改弱结论的替代条件。
8. **范围与退化情形。** 系数仅为原有限阶有界分布导数链，零阶 a.e. 对称性和完整原 Hᵐ coercivity 如实保留；没有要求经典系数导数、无限阶光滑、状态光滑核心或高阶边界条件。开域有限测度由原有界 Ω 满足，未新增几何正则性。m=0、d=0、空域及零状态不触发非法索引、正体积或除零，原 m≥1 是结论子范围。此批是精确身份，没有 q、T、网格或状态依赖的估计常数。将原允许权余项接到这个同一算子、证明严格降阶交换子和完整 A.1，仍是后续工作。

## 15 项完整清单

源码行相对于固定 `Carleman/Spatial/` 中模块；raw 行相对于下列固定本机公理文件。每项完整类型和实际定义/证明均已核对。

| 源码位置 | 声明 | raw 行 | 逐项结论 |
|---|---|---:|---|
| CoefficientDifferentialTerm:16 | `Carleman.SpatialTest.wordTest_append` | 40983 | PASS；实际词测试拼接，导数顺序正确。 |
| CoefficientDifferentialTerm:22 | `Carleman.SpatialTest.wordTest_derivativeTest` | 40986 | PASS；真实光滑测试导数交换。 |
| CoefficientDifferentialTerm:30 | `Carleman.weakWordChain_test` | 40990 | PASS；原有限弱链逐次分部积分，完整 (−1)^|l|。 |
| CoefficientDifferentialTerm:50 | `Carleman.WeakSobolevJet.coefficientDifferentialTerm` | 41002 | PASS；实际有界乘法及全部分裂列表和。 |
| CoefficientDifferentialTerm:55 | `Carleman.WeakSobolevJet.coefficientDifferentialTerm_nil` | 41008 | PASS；空外词恢复原 aD^r u。 |
| CoefficientDifferentialTerm:60 | `Carleman.WeakSobolevJet.coefficientDifferentialTerm_weak` | 41014 | PASS；内部弱乘法给下一阶真实弱链，阶数合法。 |
| CoefficientDifferentialTerm:79 | `Carleman.WeakSobolevJet.coefficientDifferentialTerm_test` | 41024 | PASS；D^l(aD^r u) 的完整原测试身份。 |
| CoefficientDifferentialOperator:20 | `Carleman.WeakSobolevJet.wordField_multiIndex_truncate` | 41037 | PASS；原多指标字段与截断字段精确相等。 |
| CoefficientDifferentialOperator:30 | `Carleman.coefficientDifferentialOperator` | 41043 | PASS；全部 αβ 微分表达式及原符号。 |
| CoefficientDifferentialOperator:36 | `Carleman.coefficientDifferentialOperator_test` | 41050 | PASS；两符号相消，精确匹配原系数形式。 |
| CoefficientDifferentialOperator:56 | `Carleman.coefficientDifferentialOperator_form` | 41062 | PASS；真实 Hᵐ 闭包推广到所有 H₀ᵐ 测试。 |
| CoefficientDifferentialOperator:77 | `Carleman.higherCoefficient_operator_graph_of_sobolev` | 41074 | PASS；内部构造原算子域成员并识别实际作用。 |
| CoefficientDifferentialOperator:95 | `Carleman.higherCoefficient_operator_eq_differential` | 41092 | PASS；既有域成员的边界资格内部供应，同值识别。 |
| CoefficientDifferentialOperator:112 | `Carleman.higherCoefficient_operator_domain_eq` | 41109 | PASS；只保留原一向 H^{2m} 正则性，证明域等式。 |
| CoefficientDifferentialOperator:130 | `Carleman.higherCoefficient_operator_canonical` | 41125 | PASS；同一原域成员 canonical 弱 jet 的算子身份。 |

## 固定依赖与本地证据

T223 正式冻结报告 `e7a58964e44140073a135d2004d2c4c762e73b54` 已全文读取（checked_sha 为本批基线，reviewed_at=`2026-10-20T05:51:29+00:00`，9/9 PASS）。本批仍直接读取其 `BoundedWeakCoefficient`、有限弱链及所需 T222 真实乘法调用。导入闭包 **168 模块**，除两新模块外的 **166 个旧模块与数学基线逐 Git blob 不变**。另直接读取原词字段/分裂、测试全阶 jet、H₀ᵐ 闭包、系数形式、实际 conforming Hilbert 嵌入、原变分算子域/关联等价、截断及 canonical Sobolev jet；不重复无关旧历史，不使用未来工作树或动态 raw。

- `/tmp/carleman-t224-local-evidence.json`：source=local、PASS，checked/source 精确等于本报告 proof SHA，finished_at=`2026-10-20T05:51:12.531427+00:00`；真实 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0。本次核对原执行记录和源码绑定，不声称重新执行全库，未查询远端 CI 或看板。
- 独立枚举固定提交全部 tracked Lean 文件及三项构建配置，与 `/tmp/carleman-t224-local-source-manifest.txt` 核对路径完整性、唯一性及逐 Git blob 字节摘要：**1016 项全部相同**，110232 bytes，SHA256 `3dc084d94b359223eedeecd78c0c603465d0aba7a230b525f9fcf2658443f374`。
- 实际 `/tmp/carleman-t224-target-build.log` 为 **3340 jobs** 成功，194 bytes，SHA256 `064ab4cd0ca26e10080e175b7914c23974db620dd34543d5807e26255ee34dd5`；`/tmp/carleman-t224-build.log` 为 **4252 jobs** 成功，80 bytes，SHA256 `ffc57f550784f0440bbc0c677e466b4cd2e12ece927a8ac6bcc7c76138048e0c`；`/tmp/carleman-t224-axioms.log` 为 0 bytes。
- 固定 raw `/tmp/carleman-t224-coefficient-operator-local-axioms.txt`：**3157418 bytes**，SHA256 `26c1799a25bad8a13f722b049837a3ec78b3337088d690cef05679cd8492a682`。15 项完整类型已逐项检查；扫描全部 **3682 个显式公理记录**，仅正常 `propext`、`Classical.choice`、`Quot.sound` 或无公理，无 sorryAx 或新增数学公理。原全命名空间 `privateToUserName`/`collectAxioms` 递归白名单循环与基线不变，末行确认 **9432 声明递归审计 PASS**。两模块根导入与 15 项 #check/#print axioms 齐全。
- Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定配置/证据一致。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。

本报告接受实际一般弱系数微分表达式与原关联算子的身份，保持 AUXILIARY / 17 of 26。正文及 reviewed_at 签发后冻结；仅单文件提交本报告，不改数学、台账、根导入或原稿，不 push。
