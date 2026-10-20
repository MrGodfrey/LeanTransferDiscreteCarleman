# T226 / C242 独立本机验收

- checked_sha: `4728609fbece53cc6afcc9013b94592eb23ee87d`
- mathematical_base: `f616d5d02bde9bd06cc719a33a727b40c5d44675`
- reviewed_at: `2026-10-20T06:13:04+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- declaration_result: **PASS，7/7 定理；实际陈述及证明未发现错误。**
- paper_result: **NOT COMPLETE；不接受完整 P022 / Proposition A.1 的 PAPER 升级。**
- accepted_scope: **AUXILIARY，原完整形式/正自伴关联图和全允许族 A2/A3；原文覆盖保持 17/26。**

已完整读取三个固定新模块、七项 raw 完整类型、公理记录、固定分析/MATH_SPEC/台账及原稿 `paper/main.tex:333–376,2615–2654`。C242 当前台账以 PAPER 为目标；本报告只对七定理的实际范围给 PASS，不能直接据此将该 PAPER 目标或 P022 标为完整 REVIEWED。

## 阻止完整 P022 升级的缺项

**F1：原 A1 末句的平方根域与形式身份尚无形式化桥。** 原稿 **353 行** 明确断言 `D(A^{1/2})=V` 和 `‖A^{1/2}v‖₂²=a(v,v)`。固定 `HigherAnalyticData.lean:32–46` 返回域等式、稠密域、闭图、非负性、完整伴随图等价、图范数界及 AllowedFamily；没有返回同一 A 的平方根、平方根域或上述范数身份。已读实际关联算子定义及此次依赖，并检索固定项目中的平方根相关接口：实际证明仍止于闭形式和正自伴关联图，未找到被本结论调用的平方根表示定理。

这不是 `operator_adjoint_graph_iff` 仅证明对称性的问题：该定理确实证明完整无界自伴图。通常数学中，对稠密闭非负形式及其关联正自伴算子，第二表示定理推出 `D(A^{1/2})=V` 和 `a(u,v)=⟨A^{1/2}u,A^{1/2}v⟩`，故当前接口包含推出原句所需的正确数据；但这一步尚未在本项目形成经过 Lean 核验的结论或等价接口。仅口头援引这个定理，或把 `sqrt(a(v,v))` 命名为平方根范数，都不能证明同一原 H 上算子的平方根及其域。由于目标是保留原文全部明确结论的形式化验收，当前闭形式接口尚不足以认证完整 P022。

可清偿的具体工作是：对同一关联 A 构造并识别原 H 上的正自伴平方根 B，证明 B²=A（包括组合域），D(B)=原 V，以及 `‖Bv‖₂²=a(v,v)`；或者建立并调用等价的形式化第二表示定理。无需为此额外要求有限维、光滑状态或谱截断。完成后再把这条身份接入总实现并复核 P022。现有七项无需撤销，其 AUXILIARY 范围可接受；若先登记其验收，应将 C242 的已验范围如实限定，不能照当前“完整原 A1–A3”标题和 PAPER 范围直接销项。

## 七项实际数学核对

1. **真实完整自伴性。** `FormSelfAdjoint.operator_adjoint_graph_iff` 对所有 y,f∈H，将全部原域测试的 ⟨Av,y⟩=⟨v,f⟩ 与 `(y,f)∈graph(A)` 等价。证明用已构造的真实 `(A+1)⁻¹`：先令 z 解 Az+z=f+y，再由原对称性得到 ⟨Av+v,y−z⟩=0；取 v=(A+1)⁻¹(y−z)，得到 ‖y−z‖²=0，再恢复 Az=f。反向由实际域对称性。`FormSolve` 中 resolvent 来自原 coercive form 的 Lax–Milgram 解及完整变分域，并非输入满射或自伴性。在最终 H=L²(S) 的 Hilbert 实例，原 domain_dense 保证这是通常无界伴随的完整图等式；没有有限维、特征向量、额外自伴假设或有界逆偷换。
2. **同一原 H₀ᵐ、原形式与 canonical jet。** `higherCoefficient_valueEquiv_jet` 用全弱射流的零阶值注入性，识别原能量实现的成员与其 canonical jet，而非另选状态；`scalarForm_canonical` 随后精确恢复完整 coefficientJetForm。原 `HigherDirichletEnergy` 是真实 H₀ᵐ 在完整 Hᵐ 平方和范数中的 Hilbert 实现，闭性在 Hᵐ、稠密性在 H=L²。`MultiDerivativeIndex` 包含全部 k≤m/Sym 多指标，所有 αβ、低阶、非对角系数的实际积分均保留。`BoundedWeakCoefficient S (2*m)` 仅包含有限真实有界分布导数链，没有光滑系数、域外延拓或预设经典导数。原对称性和 coercivity 明示保留；有界形式由有限真实乘子/分量 CLM 构造。
3. **原平方权下界。** `higherCoefficient_allowed_form_lower_uniform` 将 T221 对实际能量成员的已证下界移到原值域接口：用 valueEquiv.symm 取同一 v 和 z，z 是两次 conformingWeight 的实际 σ²v；零阶身份足以由弱唯一性识别全 jet。`conformingWeightedNorm` 是原 N 的真实平方和开方，质量项为 `(q^m‖σv‖₂)²`，没有替代导数范数或错误指数。helper 的 hp 是权保持证明参数且量化于所有此证明；总 data 定理内部以真实光滑乘法提供 hp，不把保持性或目标下界当作新增最终前提。
4. **正权、逆权及同一算子域保持。** 所有允许 σ=`q^τ exp(qηρ)`，其逆 ξ=`q^(−τ)exp(q(−η)ρ)`，η∈{±1}。SmoothOnClosure 经原有界域紧闭包提供域内 BoundedSmoothOn，不要求域外光滑延拓。已直接核对 T225 的域保持：对任意原 D(A) 状态，原 domain_le 与 hD 分别给 H₀ᵐ、H^{2m}，真实乘法保持两者，再由 T224 已证域等式回到同一原域。`higherCoefficient_allowed_data_uniform` 对 σ、ξ 均内部使用此构造，V 的正权保持亦内部供应。单 data 只列 V 的正权字段，但完整族对反符号和 −τ 同样成立，`AllowedFamily.inverse` 因而给原逆权对 V 的保持；这项没有被遗漏或另加假设。
5. **真实交换子与严格低阶项。** 展开 AllowedWeightData 和 `conjugatedCommutator` 后，左侧正是 `[A,σ]ξz`。实际 L² 互逆乘法在原域内消去 σξ，得到 Az−σA(ξz)；随后分别用 T224 canonical 公式识别 z 和 ξz 的同一原算子值，再直接应用 T225 的完整系数界。所需 u.value=σv.value 由真实 map_inverse 内部给出。右侧 `lowerParameterNorm` 精确为 Σ_{j<2m}q^(2m−j)‖D^jz‖₂，字段属于同一个原 z；没有 2m 阶余项、遗漏系数或对偶方向错误。T225 常数只依固定系数有限导数界、维数/阶数与原 profile，不依赖权绝对 sup、状态或数值空间。
6. **完整 A3 上界与全族量词。** `higherCoefficient_allowed_family_uniform` 取 C=max(C_lower,B)，B=Σαβ bound(aαβ)。放大负质量项使原下界保持；上界通过同一 canonical 形式与真实互逆权 L² 配对、T218 全系数 Cauchy–Schwarz 界以及 B≤C 得到，非负 N 因子方向正确。已展开 AllowedFamily 的 data/upper 全部字段：覆盖全部状态、全部时刻、两个 profile 符号及原 |τ|≤τStar。c,C,Ccomm 在 hD 见证、TimeWeight、τ、η、状态之前选择，family 中也先于 τStar；事实上统一于全部实 τ。TimeWeight 包含任意原区间 q 的夹断实现，空间论证只用 q(t)≥1，不额外索取时间导数；因此原任意 T>0 与 C² 允许 q 全被覆盖，常数不依赖 T/qmax。没有扩大或缩小原可用权族所需的结论。
7. **总实现与明确保留的原假设。** `higherCoefficient_analytic_realization` 接受原有界 Lipschitz 域、实际完整弱系数、原对称/coercivity、一向 hD:D(A)⊆H^{2m} 和原完整 Sobolev Hilbert 图估计；有限体积由有界性内部构造，profile 由任意原 SmoothOnClosure 函数 r 内部构造且 value=r。返回原 D(A)=H₀ᵐ∩H^{2m}、稠密域、闭图、非负与完整自伴图及全族 A2/A3。原 full Hilbert H^{2m} 图界是输入 hgraph；输出的既有 jet 范数界通过 `SobolevHilbert.toJet_norm_le` 得到，不把较小 jet 积范数伪称为原 Hilbert 范数。原完整图界仍是保留的 Proposition A.1 假设，不是本批证明的一般正则性。m=0、空域、零系数界等广义边界情形无非法除数，原 d,m≥1 为结论子范围。除 F1 的论文覆盖缺项外，未发现数学或量词错误。

## 全部声明及定位

源码位置相对于固定 `Carleman/`，raw 行相对于下列固定本机审计文件。

| 源码位置 | 声明 | raw 行 | 结论 |
|---|---|---:|---|
| Continuous/FormSelfAdjoint:13 | `Carleman.CoerciveForm.operator_adjoint_graph_iff` | 41298 | PASS；原无界算子完整伴随图等价。 |
| Spatial/HigherAllowedData:15 | `Carleman.higherCoefficient_valueEquiv_jet` | 41303 | PASS；原能量实现与 canonical 全弱 jet 身份。 |
| Spatial/HigherAllowedData:27 | `Carleman.higherCoefficient_scalarForm_canonical` | 41315 | PASS；同一原完整系数形式。 |
| Spatial/HigherAllowedData:42 | `Carleman.higherCoefficient_allowed_form_lower_uniform` | 41327 | PASS；原 σ² 测试及 N²/质量余项的统一下界。 |
| Spatial/HigherAllowedData:84 | `Carleman.higherCoefficient_allowed_data_uniform` | 41349 | PASS；内部供应保持性、逆权和同一 A 的交换子。 |
| Spatial/HigherAllowedData:142 | `Carleman.higherCoefficient_allowed_family_uniform` | 41372 | PASS；同一正常数覆盖完整双符号上下界族。 |
| Spatial/HigherAnalyticData:18 | `Carleman.higherCoefficient_analytic_realization` | 41395 | PASS 于实际返回类型；没有返回原 A1:353 平方根结论，故不能认证完整 P022。 |

## 依赖与固定本地证据

T225 冻结报告 `29169226b6046ca19fe2c259134f09f8eb883a35` 已全文读取（checked_sha 为本批基线，reviewed_at=`2026-10-20T06:07:01+00:00`，11/11 PASS）。实际关键调用仍直接检查：全系数交换子、原图/域构造、真实允许权/逆权和形式下界、AllowedWeightData/AllowedFamily 全字段、原 N 范数及低阶和、原 resolvent 与图等价。三个新模块导入闭包 **304 文件**，其中 **301 个旧模块与数学基线逐 Git blob 不变**；未混入未来工作树或动态公理产物。

- `/tmp/carleman-t226-local-evidence.json`：source=local、PASS，checked/source 都精确为本报告 proof，finished_at=`2026-10-20T06:09:23.821388+00:00`。实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0。本次读取原执行记录并核对固定源码，不声称重新执行全库，也未查询远端 CI/看板。
- 独立枚举固定提交所有 tracked Lean 文件及三项构建配置，与 `/tmp/carleman-t226-local-source-manifest.txt` 核对完整性、唯一性及逐 Git blob 字节摘要：**1020 项全部相同**，110658 bytes，SHA256 `b6205e152fbe645d8ca5ed6b4436c8b89c1289982593903c7b0bd0da8681eb55`。
- 实际 `/tmp/carleman-t226-target-build.log`：**3510 jobs** 成功，235 bytes，SHA256 `66c2e686007fb4bf1a692669a8ed344a5d4d17f5a607266b88c8beb6891efad0`；`/tmp/carleman-t226-build.log`：**4256 jobs** 成功，80 bytes，SHA256 `75f4ef993900e369cbdff7be8725d3e99a14e4121e15e46bb60101a1b06f73ec`；`/tmp/carleman-t226-axioms.log` 为 0 bytes。
- 固定 raw `/tmp/carleman-t226-higher-analytic-local-axioms.txt`：**3177824 bytes**，SHA256 `25a5b41285828a10165aa50b8437e1403559d307e86c0d9dd70b717a39fe4cc8`。七项完整展开类型逐项检查；扫描全部 **3700 个显式公理记录**，仅正常 `propext`、`Classical.choice`、`Quot.sound` 或无公理，无 sorryAx 或额外数学公理。原全命名空间 `privateToUserName` / `collectAxioms` 递归白名单循环未变，末行确认 **9453 声明递归审计 PASS**。三个根导入与七项 #check/#print axioms 齐全。
- Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定配置及证据一致。原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef` 未变。

验收结论为 **七项实际定理 PASS / 完整 P022 尚未完成**；F1 清偿前保持 AUXILIARY / 17 of 26。正文与 reviewed_at 签发后冻结，仅单文件提交本报告，不改数学、台账、根导入或原稿，不 push。
