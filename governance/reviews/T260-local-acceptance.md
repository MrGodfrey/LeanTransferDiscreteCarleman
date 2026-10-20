# T260 / C276 — 完整 Corollary A.2 独立论文级验收

- checked_sha: `cbd25fdee3e670d39fce5a03cbf172c02a890544`
- mathematical_base: `0a4c425a254d6bc108651a078b6c0adbcc02b9f5`
- reviewed_at: `2026-10-20T10:59:42+00:00`
- reviewer: 独立本机验收 Agent `/root/accept_section3`
- result: **PAPER PASS；完整 P023 / Corollary A.2；4/4 显式声明通过，无待修复缺陷。**
- axiom_check: **PASS**；evidence_source: **local**。

## 原文与最终判定

读取固定版本的治理协议、T260 analysis、MATH_SPEC 对应段、C276/T260 清单、新模块全部定义和证明、原始展开类型及 Data 完整 body。直接对照 `paper/main.tex:2659–2665` 的 Corollary A.2，以及 `286–372` 的原域、权族、范数和 A1–A3。原结论是：固定有界凸多面体（d=2,3）或任意固定正维数盒上的原 Dirichlet Laplacian，取 m=1、完整 H¹₀ 和真实梯度形式，满足全部空间解析假设。

本批两个具体终点确实清偿正则性输入，再与同一原形式的平方根、原算子完整图及全部允许权组装。不是仅接受一个带 H² 假设的泛型包装。**C276/P023 可以登记 REVIEWED / PAPER；完整原文覆盖可由主执行者更新至 19/26。** 本报告自身不修改台账。A4、Proposition A.3 / P024、连续 CE 及其他尚未完成结果不因本次验收而提升。

## 全部四项声明

源码为固定 `Carleman/Spatial/DirichletAnalyticRealization.lean`。raw 行为固定 `/tmp/carleman-t260-dirichlet-analytic-realization-local-axioms.txt` 中类型起点；Data 的完整定义 body 另从 44863 行开始。

| 源码 / raw 行 | 完整声明 | 独立结论 |
| --- | --- | --- |
| 16 / 44892 | `Carleman.DirichletSpatialAnalyticData` | PASS；显式定义完整结果命题，逐字段均指向同一 `boundedDirichletOriginalForm`。hD 是 canonical jet 的域资格参数，不是隐藏的解析公理。 |
| 36 / 44899 | `Carleman.dirichlet_spatial_analytic_of_regularity` | PASS；泛型 helper 明示 hD/hgraph，内部供应真实平方根、精确域的反向包含、稠密/闭图/非负/完整自伴、同值 profile 和全允许权。该 helper 单独不声称已证明任意有界开域的 H² 正则性。 |
| 52 / 44912 | `Carleman.finite_halfspace_analytic_realization` | PASS；具体任意非空有界有限严格半空间交，内部调用实际 T259 域包含与图估计，最终类型没有正则性、穷竭、内解或目标估计输入。覆盖原 d=2,3 凸多面体。 |
| 62 / 44917 | `Carleman.box_full_spatial_analytic_realization` | PASS；任意正维数、任意正边长和平移的坐标盒，内部调用实际盒正则性和 canonical 图估计，最终没有 hD/hgraph 输入。 |

四项均有固定审计登记、实际展开类型和递归公理输出，所依赖公理均为 `propext`、`Classical.choice`、`Quot.sound`。

## 同一原 V、形式、算子及 A1

**完整 H¹₀ 与真实梯度形式。** 直接读取 `DirichletSpace`、`DirichletForm`、`DirichletScalarForm`。`dirichletJetSpace` 是全部真实紧支光滑 `SpatialTest` 的线性空间在完整弱 H¹ 图拓扑中的闭包，其标量值实现为 `dirichletSubspace`。开域弱导数唯一性保证任意同值 jet 的成员资格一致；闭合与 L² 稠密性都有实际证明，没有用逐点边界条件、有限维子空间或算子 core 代替原 V。

`dirichletGradient` 是实际一阶 L² Euclidean 字段；`dirichletForm` 是其真实内积，`dirichletForm_integral` 给原梯度积分，未添加零阶质量项。`dirichletEnergy_norm_sq` 精确给 H¹ 能量范数平方等于值与梯度的 L² 平方和。形式的连续双线性有界性和对称性由该构造得到；原 Poincaré 控制值，内部从有界性选择 slab 半径和正维坐标，证明严格正强制性。因此最终没有外给 coercivity 或形式有界性要求。`scalarForm` 经真实 `valueEquiv` 回到原 V，`dirichlet_scalarForm_canonical` 与完整 canonical 弱梯度配对精确相等。

**实际 Dirichlet Laplacian 与精确域。** 直接读取 `DirichletDistribution`、`DirichletLaplacian`。`dirichlet_operator_graph_iff` 在全部原 H¹₀ 状态上把同一 associated operator 图等价为实际弱负 Laplacian 方程；从全部紧支光滑测试到全 H¹₀ 的配对延拓依靠真实闭包和连续性。反向 `h2_dirichlet_le_domain` 对任意 H²∩H¹₀ 使用完整 Green 身份构造真正原域成员，算子值就是 `negativeLaplacian`。新 helper 用此反向包含与具体 hD、原 `domain_le` 得到精确子空间等式，没有把域重新定义成 H²。

同一 `CoerciveForm` 内部给原算子域稠密、图闭、非负和完整自伴图。已读 `FormSelfAdjoint.operator_adjoint_graph_iff`：对全部域状态的伴随配对通过实际 `(A+I)` resolvent 得到原图成员，反向由原对称性；不是只验证形式对称。Data 的伴随图量化全部环境空间 y,g。

**完整平方根。** 此处实际调用已独立验收且整个依赖闭包未变的 `OriginalForm.exists_squareRootData`。其类型是 `Ahalf : a.V →ₗ[ℝ] L²`，域恰为同一完整 H¹₀；非负性、对全 V 的完整伴随图、对全部 x,f 的双向平方组合图以及全 V 上 `‖Ahalf v‖²=a.scalarForm v v` 一并返回。组合图显式要求中间值仍属于 V，右边是同一 `a.model.operator` 的完整图，故含完整 `D(Ahalf²)=D(A)`，没有只在原 A 的 core 上核查等式。T229 的 F1 修复在这里被真正应用，未以另一个形式、另一个空间或预设根替代。

**完整 H² 图范数及 canonical 身份。** 两个具体图估计都对任意原域 z，先提取同值 H¹₀ 弱解，使用实际正则性得到同一弱解的二阶 lift，再由值唯一性证明它完全等于 `domainSobolevJet ... z`。因此控制全部 0、1、2 阶真实 L² 字段，不是只控制 Hessian 半范数、值范数或不相关解。

准确区分范数：Data 中 `‖domainSobolevJet ... z‖` 是三个 L² 字段的完整有限乘积范数，不逐字等同于平方和 Hilbert 范数。已读 `SobolevTopology.norm_field_le`、`sum_fields_le`、`SobolevHilbert.ofJet`、`jetEquiv` 和 `norm_sq`。它们给

```text
‖ofJet J‖² = ‖field₀ J‖² + ‖field₁ J‖² + ‖field₂ J‖² ≤ 3 ‖J‖².
```

故 Data 的图界给原完整 H² Hilbert 范数图界，至多将 Creg 放大为 `sqrt(3) Creg`；这只涉及固定三个阶数，不引入状态、时间、权或域间统一性假设。所有字段均为实际弱导数，不能将此解释为任意有限维范数替代原 Sobolev 范数。

## 两种具体几何如何清偿正则性

**有限半空间交。** 已阅读全文实际 `FiniteHalfspaceRegularity` 的九项证明和 T259 冻结报告。输入 `S={x | ∀ i, b i<ℓ i x}`，ι 有限、ℓᵢ 为连续线性泛函、S 有界、存在实际严格内点 c、d>0。这是非空满维有界凸多面体域的通常半空间表示；允许任意斜面、冗余约束与角点，不要求法向独立、直角或光滑边界。非空内点没有缩小原域问题。实际结论覆盖所有正维数，特别包括原 d=2,3；不声称原命题要求了零维或退化空域。

具体调用 `finite_halfspace_dirichlet_domain_le_h2` 与 `finite_halfspace_dirichlet_graph_estimate` 的完整类型没有外给正则性。其实际证明内部选择包含同一 c 的平滑指数和内域尾序列，证明单调、包含并覆盖完整 S；每层原 coercive Dirichlet 解、同一限制载荷、真实 H² lift 和统一 Hessian 界均由既有证明供应。极限只作合法 H¹₀ 零延拓，不假设 H² 零延拓；完整原测试上的弱极限给实际 H² 解。原弱解唯一性再识别为给定任意原状态。令 `N_d=card(Sym(Fin d,2))`，所得二阶界为 `N_d‖f‖`，并未冒称最优常数 1；slab Poincaré 和原弱方程给零、一阶界，从而先于全部 u,f 选择 `K=(2R)²+2R+N_d`。canonical 图常数为 `max(1,K)>0`。

本批确切调用这些已经证明的具体定理来填入 helper 的 hD/hgraph，而不是把它们作为最终使用者要补的参数。新定理与 T259 之间没有循环正则性依赖；T259 的目标此前只是辅助正则性，本批再补全整个 A1–A3，才接受完整 P023。

**盒域。** 直接读取 `BoxAnalyticData`、`BoxDirichletRegularity` 和 `BoxPoissonRegularity` 及既有冻结报告。实际有限个上下坐标面奇延拓把原闭盒严格置于固定扩大开盒内部；完整 H¹ 状态限制恢复，原内部正则性给同一二阶 lift，弱右端唯一性恢复同一 f。原 Poincaré 与弱方程消去值/梯度，得到只依赖固定盒和维数的完整 H² 右端界；canonical jet 再由弱唯一性识别。正边长与 d>0 保留任意平移、一维及更高维的原盒情形，没有边界光滑、原状态光滑、预设 H²、载荷兼容性或目标图估计要求。

## 全允许权、A2/A3 与统一量词

直接读取 `DirichletAllowedData`、`DirichletAllowedForm`、`DirichletCommutator`、`DirichletCommutatorIdentity`、`DirichletDomainOrders` 的实际实现，并使用版本不变的原 `AllowedFamily` 接口。

对给定任意 `SmoothOnClosure r S`，内部构造真正 `SpatialProfile ρ` 且 `ρ.value=r`。有界域紧闭包给所需有限导数界；无需外部光滑延拓或额外有界代表假设。原负 profile 是这个更一般结论的特例。最终先固定域与 r，先选择 `Creg>0`、`C≥1`、`Ccomm>0`，随后才量化全部 TimeWeight、τStar；族内再量化双符号、`|τ|≤τStar`、全部时刻和全部原 V/D(A) 状态。常数独立于 T、q/qmax、τ、时刻、状态；可以依赖固定几何和空间权导数。时间标量 `q^τ` 不产生空间导数，因此在 τStar 前选择常数合法。

- **A2 域保持与逆权。** 真实弱乘法和完整原 Dirichlet 算子图给 σ 对 V、D(A) 的保持；相反空间符号与 `−τ` 给真正 `q^(−τ)exp(∓qρ)`。族的 inverse 操作也给逆权 V 保持，不遗漏原 A2 的四种保持性。
- **A2 交换子。** 实际原算子的乘积公式给负 Laplacian 修正项；共轭交换子是该修正项的负值。输入 `u=σ⁻¹z`，实际 σξ=1 和弱乘法法则将界转为 `Ccomm(q²‖z‖+q‖∇z‖)`。`dirichlet_domain_lower_sum` 将 canonical H² 截断识别为真实原 H¹ jet，严格等于 m=1 原 `j=0,1` 的低阶和，没有漏梯度或用 H² 主阶替代。
- **A3 上界。** 同一真实原梯度配对中 σ 与 σ⁻¹ 精确抵消，Cauchy–Schwarz 给原双权 N 范数上界。C≥1 的放大方向正确，两个输入量化全部 V。
- **A3 下界。** 同一个 σ 连续作用两次给真实 σ² 测试；弱乘积与 Young 不等式给 `(1/2)Nσ(v)²−C0‖qσv‖²`。取 `C=max(1,C0)` 使负余项增大，降低左端，方向正确。所有乘权测试资格内部提供，没有假设目标强制估计。

原任意 T>0 和原 C² 周期 q 类都在空间结论的适用范围内；这里仅使用空间估计需要的 q≥1，因此没有增加时间光滑或周期限制。没有观测、CE、网格、频率过滤、有限维状态或数值估计前提。

## 固定依赖及源码边界

新模块的 Carleman 导入闭包为 **449 模块**，其中 **448 个旧模块与 mathematical_base 逐 Git blob 完全相同**。仅新数学模块及 root/audit 登记变化；其他变化为治理、原有验收报告和状态记录。另独立比对以下关键完整闭包，全部与已验收 proof 相同：

| 比较根 | 已验收 proof | 模块数 |
| --- | --- | --- |
| `Spatial/FiniteHalfspaceRegularity` | `0a4c425a254d6bc108651a078b6c0adbcc02b9f5` | 313 |
| `Section3/OriginalSquareRoot` | `d1dabe5404212ce3dd399028a79233e3da4e324b` | 47 |
| `Spatial/BoxAnalyticData` | `90ca06c7cd42fae4b870fae9a67219fa729226f7` | 362 |
| `Spatial/BoxDirichletRegularity` | `b818f314b275265490aa9b797779f7db0005ddb9` | 224 |
| `Weights/DirichletAllowedData` | `d65579460032f15bcba3c77709ccfd3f1642b8fc` | 227 |

T259 冻结报告 commit `8693fe2b3f59764bf3544d6c81abba6a3d29bcd1` 已完整读取，时间 `2026-10-20T10:49:20+00:00`，9/9 PASS，已包含于本 proof。T229 自己此前冻结的完整根桥验收为 `7311b6e17169c4248895dd1150990145ffd7985d`；其原 F1 已关闭，未把之前缺项状态沿用到此版本。还读取 T141 报告 `dfab53c2a4b49f043f28a8dfea6fd7c5cad9e125`、T143 报告 `73e1b1b7d6ebf8b8f67901d25329c62a55a865ab`、T071 报告 `605482c31a83563b5c3a027ca3860be543aa3fce` 的相关数学结论，并实际重读上述关键调用。复用已验收且 blob 不变的底层证明，不重复审核无关全库。

## 固定本地证据

- `/tmp/carleman-t260-local-evidence.json`：PASS、source=local、checked/source SHA 均为本报告 proof；`lake build Carleman`、`lake env lean tools/CheckAxioms.lean` 均 exit 0，`finished_at=2026-10-20T10:49:36.651533+00:00`。固定 T260 记录定向/根/审计三个退出状态均为 0。
- `/tmp/carleman-t260-local-source-manifest.txt`：**1057 项，114738 bytes**；SHA256 `a4dd3bc74b44e2ce8c10016e3b526dba6a09a63b06bfb2851e6ce7f92f6ae8fb`。独立核对完整路径集、唯一性及每一项 Git 原始字节哈希，与固定全部 tracked Lean 文件及三个构建配置完全吻合。
- `/tmp/carleman-t260-target-build.log`：**3675 jobs** 实际成功，117 bytes；SHA256 `7498395de8c18db8e503388e17b247c45d900e70f5f4d016ff13db256112b955`。
- `/tmp/carleman-t260-build.log`：**4299 jobs** 实际成功，80 bytes；SHA256 `932e3e78e95715c4f982e90efd842b583858a7c8da247f899060043a0353f9d1`。
- `/tmp/carleman-t260-dirichlet-analytic-realization-local-axioms.txt`：**3459007 bytes**，SHA256 `def0534f4a57840edc30332bb0acbfaa0e5fdae20cd6f81e8d3db35cf209a395`；实际末行 **10318 Carleman 声明递归审计 PASS**。独立解析 4149 个显式依赖列表，全在三个正常基础公理内，另有 10 个无公理记录。Data body 与四项类型/公理均实际存在；审计循环遍历全部 Carleman 声明并递归 `collectAxioms`，未缩小检查范围。
- `axioms.log` 的 0 bytes 只表示 stderr 为空，不充当 PASS 证明。早期 `/tmp` probe 不是固定交付版本；验收依据上述与 Git manifest 绑定的最终构建及 raw，无 `sorryAx` 或新增数学公理。
- 根模块实际导入新模块；固定审计含 Data 的 `#print` 完整 body 和四项 `#check`/`#print axioms`。Lean `4.35.0`，compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin/lock 与实际干净 checkout 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。
- 原稿未改，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。没有使用未来工作树或动态 `.ci`，没有重新构建全库，没有查询看板/远端 CI，也未将本机 PASS 写成远端成功。

**最终接受完整 P023 / Corollary A.2。** 本报告仅对上述固定版本签发；单文件提交后正文与 `reviewed_at` 冻结。未修改数学、台账或其他报告，不 push。
