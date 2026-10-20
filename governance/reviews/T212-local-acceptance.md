# T212 / C228 独立本机验收

- checked_sha: `9a2857abc4c61b3c6de1fa2d282bac81f14a3d16`
- base_commit: `a98192d2b1dc2e5f7d7034d4a5be49d41c7b3bec`
- reviewed_at: `2026-10-20T04:39:00+00:00`
- reviewer: independent local Agent `/root/accept_spatial_foundations`
- result: **PASS — 7/7 定理，无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，P021 不提升；未声称唯一性**
- evidence_source: **local**；按简化协议核对实际本地构建、公理和固定源清单，不查询远端 CI。

直接读取固定 Git 对象的四模块全部证明与七项完整 raw 类型、分析/MATH_SPEC/台账，对照原稿 `paper/main.tex:2338–2415` 中原能量解、弱时间方程和连续迹。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。这里新增逐时能量恒等式是原能量法的基础；不能仅凭它把整条控制收敛或唯一性标为完成。

## 七项声明

源码位于固定 SHA 的 `Carleman/Control/`；声明省略公共前缀 `Carleman.`。raw 行号指 `/tmp/carleman-t212-pivot-energy-local-axioms.txt` 中完整类型。

| 模块:行 | 实际声明 | raw 行 | 结论 |
| --- | --- | --- | --- |
| PivotIntervalEnergy:15 | `HasWeakTimeDerivative.pivot_energy_identity_to` | 39702 | **PASS**：实际 V 连续弱 H¹ 轨迹在每个 t∈[0,T] 的质量能量等式。 |
| PivotIntervalEnergy:46 | `time_restrict_inner_integral` | 39713 | **PASS**：真实部分区间限制后的 L² 内积等于原区间积分。 |
| PivotPathConvergence:14 | `pivot_path_limit_strong` | 39720 | **PASS**：给定两项实际强 L² 极限，得到完整 C([0,T];H) 范数收敛并识别同一原 Bochner 像。 |
| PivotWeakEnergyIdentity:15 | `exists_pivot_time_energy_representative` | 39733 | **PASS**：仅由原 L² 状态/载荷及弱 (E*EY)'=D，内部构造连续代表和所有 t 的能量式。 |
| PivotWeakEnergyIdentity:71 | `pivot_time_energy_identity` | 39745 | **PASS**：同一结论适用于任意实际连续代表，保留同一 Y/D。 |
| DirichletTimeEnergyIdentity:16 | `FiniteDirichletControlIdentity.energy_identity` | 39759 | **PASS**：原有限弱身份内部给质量弱导数，接同一 b/Y/U 的真实载荷。 |
| DirichletTimeEnergyIdentity:40 | `FiniteDirichletControlIdentity.continuous_H_energy_trace` | 39778 | **PASS**：同一 q 同时保留原 a.e. 身份、q(0)=y0、q(T)=0 及全部时刻的能量式。 |

## 数学核对

**实际近似轨迹的部分区间公式。** 第一项明确以连续 V 值弱 H¹ 轨迹作为辅助输入。已直接重读旧 `absolutelyContinuous`/`ae_hasDerivAt`：它们从真实弱导数和 Bochner FTC 得绝对连续及 a.e. 强导数。新证明将实际 CLM E 复合到轨迹，以范数平方的真实导数及伴随身份得到 `2〈u,E*E du〉`，再把绝对连续限制到 `[0,t]` 并应用 FTC。因此系数 2、端点差 `‖Eu(t)‖²−‖Eu(0)‖²` 及符号均正确，没有把目标链式法则列为假设。

`time_restrict_inner_integral` 使用真实 `restrictRegionCLM (Ioc 0 t)` 和其 a.e. 代表身份。`g.timeMeasure=volume.restrict (Ioo 0 T)` 到 Ioc 的转换仅用 Lebesgue 端点零测，再由 `0≤t≤T` 识别二次限制的测度；部分积分不是全区间积分的替身。L²–L² 配对本身给可积性。t=0 的零区间与 t=T 的右端点均包含，没有在任意 Lp 代表上规定端点值。

**完整路径强收敛。** `TracePath` 实际是 `C(Icc 0 T,H)`，所用范数为整个紧区间上的一致范数。对任意 n,m，把真实质量迹界作用于 `u_n−u_m`，逐一识别其 L² 状态差、E 像与质量导数差，得到
`‖Eu_n−Eu_m‖∞ ≤ sqrt(‖E(U_n−U_m)‖²/T + 2‖U_n−U_m‖‖Z_n−Z_m‖)`。
两项强 L² 收敛在 `ℕ×ℕ` 上给两索引差趋零，进而给一致 Cauchy；真实 C([0,T];H) 完备性产生 p。`pathL2` 的连续性与实际 a.e. 身份把 p 的 L² 类识别为 E Y，未误用 MY 连续替代 EY 连续。

已与接受的 T204 `pivot_path_limit` 逐段比较：新定理只在结论增加原路径 `P` 的 `Tendsto P ... p`，并返回原证明已经获得的 hq；实际 Cauchy 估计、完备性和 pathL2 识别没有改变。原源码也未修改。辅助路径定理不要求 E 注入；它的连续弱 H¹ 前提仅用于近似轨迹，并未套到原 Y 上。T⁻¹ 显式且 T>0 由 TimeGrid 保证，不宣称此估计对 T 统一。

**仅由原质量弱导数构造能量代表。** 主存在定理输入真实实 Hilbert 空间、bounded injective E、原 Y/D∈L² 和 `(E*E Y)'=D`。E 注入通过 `ker(E*E)=ker E`、自伴性与正交补内部推出质量值域稠密；不要求 E 满射、在 H 中稠密、有限维或逆有界。实际 ε_n=1/(n+1) 正质量正则化内部供应连续弱 H¹ 轨迹 u_n、du_n，且 `U_n→Y`、`Z_n=E*E du_n→D` 强 L²。这里采用实际质量正则化与其 a.e. 身份，不是任意近似序列见证或另一个载荷。

先获得一个 p/q，再对所有 t 论证：连续点值算子把完整路径收敛传到同一个 t 和 0；真实时间限制 CLM 把 U_n/Z_n 的强收敛传到 `(0,t]`，内积连续性给 `〈R_t U_n,R_t Z_n〉→〈R_tY,R_tD〉`。每个 n 的真实能量公式与此极限相接，得到同一 q 对全部 t 的等式。没有只取几乎处处时间、没有随 t 另选子列或代表，也没有正则化逆范数进入最终公式。原 Y 仅为 L² 类，不要求 Y∈H¹(0,T;V) 或具有原 V 连续代表。

`pivot_time_energy_identity` 通过真实连续代表唯一性将存在构造转到任意给定连续 q。唯一性使用正时间区间上的 Lebesgue 满支撑及闭区间连续性，把 a.e. 相等提升为整个 `[0,T]` 相等；不是利用端点零测直接指定其值。μ 参数明确满足 `g.timeMeasure=μ`，不把该结论推广到任意时间测度。

**原 Dirichlet 状态及载荷。** 最后两项取 E 为实际 H¹₀ 值嵌入，其注入由真实弱导数唯一性供应；D 恰为同一 b/Y/U 的 `dirichletTimeLoad`。该 D 是实际 Bochner 伴随构造 `E*U−G*GY−E*J*(b·JEY)`，原 `mass_weak_time_derivative` 已由全部有限弱身份内部推出。证明不输入目标能量关系，也不把 D 换成任意新函数。已重读此载荷定义与原配对公式，势号和刚度号保持原 U−Ay−by。

`energy_identity` 接任意实际 H 连续代表；`continuous_H_energy_trace` 则内部调用已有真实连续迹/初终值定理，返回同一个 q 的 a.e. 身份、q(0)=y0、q(T)=0 及 `‖q(t)‖²−‖y0‖²=2∫₀ᵗ〈Y,D〉`。后者只输入 `FiniteDirichletControlIdentity` 和原开域、有限测度、T>0；未新增盒域、H² 正则性或正维要求。这里的 RHS 保留实际 V 内积载荷表达；本批未完成局部载荷能量界与零数据论证，未声称解唯一性。

## 固定证据与不变依赖

`/tmp/carleman-t212-local-evidence.json` 的 checked/source SHA 均为本报告 proof，source=local、status=PASS，finished_at=`2026-10-20T04:36:18.706361+00:00`；实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0。已读取四模块定向 `target-build.log` **3634 jobs** 成功及全库 `build.log` **4227 jobs** 成功，`axioms.log` 为 0 bytes。审核核查实际执行记录与固定源关联，不声称另行重建旧闭包。

独立枚举并核对 `/tmp/carleman-t212-local-source-manifest.txt` **992** 个 tracked Lean/构建配置项，集合完整无重复，每项与固定 Git blob 的 SHA256 一致。清单 107589 bytes，SHA256=`322f962b0d226a7f92d62a63c2cc6cb13a481a36b128b2499903aacc4a319a56`，与 evidence 绑定匹配。新模块递归 Carleman 闭包 **432** 文件，其中 **428** 个旧文件与基线逐字节不变，四新模块全读。

另直接比对六个关键旧源：PivotTimeTrace 与已接受 T202、MassRegularizedPaths 与 T203、PivotTimeContinuity 与 T204、DirichletTimeEndpoints 与 T205，以及 DirichletTimeLoad/DirichletMassWeakDerivative 与 T200，均逐字节不变；重读实际近似构造、弱 FTC、路径定义、代表唯一性及载荷接口，不重复无关历史审查。

固定 raw **3059710 bytes**，SHA256=`3f858ab89b94eb23a812597328bd126e1b3ead73bb2d7bd87e884b4aa3e9d649`。七项完整类型和各公理记录已核对，root 实际导入四模块，七项 `#check`/`#print axioms` 齐全；审计循环经 `privateToUserName` 遍历命名空间并递归 `collectAxioms`。raw 全部 **3541** 条显式记录（3537 个唯一声明，9 条无公理）均仅含 `propext`、`Classical.choice`、`Quot.sound` 或无公理，末行 **9016** 项全命名空间递归审计 PASS，无 sorryAx 或白名单外项。Lean v4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 与 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 均与固定配置一致。

本报告在上述 reviewed_at 冻结，仅单独提交报告；不修改数学、台账、原稿或覆盖统计，不 push。
