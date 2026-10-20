# T205 / C221 独立本机验收

- checked_sha: `bfa6e3a8b9af4367eca74101ad0473c42e8bdfa8`
- base_commit: `7afc739b6c8f95e208beeaefed4b955f0eebbdb5`
- reviewed_at: `2026-10-20T03:51:09+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 6/6 显式声明，无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，P021 不提升**
- evidence_source: **local**；不查询或声称远端 CI 成功。

直接读取固定 Git 对象中两个新模块的完整类型与证明、T205 分析、MATH_SPEC 对应段和原稿 `paper/main.tex:2395–2415`。新结论确实从同一原弱控制恒等式恢复 H 连续迹的初终值，符合第 2415 行的用途；原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 六项逐声明核查

| 固定声明 | 源模块 | 结论及核对点 |
| --- | --- | --- |
| `Carleman.HasWeakTimeDerivative.scalar_affine_green` | `Carleman/Control/ScalarTimeEndpoints.lean` | **PASS**。真实标量弱 H¹ 身份先给绝对连续性及 a.e. 导数，再以 t−c 作因子得到 `∫(f+(t−c)df)=(T−c)f(T)+cf(0)`，两端点符号正确。 |
| `Carleman.HasWeakTimeDerivative.scalar_endpoints` | 同上 | **PASS**。c=0 的 Green 式和 `∫f+∫t·df=0` 给 Tf(T)=0；T>0 后得 f(T)=0，再由真实弱 FTC 和 `a+∫df=0` 得 f(0)=a。 |
| `Carleman.FiniteDirichletControlIdentity.continuous_pairing_weak` | `Carleman/Control/DirichletTimeEndpoints.lean` | **PASS**。将原质量弱导数经实际 `innerSL w` 映射，结合 q=EY a.e. 及 E*E 伴随配对，得 `〈q,Ew〉′=〈D,w〉` 的完整标量弱身份。 |
| `Carleman.FiniteDirichletControlIdentity.continuous_pairing_test` | 同上 | **PASS**。原不限端点 C¹ 时间测试经真实 tensor/toLp 身份改写，准确保留 `−∫η′〈q,Ew〉=η(0)〈y₀,Ew〉+∫η〈D,w〉`。 |
| `Carleman.FiniteDirichletControlIdentity.continuous_H_endpoints` | 同上 | **PASS**。对每个完整能量方向 w 使用 η=1、η=t，先恢复连续标量配对的两端点，再以原值嵌入的稠密值域分离 H 向量，得到 q(0)=y₀、q(T)=0。 |
| `Carleman.FiniteDirichletControlIdentity.continuous_H_trace` | 同上 | **PASS**。实际调用 T204 构造同一原 EY 的连续代表 q，并对该 q 证明两端点；一个存在量词同时返回闭区间连续性、原 a.e. 身份及两项端点等式。 |

六项与 manifest、根导入、固定 `#check @...` / `#print axioms` 一一对应；已读取全部展开类型，未只核验编译结果。

## 关键数学、数据及边界

**端点来自真实连续函数的 FTC。** 标量辅助定理输入实际弱导数、f 在 `[0,T]` 上连续及 df∈L²。旧弱 FTC 给 f 绝对连续和实际 `HasDerivAt f (df t)` a.e.；固定 mathlib 的绝对连续乘积分部公式用于 `(t−c)f(t)`。把实际导数替换为 df 只发生在积分的 a.e. 身份中。f、t·df 的可积性分别由闭区间连续性和 L²×L² 供应；绝对连续积分分部的导数积分同样具有实际可积性，未利用未定义积分的默认值。以 c=0 得 `∫f+∫t·df=T f(T)`，合法除以正 T；再用 `∫df=f(T)−f(0)` 识别初值。

**原质量与同一载荷。** 记 `V=DirichletEnergyState S`、`H=L²(S)`、`E=dirichletStateValue S`、`M=E*E`、`D=dirichletTimeLoad T hS b Y U`。实际原质量弱导数映射到方向 w 后，`M.coeFn_compLpL Y` 与 q=EY 的 a.e. 身份给 `〈w,MY〉V=〈q,Ew〉H`；真实伴随公式和实内积对称性处理方向，没有把 V 图内积误当 H 配对。D 始终来自同一个 Y、U、原有界势 b，初值始终是原 y₀。

原测试身份保持所有闭区间 C¹ 时间系数及真实 `HasDerivWithinAt`，不要求 η 在端点为零。η=1、η′=0 得 `0=a+∫df`；η=t、η′=1 得 `−∫f=∫t·df`，其中 `a=〈y₀,Ew〉`、`f(t)=〈q(t),Ew〉`、`df(t)=〈D(t),w〉`。D∈L² 经有界 `innerSL w` 给真实标量 df∈L²；q 的 H 连续性给 f 在整个闭区间连续。由标量端点定理得到所有 w 的 `〈q(0),Ew〉=〈y₀,Ew〉`、`〈q(T),Ew〉=0`。

**稠密性与代表。** `conformingEmbed_range` 将实际 E 的值域识别为原 `dirichletSubspace`；该子空间由原光滑测试闭包构造，其在 H 的稠密性由真实空间测试分离证明。端点代码通过内积连续性在闭等值集合上传递稠密性，扩展到每个 H 方向，再用内积外延性分离向量。这里需要并使用的是 E 在 H 的稠密值域，不是仅 E 单射或 M 在 V 的稠密性；也未要求任意原 y₀ 属于 V。

中间两个 pairing 定理只需 q=EY a.e.，其积分/弱身份不依赖零测集上如何选代表；真正识别端点的定理另有 q 的闭区间连续性，并由最终定理在内部供应。没有从 a.e. 相等直接读取端点，没有为任意 Lp 代表指定端点，也没有另选择一个 q 来满足终值。

最终完整接口保留 T>0、S 开且有限测度、原 b、任意 L² 初值、完整 Y∈L²(0,T;V)、U∈L²(0,T;H) 及既有 `FiniteDirichletControlIdentity`。不增加 H²、经典时间导数、控制预算、端点条件或新网格限制。一步 TimeGrid 仅编码同一正 T；Ioo/Ioc 的测度转换只使用 Lebesgue 端点零测，不施加周期端点匹配。连续迹与端点身份已在这一原弱恒等式接口下完整返回；本批仍未组装实际控制族的最终整体结论或一般 P1 控制分支，因此不提升 P021，也不改变既有统一控制费用。

## 依赖与本地证据

全文读取 T204 冻结报告 `9720d4b27b055716a613d8666a82fdb393f02d8e:governance/reviews/T204-local-acceptance.md`（4/4 PASS，reviewed_at `2026-10-20T03:45:17+00:00`），并逐字节核对该提交与报告文件相同。直接阅读其实际 `PivotTimeContinuity` 和 `DirichletTimeContinuity`：连续路径空间的真实一致 Cauchy 极限经 `pathL2` 连续性与极限唯一性识别同一 EY，最终端点定理调用的正是这个 q。

两个新模块的 Carleman 递归源闭包共 **428** 文件，其中 **426** 个旧文件与基线 Git blob 全部相同。`DirichletTimeContinuity` 的整个 426 模块闭包与 T204 固定证明一致，`DirichletMassWeakDerivative` 的 418 模块闭包与 T200 固定证明 `a081c61839658c2869ef6a01e7bcd387a81b9af4` 一致。重读新证明所用的真实弱 FTC/绝对连续性、L² 张量配对及 Dirichlet 值域稠密性定义；固定 mathlib 的 `AbsolutelyContinuousFun.lean` 积分分部定理已读取并核对本地文件与 pin 逐字节一致。

独立读取 `/tmp/carleman-t205-local-evidence.json`：`source=local`、`status=PASS`，`checked_sha=source_head_sha` 均为本报告 proof SHA，完成时间 `2026-10-20T03:47:47.117199+00:00`。实际记录中 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均 exit 0。本报告核查这些真实执行记录及源码关联，没有声称重新执行全库。

| 固定本地证据 | 独立核验 |
| --- | --- |
| `/tmp/carleman-t205-target-build.log` | 两新模块实际完成，3630 jobs；177 bytes，SHA256 `38c82404766849bbf19e0c3ace3de2692284d002eb3cea6098481bbfdaeb5af3`。 |
| `/tmp/carleman-t205-build.log` | 根目标实际完成，4209 jobs；80 bytes，SHA256 `6e06b49ba82da901e2c9a7cf7d13711954e3fe7f8ed00ccdd9523c836a4d1e0d`。 |
| `/tmp/carleman-t205-axioms.log` | 0 bytes，stderr 为空。 |
| `/tmp/carleman-t205-endpoints-local-axioms.txt` | 2,937,412 bytes；SHA256 `e718f2be6d571068589b98d075cbe506f5c7583e2288d53ce10fd60b47250ed2`；末行确认 **8927** 项全命名空间递归审计通过。 |
| `/tmp/carleman-t205-local-source-manifest.txt` | 105,602 bytes；SHA256 `3dfbf00ec834220aa4a9e129b6cf238510e5f0133c0998fb73eeb60e7d962c1d`。独立枚举固定 Git 树的全部 tracked Lean 文件及三项工具链配置，共 **974** 项；集合精确、无重复，每项摘要均与 proof blob 相同。 |

六项 raw 展开类型起于第 38333、38339、38347、38367、38393、38414 行，每项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。全部 3492 条显式依赖列表及 9 条无公理输出均无白名单外项；另直接核对固定全命名空间循环使用 `privateToUserName` 和 `collectAxioms`，覆盖私有及生成声明。工具链为 Lean 4.35.0、compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定配置及证据一致。

**签发结论：C221 在上述 AUXILIARY 范围可接受，6/6 PASS，无修复项。** 原同一弱状态的 H 连续迹及初终值已由该接口证明；实际控制族整合和一般空间分支仍单列，P021 与 17/26 不变。报告签发后冻结正文与时间，仅提交此报告，不改数学、台账或原稿。
