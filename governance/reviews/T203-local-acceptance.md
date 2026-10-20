# T203 / C219 独立本机验收

- checked_sha: `d6634423766eaa11b670fb643578e3a62ff1a71e`
- base_commit: `1b8ccf90c8aeef46bf0f614e537c02a6494caa5a`
- reviewed_at: `2026-10-20T03:42:52+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 3/3 显式声明，无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，P021 不提升**
- evidence_source: **local**；不查询或声称远端 CI 成功。

直接读取固定 Git 对象中两个新模块的完整类型和证明、分析 `T203-regularized-paths.md`、MATH_SPEC 对应段及实际关键依赖。原稿 `paper/main.tex:2403–2415` 从 V′ 弱导数转向 H 连续迹；本批只完成其中所需的真实连续正则化路径及两项 L² 强极限，没有完成第 2415 行的 H 连续代表或端点身份。原稿 SHA256 保持 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 逐声明核查

| 固定声明 | 源模块 | 结论 |
| --- | --- | --- |
| `Carleman.HasWeakTimeDerivative.linear_map` | `Carleman/Control/MassRegularizedPaths.lean` | **PASS**。原完整内部光滑测试的向量积分身份，经实际有界线性映射 L 传递。u、du 的 L² 资格保证两个测试乘积可积，再交换 L 与 Bochner 积分；负号保留。 |
| `Carleman.mass_regularized_time_paths` | 同上 | **PASS**。从真实 `(MY)'=D` 构造闭区间 V 连续的 uₙ 和其实际弱导数 duₙ，得到 `uₙ=QₙY`、`Mduₙ=QₙD` 的 a.e. 身份及对应两项实际 Lp 强极限。 |
| `Carleman.FiniteDirichletControlIdentity.regularized_time_paths` | `Carleman/Control/DirichletRegularizedPaths.lean` | **PASS**。将原同一 Y、U、b 的质量和载荷代入；非负性、稠密值域及质量弱导数均内部供应，返回真实全 H¹₀ 值连续路径和原 Y、D 的强逼近。 |

全部三项根导入、清单、`#check @...`、`#print axioms` 及固定 raw 展开类型已一一核对。

## 关键数学与量词

**连续性从质量弱导数推出。** 一般定理明确输入实 Hilbert 空间 V、非负且稠密值域的有界 M、Y,D∈L²(μ;V)、`g.timeMeasure=μ` 以及实际 `(M.compLpL Y)'=D`。证明将既有 `exists_continuous_representative` 应用于质量场，得到同一个 m，在 `[0,g.period]` 上 V 连续且 m=MY a.e.。重读该依赖确认 m 由 D 的真实 Bochner 原函数和弱导数为零时的常向量构造；没有把原 Y 的连续性当成输入。弱导数定义只使用 `(0,T)` 内完整紧支光滑测试，既不要求周期端点匹配，也不输入经典导数。

令 `Rₙ=(M+εₙI)⁻¹`、`Qₙ=MRₙ`，实际定义为 `uₙ(t)=Rₙ(m(t))`、`duₙ(t)=Rₙ(D(t))`。Rₙ 是已构造的连续线性算子，因此 uₙ 在整个闭区间连续；每个 duₙ 的 L² 资格由有界线性作用取得。m 的弱导数经上述 `linear_map` 给 uₙ 的弱导数恰为 duₙ。这里只需各 n 的有限算子范数，没有声称这些范数或 ‖duₙ‖ 对 n 一致有界。

**真实代表与强极限。** `hmae` 和 `M.coeFn_compLpL Y` 先把 m 识别为同一个 MY 的代表；再用真实交换式 RₙM=MRₙ 得 uₙ=QₙY a.e.。Mduₙ=QₙD 直接由 Qₙ 定义得到。两项 `toLp` 类分别通过 `coeFn_toLp`、a.e. 身份和 `coeFn_compLpL` 证明等于 `Qₙ.compLpL Y`、`Qₙ.compLpL D`，然后调用 T201 的实际 Bochner 强收敛。没有将代表的点态写法直接当作 Lp 类恒等式，也没有把第二项误写为 duₙ→D。原 Y 和原 D 始终固定，同一对序列 uₙ、duₙ 同时满足所有结论；εₙ只要求每项正且趋零，不要求单调或与任何网格尺度耦合。

**原控制实例。** 最终声明的 V 正是 `DirichletEnergyState S`，M 是原值嵌入 E 的 E*E，D 是同一 `dirichletTimeLoad T hS b Y U`，其定义保留原控制、同一 Y 的完整梯度和原产品势。实际使用 `hid.mass_weak_time_derivative`，没有向原控制问题增添目标质量导数、质量稠密性或正则化存在性假设。y₀保留在原 `FiniteDirichletControlIdentity` 输入中；本批没有替换数据，但也尚未识别 uₙ 或最终状态的初终值。

S 开且空间有限测度是最终接口的明确前提，原有界盒满足。给定 g 和 `g.period=T` 自动保证 T>0；g 在所用弱导数和代表定理中只提供正区间长度及真实测度，不施加离散方程或周期边界条件。`Ioo` 与 `Ioc` 的测度传输仅依赖 Lebesgue 端点零测，不把任意 Lp 代表的端点值当作连续迹。结论覆盖 `[0,T]` 的近似路径连续性，但不声称 `Euₙ` 已在 C([0,T];H) 一致收敛、EY 已有 H 连续代表，或原初终态已经识别。

## 固定依赖与执行证据

新模块的 Carleman 递归源闭包共 **423** 文件，其中 **421** 个旧文件与基线 Git blob 全部相同。关键闭包逐项比对：`DirichletMassRegularization` 的 409 模块与 T201 固定证明 `cf2701d48ac60007502c1ad44286c1d64b1303ce` 不变；`DirichletMassWeakDerivative` 的 418 模块与 T200 固定证明 `a081c61839658c2869ef6a01e7bcd387a81b9af4` 不变；`WeakIntervalRepresentative` 的 28 模块与基线不变。除了两个新证明，直接重读质量弱导数、线性映射积分交换、弱导数定义、闭区间连续代表、实际原函数及弱常向量构造，核实本次调用条件与方向。T202 的质量迹估计是后续用途，不是本批构造或极限的隐含前提。

独立读取 `/tmp/carleman-t203-local-evidence.json`，`checked_sha=source_head_sha` 均精确匹配本报告 proof SHA，`source=local`、`status=PASS`，完成时间 `2026-10-20T03:40:12.377586+00:00`。实际执行记录中的 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 均 exit 0。本次核对这些执行记录及源码关联，没有声称再次运行全库。

| 固定证据 | 独立核验结果 |
| --- | --- |
| `/tmp/carleman-t203-target-build.log` | 两新模块实际完成，3625 jobs；181 bytes，SHA256 `0f9cb9229a995a97cf51ca5851c1e5e7ccc5d67c93d26f9925ff7e35f2865a67`。 |
| `/tmp/carleman-t203-build.log` | 根目标实际完成，4205 jobs；80 bytes，SHA256 `d609a243006ef05cdf60fadf15a3d9eba72b527430f999b1a4cf8b5445ab2bc3`。 |
| `/tmp/carleman-t203-axioms.log` | 0 bytes，stderr 为空。 |
| `/tmp/carleman-t203-regularized-paths-local-axioms.txt` | 2,927,183 bytes；SHA256 `899fe722c25dd787605ebfd8d5e69ca9e2fc8df4a9f38a700a1a5ee19aca4e48`；末行确认 **8917** 个 Carleman 声明递归审计通过。 |
| `/tmp/carleman-t203-local-source-manifest.txt` | 105,167 bytes；SHA256 `7667b8d87340cb3cdfe446c6902881824252cd56a2a4734d1760751f0630e1e2`。固定 Git 树中全部 tracked Lean 文件及三项工具链配置共 **970** 项，覆盖精确、无重复，每项摘要与 proof blob 相同。 |

三项完整类型及公理记录分别位于固定 raw 第 38216、38223、38244 行起，仅依赖 `propext`、`Classical.choice`、`Quot.sound`。检查全部 3482 条显式依赖列表及 9 条无公理输出，均无白名单外项；另读取固定全命名空间审计循环，确认通过 `privateToUserName` 与 `collectAxioms` 递归检查私有及生成声明。工具链为 Lean 4.35.0、compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定配置及证据一致。动态工作树和未来审计不作为本批依据。

**签发结论：C219 在上述 AUXILIARY 范围可接受，3/3 PASS，无修复项。** H 一致极限、连续迹及端点仍待，P021 与原文 17/26 不变。报告签发后冻结正文和时间，仅提交本报告，不修改数学、台账或原稿。
