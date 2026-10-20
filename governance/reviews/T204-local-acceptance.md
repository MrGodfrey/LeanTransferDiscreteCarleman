# T204 / C220 独立本机验收

- checked_sha：`7afc739b6c8f95e208beeaefed4b955f0eebbdb5`
- mathematical_base：`d6634423766eaa11b670fb643578e3a62ff1a71e`
- reviewed_at：`2026-10-20T03:45:17+00:00`
- reviewer：独立 Agent `/root/accept_spatial_foundations`
- 结论：**PASS，4/4 声明，无阻断缺陷；AUXILIARY，17/26 不变，P021 不提升。**

直接阅读固定 Git 对象中两新模块的完整证明、四项 raw 展开类型、`governance/analysis/T204-pivot-continuity.md`、MATH_SPEC 对应段和 C220/T204 台账。实际原稿 `paper/main.tex:2415` 包含 H 连续代表与初终值识别；本批完成前一部分，后一部分仍待。原稿 SHA256 保持 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 四项声明

源路径为固定 `Carleman/Control/<模块>.lean`；名称均带 `Carleman.` 前缀。raw 行来自 `/tmp/carleman-t204-pivot-continuity-local-axioms.txt`。

| 模块:源行 | 声明 | raw 行 | 独立结论 |
| --- | --- | ---: | --- |
| PivotTimeContinuity:18 | `HasWeakTimeDerivative.sub_memLp` | 38280 | PASS；先证明四个测试乘积可积，原弱导数积分身份相减，保留导数及负号。 |
| PivotTimeContinuity:34 | `pivot_path_limit` | 38290 | PASS；真实质量迹界给全路径两索引 Cauchy，完备性产生连续 p，且实际 `pathL2 p=EₜY`。 |
| PivotTimeContinuity:120 | `exists_pivot_time_representative` | 38302 | PASS；有界单射 E 内部给真实质量非负性与稠密值域，正则化路径及两项 L² 极限内部构造，返回原 EY 的 H 连续代表。 |
| DirichletTimeContinuity:15 | `FiniteDirichletControlIdentity.continuous_H_representative` | 38313 | PASS；原 Dirichlet 值嵌入的单射性和质量弱导数均内部清偿，保持同一 Y、U、b、y₀。 |

## 数学与量词核对

**真实路径范数与两个索引。** `TracePath` 展开为 `C(Icc 0 T,H)`，不是 Lp 空间或仅逐点函数集。对真实连续弱 H¹ 路径 uₙ，记其实际 L² 类为 Uₙ，质量导数类为 Zₙ。`sub_memLp` 及 T202 的质量迹界应用于 uₙ−uₘ，得到

`‖pₙ−pₘ‖∞ ≤ sqrt(T⁻¹‖Eₜ(Uₙ−Uₘ)‖² + 2‖Uₙ−Uₘ‖‖Zₙ−Zₘ‖)`。

三个差的 `toLp` 身份逐一用实际 a.e. 代表及算子线性证明；没有把未核对的点态式直接视为 Lp 等式。平方根的非负条件由 T>0 和范数给出，`ContinuousMap.norm_le` 把每个闭区间时刻的界提升为实际上确界范数界。证明分别以 `Prod.fst`、`Prod.snd` 在 `ℕ×ℕ` 的乘积 atTop 上趋于无穷，将 Uₙ→Y、Zₙ→D 推成两个索引差同时趋零；由真实 metric Cauchy 等价判据得到整个 pₙ 序列 Cauchy，没有只检验相邻项或固定其中一个索引。

**连续极限确为同一个 EY。** H 完备且时间区间紧，实际连续映射空间完备，故得到 pₙ→p 于 `C([0,T];H)`。`pathL2` 是将路径经真实区间夹取连续延拓后映入 L² 的有界线性映射。源码分别用 `pathL2_ae`、`clampPath_on`、`E.coeFn_compLpL` 和原 uₙ 的 `toLp` 身份证明 `pathL2 pₙ=EₜUₙ`。两侧连续性与 L² 极限唯一性给 `pathL2 p=EₜY`。最后 `clampPath p` 在闭区间 H 连续，并由同一 Lp 身份恢复 `q=EY` a.e.；未以质量场 MY 的 V 连续性代替 EY 的 H 连续性。

**泛型构造不预设原状态连续。** `exists_pivot_time_representative` 只输入完整实 Hilbert V、H，有界单射 E、Y,D∈L² 和真实 `(E*E Y)'=D`。`E*E` 非负由实际伴随配对给出；其稠密值域由 `ker(E*E)=ker E=0` 与 Hilbert 正交补定理内部清偿。取明确 εₙ=1/(n+1)，T203 同时构造真实 V 连续 uₙ、其弱导数 duₙ，以及 Uₙ→Y、(E*E duₙ)→D。再应用上述路径极限结论。这里不假设原 Y 连续、E 满射、有界逆、有限维或闭值域；也不要求未加权 duₙ 范数一致有界。`pivot_path_limit` 本身甚至不要求 E 单射；单射性只用于从原质量弱导数构造所需近似族。

**原 Dirichlet 接口与范围。** 最终 V 是原 `DirichletEnergyState S`，H 是原 `Lp ℝ 2 (volume.restrict S)`；E 的单射性来自开放域上的真实弱 jet 值唯一性。`hid.mass_weak_time_derivative` 提供同一个 `dirichletTimeLoad T hS b Y U`，没有新增目标导数或近似序列前提。一步 TimeGrid 只编码正 T；Ioo/Ioc 转换使用时间端点零测，不增添周期轨道条件。最终明确前提仍为 T>0、S 开且有限测度、有界原势及既有 `FiniteDirichletControlIdentity`；d=0、空域未被排除。

T⁻¹ 及各连续算子的有限范数只用于固定 T 的收敛证明；没有将它们并入论文统一控制费用常数。本批产生真实闭区间连续函数和原 EY 的 a.e. 身份，未声称 q(0)=y₀、q(T)=0，亦未完成整个 P021。

## 必要依赖与本地证据

两新模块的 Carleman 递归源闭包共 **426** 文件，其中 **424** 个旧文件与基线 Git 内容全部逐字节相同。重读了实际 `MassRegularizedPaths`、`DirichletRegularizedPaths`、`WeakIntervalRepresentative`、`TimeInterval`、`MassRegularizerStrong`、质量弱导数及 `conformingEmbed_injective` 的调用依据。T202 的质量迹界已在报告 `31a68eca148364486a25a736b6272ee0779b6f34` 验收，固定实现保持不变。全文读取 T203 冻结报告 `51434001118a81a4b437dbf48210ebdb18d01084:governance/reviews/T203-local-acceptance.md`（3/3 PASS），当前报告与该提交逐字节相同。

另读取 mathlib 的乘积索引 Cauchy 判据、完备空间序列极限定理、紧域连续映射上确界范数判据及连续映射空间完备性。所读 `MetricSpace/Pseudo/Basic`、`UniformSpace/Cauchy`、`ContinuousMap/Compact`、`UniformSpace/CompactConvergence` 四文件均逐字节匹配固定 mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679`。

- `/tmp/carleman-t204-local-evidence.json`：`source=local`、`status=PASS`，`checked_sha=source_head_sha` 精确匹配本报告；实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均 exit 0，完成时间 `2026-10-20T03:42:45.908348+00:00`。
- `/tmp/carleman-t204-local-source-manifest.txt`：**972** 项逐一核对固定 Git 内容摘要，集合恰为全部受控 Lean 源文件及三项工具链/依赖配置，无重复、遗漏或多项。**105385 bytes**，SHA256 `20e315393582460ee96fe09e121ebcd8fe9204e54d98832f71aefc90c14387ef`。
- 实际读取 `/tmp/carleman-t204-target-build.log`：两模块成功、**3628 jobs**；`/tmp/carleman-t204-build.log`：完整根构建成功、**4207 jobs**。`/tmp/carleman-t204-axioms.log` 与 `probe4.log` 均为空；probe 空输出本身不单独用作退出码证据。本次核对固定执行记录，没有声称再次运行全库。
- 固定 raw **2930811 bytes**，重算 SHA256 `1d8820b367cb04cdf3eb997ed259b4e8c5829731df708572beefa0b2c444084e`，与证据/台账一致。四项根导入、`#check`、`#print axioms`、完整类型均对应，每项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
- 全部显式公理输出 **3495** 条、**3491** 个不同名称（9 条无公理），无白名单外项；另实际读取固定全命名空间递归审计循环，raw 末行确认 **8921** 项审计通过。Lean `4.35.0` / compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 与固定配置及证据一致。

按用户简化政策不查询或等待远端 CI。**C220 可在本报告 AUXILIARY 范围接受，4/4 PASS。** 初终值识别及完整定理组合仍待；签发后冻结正文与时间，仅单文件提交，不改变实现、原稿、台账或覆盖数。
