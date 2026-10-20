# T213 / C229 独立本机验收

- checked_sha: `a7ffa08f871d033a1729d80f998b56c5e98d6218`
- base_commit: `9a2857abc4c61b3c6de1fa2d282bac81f14a3d16`
- reviewed_at: `2026-10-20T04:46:32+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 9/9 定理，无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，不提升 P021，不声称唯一性**
- evidence_source: **local**；按当前简化协议核对固定提交的本地构建、公理与源文件关联，不查询或声称远端 CI 成功。

直接读取固定 Git 对象中的三模块全部证明、九项完整 raw 类型、分析与 MATH_SPEC，并对照原稿 `paper/main.tex:2338–2415` 的原能量空间、弱方程与连续迹。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。新增局部能量估计是该能量解路线的辅助步骤，不是原控制收敛整条结论或唯一性定理。

## 逐项结论

源码均位于固定 SHA 的 `Carleman/Control/`；raw 行号指 `/tmp/carleman-t213-local-load-local-axioms.txt`。

| 模块:行 | 完整声明 | raw 行 | 独立核对 |
| --- | --- | --- | --- |
| TimeCutoffPairing:17 | `Carleman.BoundedMultiplier.compLpL_map` | 39802 | **PASS**：真实时间标量乘子与固定 CLM 的 Bochner 延拓交换；四项 a.e. 代表身份和线性性给等式。 |
| TimeCutoffPairing:24 | `Carleman.cutoff_map_idempotent` | 39808 | **PASS**：实际可测集合指示乘子在 L² 类上幂等，集合内外分支均处理。 |
| TimeCutoffPairing:34 | `Carleman.cutoff_inner_integral` | 39814 | **PASS**：真实 L² 内积等于限制测度上的积分，使用实际乘子代表与指示函数积分公式。 |
| BochnerProductCutoff:17 | `Carleman.bochnerL2ProductIsometry_cutoff` | 39819 | **PASS**：实际 J 与时间截断交换；从简单函数证明再由稠密性和连续性延拓。 |
| TimeCutoffPairing:43 | `Carleman.cutoff_inner_cutoff` | 39826 | **PASS**：单侧与双侧截断配对相等，未假设任意 Lp 代表逐点一致。 |
| TimeCutoffPairing:54 | `Carleman.cutoff_multiplier_pairing` | 39832 | **PASS**：同一真实标量势与指示乘子交换，局部势配对等于截断态的二次配对。 |
| DirichletLocalEnergy:18 | `Carleman.dirichletTimeLoad_cutoff_pairing` | 39837 | **PASS**：展开原真实伴随载荷，得到控制项减梯度平方减原势二次配对。 |
| DirichletLocalEnergy:46 | `Carleman.dirichletTimeLoad_cutoff_upper_bound` | 39854 | **PASS**：Cauchy–Schwarz、原 `b.bound` 和 J 等距给局部上界；不引入目标估计前提。 |
| DirichletLocalEnergy:70 | `Carleman.FiniteDirichletControlIdentity.local_energy_inequality` | 39871 | **PASS**：对同一连续代表每个 `t∈[0,T]`，真实部分区间能量身份给系数 2 的梯度耗散不等式。 |

## 数学忠实性与假设边界

**真实截断和产品映射。** 已重读 `BoundedMultiplier.cutoff`：其值是可测集合的真实指示函数，界为 1；并非另设抽象投影。`TimeCutoffPairing` 的五项辅助结论适用于声明中的任意测度与实际 L² 类，没有暗加有限测度或光滑性。配对的可积性由两个 L² 对象保证，等式使用 `L2.inner_def`、a.e. 乘子身份和真实限制积分，不把不受控积分形式当作额外前提。

J 仍是 `simpleL2_productLinear.extendOfIsometry` 的实际线性等距延拓。其基础证明通过简单函数有限值域得到联合可测代表、真实 Fubini 平方范数身份及 Bochner 简单函数稠密性。本批先以可测 `piecewise s` 截断简单函数，证明其 Bochner 类等于 W 的作用；在产品空间上使用已证简单函数代表身份。集合外分支明确通过 `quasiMeasurePreserving_snd.ae (Lp.coeFn_zero …)` 处理零 Lp 类的代表，未把该代表假定为处处零。最后以两个连续映射相等的闭集包含稠密像，推广到所有原 Bochner L² 状态。因此不要求 J 满射，也不要求任意双层 Lp 代表联合可测。该项明确要求时间测度有限、空间测度 SFinite；原有限时间区间与受限 Lebesgue 空间满足这些条件。

**同一原载荷及耗散符号。** 已重读实际 `dirichletTimeLoad`、`dirichletStateValue`、`dirichletStateGradient` 和原有限弱身份。E 是原 H¹₀ 值嵌入，G 是全部真实弱梯度；它们的时间延拓作用于同一 Y。D 恰为 `E*U − G*GY − E*J*(b.map(J(EY)))`，其中所有星号是实际 Hilbert 伴随。新配对证明展开这个定义，逐次使用伴随恒等式、E/G 与 W 交换以及 J 与 W 交换，得到

`〈D,WY〉 = 〈WU,WEY〉 − ‖WGY‖² − 〈b.map(J(WEY)),J(WEY)〉`。

梯度平方恰出现一次且为负，原 U、b、Y 均未被替换。这里的 U 是原方程右侧的空间 L² 控制重构；局部能量步骤不需要也没有假设新的观测支撑。上界对可能变号的 b 使用绝对值配对，再以 `‖b.map z‖≤b.bound‖z‖` 和 J 的真实保范数消去 z，得到原 `b.bound‖WEY‖²`。没有把 b 假定非负、局部光滑或小势，也没有使用网格条件或额外状态预算。

**每个时刻的真实能量不等式。** 最后一项输入 `T>0`、开域 S、有限空间测度、原 `FiniteDirichletControlIdentity T S b y0 Y U`，以及任意满足闭区间连续性和 `q=EY` a.e. 的同一 q。连续 q 是此辅助接口的显式前提；已接受 T212 的 `continuous_H_energy_trace` 已从原有限弱身份内部构造同一 q，并同时给 q(0)=y0、q(T)=0。本批没有重新假设 Y 本身连续，也没有把目标能量不等式列为输入。

实际调用 T212 的 `energy_identity`，取 W 为 `(0,t]` 的指示乘子。由 `0≤t≤T`，证明 `((volume|_(0,T])|_(0,t])=volume|_(0,t]`；再以真实区间积分和实内积交换识别 `〈D,WY〉=∫₀ᵗ〈Y,D〉`。因此

`‖q(t)‖²−‖q(0)‖²+2‖WGY‖² ≤ 2(‖WU‖‖WEY‖+b.bound‖WEY‖²)`。

系数 2 来自真实范数平方的能量身份，端点差方向正确；t=0 与 t=T 均包括。端点只读取真实连续 q，未在任意 Lp 代表上指定值。所有 t 共用原 Y/U/b/q，不随 t 选择近似或载荷。声明不产生新的统一费用常数；T 固定但任意正，不将本批误称为 T 独立控制预算。未使用 Grönwall，未证明或宣布零数据唯一性、一般控制收敛或新的 PAPER 结果。

## 固定依赖与本地证据

已全文读取冻结的 [T212 验收报告](T212-local-acceptance.md)，报告提交 `5ac0a17bf01823f61003428674b282403ea6443c`，checked SHA 等于本批基线；同时直接重读它的实际 Dirichlet 能量接口。三新模块递归 Carleman 闭包共 **435** 文件，其中 **432** 个旧文件与基线逐字节不变。另核对 `BochnerProductL2`/`SimpleL2Product` 与已接受 T190 `f0ab18741c799cd2d821174cfce77ffbb454fa20`、`DirichletTimeLoad` 与 T200 `a081c61839658c2869ef6a01e7bcd387a81b9af4`、`DirichletTimeEnergyIdentity` 与 T212 均逐字节一致；重读与本批有关的实际定义和证明，不重复无关历史审核。

`/tmp/carleman-t213-local-evidence.json` 的 checked/source SHA 均为本报告 proof，source=local、status=PASS，finished_at=`2026-10-20T04:41:28.200604+00:00`。实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0；定向 `target-build.log` 为 **3637 jobs** 成功，全库 `build.log` 为 **4230 jobs** 成功，`axioms.log` 为 0 bytes。此次验收核查这些实际执行记录及固定源关联，未声称另行重建旧闭包。

独立枚举 `/tmp/carleman-t213-local-source-manifest.txt` 的 **995** 个 tracked Lean/三项构建配置文件，集合完整无重复，逐项 SHA256 与 proof Git blob 一致。清单 **107910 bytes**，SHA256=`454b09969e0011ca44de8b816a632cb6b43d544d01002613a07d40c23c8021b2`。Lean v4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 与 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定配置相符。

固定 raw **3067306 bytes**，SHA256=`c46bfc47e2d7efba57a63b356efa5f38615e76e638b6cad079df37919fcebe2c`。九项完整展开类型及各自公理记录均已核对，仅含 `propext`、`Classical.choice`、`Quot.sound`。raw 全部 **3541** 条非空公理列表及 **9** 条无公理记录均未出现白名单外公理；末行 **9025** 项全 Carleman 命名空间递归审计 PASS。已核查实际审计循环使用 `privateToUserName` 和 `collectAxioms`，不是只检查本批显式列表；不存在 sorryAx。root 实际导入三模块，九项 `#check`/`#print axioms` 完整。

本报告在上述 reviewed_at 冻结，仅单文件提交；不修改数学、台账、原稿或覆盖统计，不 push。
