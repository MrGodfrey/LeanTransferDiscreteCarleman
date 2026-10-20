# T214 / C230 独立本机验收

- checked_sha: `9662adfb01356f17d6bdb85ea93c7e47046373b0`
- base_commit: `a7ffa08f871d033a1729d80f998b56c5e98d6218`
- reviewed_at: `2026-10-20T04:52:18+00:00`
- reviewer: independent local Agent `/root/accept_spatial_foundations`
- result: **PASS — 6/6 定理，无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，P021 不提升**
- evidence_source: **local**；按简化协议核对固定提交的真实本地构建、公理及源清单，不查询远端 CI。

独立读取固定 Git 对象中三模块全部证明、六项完整 raw 类型、分析/MATH_SPEC/台账，对照原稿 `paper/main.tex:2338–2415` 的能量解与控制极限识别。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。全文读取 T213 冻结报告 `3a869e6b41c8a21d3e60f08ef657ed58164dd63b`，并直接读取它的三模块实际证明及本批使用的 T212 逐时能量接口、弱导数减法、原载荷和连续端点接口。

## 六项声明

源码均位于固定 SHA 的 `Carleman/Control/`；声明省略公共前缀 `Carleman.`。raw 行号指 `/tmp/carleman-t214-uniqueness-local-axioms.txt`。

| 模块:行 | 实际声明 | raw 行 | 结论 |
| --- | --- | --- | --- |
| VolterraEnergyUniqueness:13 | `continuous_volterra_nonneg_eq_zero` | 39902 | **PASS**：连续非负 f 满足原 Volterra 界即在全部闭区间为零，不要求 f 可微。 |
| TimeCutoffEnergyNorm:12 | `time_cutoff_norm_sq_of_ae` | 39910 | **PASS**：实际时间截断范数平方等于同一代表的部分区间平方范数积分。 |
| DirichletEnergyUniqueness:15 | `dirichlet_mass_energy_zero` | 39917 | **PASS**：零初值、零控制的原质量弱能量解及其真实连续 H 迹全为零，无终态前提。 |
| DirichletEnergyUniqueness:70 | `dirichletTimeLoad_sub` | 39934 | **PASS**：固定同一 b，实际载荷对状态/控制差的精确线性身份。 |
| DirichletEnergyUniqueness:82 | `dirichlet_mass_energy_unique` | 39944 | **PASS**：同一 b/U 和相同初迹的任意两质量弱能量解，在完整 L²V 与全部连续 H 时间迹上相等。 |
| DirichletEnergyUniqueness:125 | `FiniteDirichletControlIdentity.identifies_energy_solution` | 39971 | **PASS**：原控制极限识别任意同数据比较解，并推出比较解终迹为零；零终态不是其输入。 |

## 数学核对

**Volterra 引理。** f 仅在 `[0,T]` 连续非负，输入原不等式 `f(t)≤C∫₀ᵗf`、T>0、C≥0。证明把实际 f 夹持延拓为连续 F；在原区间 F=f，实际原函数 `G(t)=∫₀ᵗF` 由 FTC 满足 G'=F，且 G(0)=0。对每个 t∈[0,T)，利用 f≥0 及原不等式得到 `‖G'(t)‖≤C‖G(t)‖`，再应用真实 mathlib Grönwall 零初值推论。已直接阅读固定 mathlib 的 `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` 及其 Grönwall 依赖：它只要求 G 连续和右导数界；本批的真实原函数提供全部条件。最后由 G=0、原不等式及 f≥0 推出 f=0。没有把 f 的可微性或零值作为前提，C=0 分支亦覆盖，没有小时间条件或除以 C。

**真实局部范数。** `time_cutoff_norm_sq_of_ae` 展开实际 `(0,t]` 指示乘子，使用单/双侧截断内积身份及 `L2.inner_def`，将范数平方化为真实限制积分。由 `0≤t≤T` 证明 `((volume|_(0,T])|_(0,t])=volume|_(0,t]`，再限制原 q=Z a.e. 身份。积分可积性来自原 L² 类；不另要求 q 连续或某个任意代表逐点相等。t=0 与 t=T 均包含；没有利用端点零测来赋予 q 端点值。

**原零数据解。** `dirichlet_mass_energy_zero` 的输入是实际 Y∈L²(0,T;H¹₀)、同一原 b、质量弱方程 `(MY)'=D(b,Y,0)`，以及真实 H 连续 q=EY a.e. 和 q(0)=0。没有 Y 的 V 值强时间导数或 q(T)=0。T212 的逐时能量恒等式给 `‖q(t)‖²=2∫₀ᵗ〈Y,D〉`；真实部分积分与 T213 的载荷截断配对相接。控制项确为零，梯度项以负的完整平方范数出现，丢弃该非负耗散后给
`‖q(t)‖²≤2*b.bound·∫₀ᵗ‖q(s)‖²`。
系数 2、初值差方向、势项符号和部分区间均一致。b 允许变号，仅使用真实乘子上界，不要求小势、非负势或更强正则性。

把 f 取同一 q 的连续范数平方，Volterra 引理给所有 t∈[0,T] 的 q(t)=0。之后用原 q=EY a.e.、原值嵌入的注入性和 Lp.ext 推出整个 H¹₀ Bochner 状态 Y=0，故未只证明零阶值为零而遗留独立梯度。所有 t 共用同一个 Y/q/b，未逐时更换解或例外集合。

**同一数据差方程。** `dirichletTimeLoad_sub` 展开真实载荷 `E*U−G*GY−E*J*(b·JEY)`，用固定 CLM、同一个 b 的实际乘法线性性及代数得精确差身份。唯一性证明保留同一 b 和 U，故差载荷是 `D(b,Y−Z,0)`。真实弱导数减法先验证原 L² 项的配对可积性；随后分别用 Lp 差的 a.e. 公式搬运质量值、载荷导数和 q−r 的原值身份，未把 Lp 类的任意代表当成处处可减的相同函数。

由相同初迹得到 `(q−r)(0)=0`，调用零数据定理即得 Y=Z 及整个闭区间 q=r。比较对象无需满足 FiniteDirichletControlIdentity，也无需零终态。连续 H 代表及其 a.e. 身份是此能量解接口的明确前提；没有提升为 V 连续或 V 值强 H¹。原质量弱导数本身已在 T204/T212 能产生 H 连续代表，本批没有把额外强时间正则藏入比较条件。

**控制极限的识别。** 最后一项先从原 Y 的有限弱身份内部获得其真实连续 q、q(0)=y0、q(T)=0 及原质量弱方程；比较解 Z 只输入同一 b/U 的质量弱方程、真实 H 连续 r=EZ a.e. 和 r(0)=y0。类型中不存在 r(T)=0，也不要求 Z 的有限弱身份。实际唯一性给 Y=Z、q(T)=r(T)，因而推出 r(T)=0；这是结论，不是比较解的预设。

**范围边界。** 定理针对原开域 S、有限空间测度及正时间区间；不增加盒域、凸性、正维、H²、网格或观测假设。唯一性允许任意原 U，不需要先附加区域支撑。此批证明的是实际质量弱方程表述下的能量解唯一性与已有控制极限识别；原 StrongDual 表述到质量表述的完整互换及最终能量解定义整合尚待，不将本批冒充整条 P021 或一般多面体 CE 的完成。

## 固定本地证据与依赖

`/tmp/carleman-t214-local-evidence.json` 的 checked/source SHA 均为本报告 proof，source=local、status=PASS，finished_at=`2026-10-20T04:46:28.394407+00:00`；实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0。已读取三模块定向 `target-build.log` **3641 jobs** 成功及全库 `build.log` **4234 jobs** 成功；`axioms.log` 为 0 bytes。核查实际执行记录及固定源码关联，未声称审核者重跑旧闭包。

独立枚举 `/tmp/carleman-t214-local-source-manifest.txt` 的 **998** 个 tracked Lean/构建配置项，集合完整无重复，各项 SHA256 均匹配 proof Git blob。清单 108243 bytes，SHA256=`ca837f21f6a2e0ad2d9dfaf436ef8625903795e71cab50a42a83b01019726ea7`，与 evidence 绑定相符。三模块递归 Carleman 源闭包 **438** 文件，其中 **435** 个旧文件与基线逐字节不变，三个新增模块全读。

另比对已接受 T212 的 PivotWeakEnergyIdentity、T200 的 DirichletTimeLoad、T204 的 PivotTimeContinuity、T205 的 DirichletTimeEndpoints，源码均逐字节不变。T213 的三个关键源已直接重读。新增引用的 `Mathlib/Analysis/ODE/Gronwall.lean` 已实际检查，且所读文件与 pin `56a005855ea17e0b0958f73ec801ae140b0a1679` 的 Git 对象逐字节一致；不以定理名称代替其实际条件。Lean v4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 与 mathlib pin 均匹配固定配置。

固定 raw **3073557 bytes**，SHA256=`8bd1fb3855c26c8959da18d0c629ec34d93bc2e885dd4053011898db902896d9`。六项完整类型/公理均已逐项读取，root 实际导入三模块，六项 `#check`/`#print axioms` 齐全。固定审计循环经 `privateToUserName` 遍历命名空间并递归 `collectAxioms`；raw 全部 **3556** 条显式记录（3552 个唯一声明，9 条无公理）只含 `propext`、`Classical.choice`、`Quot.sound` 或无公理，末行 **9031** 项全命名空间递归审计 PASS。未发现 sorryAx 或白名单外项。

本报告在上述 reviewed_at 冻结，仅单文件提交；不修改数学实现、台账、原稿或覆盖统计，不 push。
