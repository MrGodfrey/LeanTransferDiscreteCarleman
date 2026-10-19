# T133 / C149 独立本机验收

- `checked_sha`: `c3ea3c03352de258d944bf495695b31bcef3f3b0`
- `base_commit`: `a69b48ebeef0ea36e6f324c6bd2e1e7bf6659f52`
- `reviewed_at`: `2026-10-19T07:25:07+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：实际经典 Laplacian 乘积法则、原 H¹ 弱 Poisson 解的截断卷积恒等式及截断后平滑函数的统一 H² 界。原弱解的内部 H² 极限、边界正则性、凸域全局估计与穷竭仍待，P023 不提升，原文保持 **14/26**。

本 Agent 直接读取固定 Git 对象中三模块全部证明、12项实际展开类型、关键依赖、原稿、T133 分析、MATH_SPEC 和 C149/T133 清单；治理协议与已读版本相同，已核对版本。执行者说明、历史验收标签和 CI 未替代数学判断。后续 T134 工作树及动态 `.ci/axioms.txt` 未纳入本次依据。

## 全部十二项声明

名称省略 `Carleman.`；源位置以 `Carleman/Spatial/` 为根。顺序与固定台账及交付 JSON 完全一致，包含实际定义。类型行号来自本次独立下载并逐字节比对的原始 axioms.txt。

| # | 声明 | 固定源位置 / 完整类型行 | 独立结论 |
|---|---|---|---|
| 1 | `spatialLaplacian` | `SmoothLaplacianProduct.lean:13` / 27716 | PASS；定义为标准 Euclidean 坐标方向实际纯二阶 Fréchet 导数之和。 |
| 2 | `smooth_directional_mul` | `SmoothLaplacianProduct.lean:17` / 27718 | PASS；真实全空间光滑函数的一阶方向乘积法则，方向任意且未漏项。 |
| 3 | `smooth_second_directional_mul` | `SmoothLaplacianProduct.lean:25` / 27724 | PASS；真实同方向二阶乘积法则，两个交叉项合成系数2。 |
| 4 | `spatialLaplacian_mul` | `SmoothLaplacianProduct.lean:46` / 27732 | PASS；逐坐标求和给 Δ(fg)=fΔg+2ΣᵢDᵢfDᵢg+gΔf。 |
| 5 | `SpatialTest.mulSmooth` | `SmoothLaplacianProduct.lean:59` / 27744 | PASS；真实乘积 ηf 保持全空间 C∞、紧支及原域支持，是同一函数的原 SpatialTest。 |
| 6 | `SpatialTest.laplacianLp_ae` | `SmoothLaplacianProduct.lean:66` / 27748 | PASS；实际纯二阶导数 L² 类之和，在原域 a.e. 等于经典 spatialLaplacian。 |
| 7 | `spatialLaplacian_smooth` | `CutoffPoissonConvolution.lean:15` / 27751 | PASS；真实二次导数的有限和保持 C∞。 |
| 8 | `SpatialTest.laplacian_eq_zero_of_notMem_tsupport` | `CutoffPoissonConvolution.lean:23` / 27754 | PASS；一阶导数支持包含于原支持，再用支持外 fderiv 为零得到实际 Laplacian 为零。 |
| 9 | `IsWeakNegativeLaplacian.cutoff_convolution` | `CutoffPoissonConvolution.lean:32` / 27758 | PASS；只在截断支持上要求反射核合法，内部用原弱 PDE 和一阶链，支持外用实际导数消失，得到每个全空间点的精确身份。 |
| 10 | `SpatialTest.exists_laplacian_multiplier_bound` | `CutoffPoissonEstimate.lean:16` / 27781 | PASS；由固定真实截断内部构造统一 M≥0，控制值、全部一阶坐标导数及 Laplacian。 |
| 11 | `IsWeakNegativeLaplacian.cutoff_laplacian_bound` | `CutoffPoissonEstimate.lean:46` / 27790 | PASS；实际 MemLp、非负单位核 L² 收缩、有界乘法及有限 Minkowski 给精确所列范数界。 |
| 12 | `exists_uniform_cutoff_H2` | `CutoffPoissonEstimate.lean:122` / 27814 | PASS；M 先于解、载荷和核选择，输出同一截断平滑函数的真实 H² jet、完整一阶截断、负 Laplacian 和显式 Sym 维数因子。 |

## 原稿目标与本阶段范围

已核对固定 `paper/main.tex:2659–2664`：`prop:analytic-realizations` 为原凸多面体或盒上的 Dirichlet Laplacian 供应 A1–A3，并引用 Grisvard Theorem 3.2.1.2 获得 D(A)=H²∩H¹₀ 及椭圆正则估计。本批是构造内部正则性证明的截断平滑化工具，不是原完整推论，也不是原凸域 Hessian 估计的直接形式化。

本批接受任意实际弱 H¹ jet u 和原域 L² 右端项 f，只要求 `IsWeakNegativeLaplacian u f`，无需 u 为光滑函数、H² 或 H¹₀。已展开该谓词：它对全部原 SpatialTest 要求真实全梯度配对等于 f 与测试值的 L² 内积，正是 −Δu=f 的弱形式。更广的 H¹ 输入覆盖原 Dirichlet 状态，没有缩小原状态类。

η 是给定的真实紧支光滑测试；本批证明关于该固定 η 的常数与估计，尚未构造在任意内部紧集上等于1的截断。κ 的非负、单位积分和反射支持条件在最终类型中明确保留。它们是平滑化所需的公开核条件，不是预设目标估计；具体核序列、强极限及原弱解内部 H² 结论仍须后续供应。边界正则性、全局凸域先验界和穷竭均未提前认定。

## 实际经典导数、乘积和 L² 代表

第1项直接定义 Δf(x)=ΣᵢDᵢ(Dᵢf)(x)，每次 D 均是实际 `fderiv` 在 Euclidean 标准基上的求值；不是任意命名的候选 Laplacian。第2项使用真实可微性和 `fderiv_mul`；第3项先取得两个实际一阶方向导数函数的 C∞，再对一阶乘积法则逐项求导，因此系数2来自两个真实交叉项。第4项只作有限坐标和的代数重排，不漏混合的一阶乘积项。

`mulSmooth` 的 value 就是 η.value*f；紧支来自左因子 η，支持来自 tsupport_mul_subset_left。它没有要求一般平滑 f 紧支。`laplacianLp_ae` 同时取有限多个二阶导数 toLp 的 a.e. 身份及真实有限 L² 和的代表身份，因此把同一实际 L² Laplacian 与同一经典表达式识别；不是对 L² 类任意取点值。

第8项利用 tsupport(Dᵢη)⊆tsupport η，推出在原支持外 Dᵢ(Dᵢη)=0。配合 η 自身及其实际 Fréchet 导数在支持外消失，使后续全空间身份的域外分支完全成立；没有只证明在 support η 内的公式后遗漏边界或域外点。

## 原弱 PDE 的局部卷积与全空间截断身份

记 U=(E_Su)*κ、F=(E_Sf)*κ、Gᵢ=(E_SDᵢu)*κ，其中 E_S 是实际 L² 零延拓。第9项的实际结论为所有 x 上

\[
\Delta(\eta U)(x)
=-\eta(x)F(x)+2\sum_i D_i\eta(x)G_i(x)+(\Delta\eta)(x)U(x).
\]

已直接复核 `WeakPoissonConvolution` 和 `DomainConvolution`。对 x∈tsupport η，公开条件要求任意 y∈tsupport κ 都有 x−y∈S，故反射核在 S 上确为合法紧支光滑测试。反射的一阶导数负号与原弱 Poisson 配对给 −ΔU=F；原 jet 的实际一阶弱身份给 DᵢU=Gᵢ。这里 `IsWeakSpatialDerivative.zeroExtend` 的目标是 `IsWeakSpatialDerivative volume S`，测试域仍为 S；没有把一般零延拓的弱身份错误升级为全空间测试域 univ。

U 的全空间 C∞ 来自实际 L² 函数与光滑紧支核的卷积光滑性，独立于原解是否有二阶导数。对支持内点，将上述局部识别代入经典乘积公式，负号和交叉项系数2正确。对 x∉tsupport η，η、fderiv η 和 Δη 都为零，公式两侧直接消失，因此无需在这些点要求反射核留在 S。条件只作用于截断支持，而非整个 S；无需 κ 对称、无需特殊核形状，也没有隐含原状态的全空间 H² 零延拓。

## 常数、MemLp 和真实范数估计

第10项内部取得 η 的全局值界 A，每个真实坐标导数的非负界 Bᵢ，以及 Δη 在紧集 tsupport η 上的界 D；后者使用实际 Laplacian 的连续性。支持外 Δη=0。随后取

\[
M=\max(0,A)+\sum_i B_i+\max(0,D)\ge0,
\]

同时控制 |η|、全部 |Dᵢη|、|Δη|。M 只由固定截断及维数决定，不从 u、f、κ 或某个积分的数值反推。M=0 和零截断也合法，证明未除以 M。

第11项对任意原域实际 L² 类 v，先把 E_Sv 作非负单位质量卷积，调用真实 L² 收缩性得到全空间 MemLp 及范数≤‖v‖，再以 measure.restrict_le_self 限制到 S。将 eLpNorm 转为实值时显式使用全空间 MemLp 的有限性，未把 ∞ 的 toReal 当作可用能量。已直接读取 `ConvolutionL2`：该收缩性由非负单位核的加权 Cauchy–Schwarz、可积平方卷积及真实积分卷积恒等式证明，不是额外假设。

证明分别为 ηF、每个 DᵢηGᵢ、其有限和以及 ΔηU 建立实际 MemLp；乘子由真实光滑性给可测性、由同一 M 给有界性。`memLp_mul_of_ae_bound` 和相应范数引理作用于实际函数及其 toLp a.e. 身份。随后使用有限 Minkowski、两次 L² 三角不等式及系数2的精确齐次性，得到

\[
\|\Delta(\eta U)\|_{L^2(S)}
\le M\left(\|f\|_{L^2(S)}+2\sum_i\|D_i u\|_{L^2(S)}+\|u\|_{L^2(S)}\right).
\]

左端 `φ.laplacianLp` 与 −ηF+2ΣᵢDᵢηGᵢ+ΔηU 的 a.e. 身份由第6、9项连接，再转为同一 Bochner L² 范数。右端保留真实坐标梯度 L² 范数之和，没有无损改写成单一全梯度范数；未遗漏维数因素，也没有使用不可积函数的默认积分。

## 实际 H² jet 与统一量词

第12项量词顺序为固定开域 S 和固定 η 后先选 M，再量化所有原弱 H¹ 状态 u、右端项 f、真实弱 PDE、κ 及合法核条件。由第10项供应 M 和全部三个乘子界，然后对同一个 φ=ηU 调用已验收的 `SpatialTest.exists_H2_jet`。

已直接读取 `CompactTestHessianEnergy`、`CompactTestH2Jet` 和 `WeakH2BoundedTest`：紧支测试的有序 Hessian 平方和与真实 Laplacian L² 范数平方通过两次弱分部积分精确相等；每个实际二阶分量由该能量界控制。真实弱导数表示、混合导数交换和无序字段组装给 v。输出完整 `truncate 1 v=φ.sobolevJet`，不只是零阶值相同；`negativeLaplacian v=−φ.laplacianLp` 由真实弱导数唯一性识别全部对角项。

因此最终结论保留

\[
\|\operatorname{field}_2v\|^2\le
\#\operatorname{Sym}(\operatorname{Fin}d,2)\,
\left[M\left(\|f\|+2\sum_i\|D_i u\|+\|u\|\right)\right]^2.
\]

该维数因子是原实际无序二阶字段的坐标数；没有把有序双和与无序范数误认成无系数相等。平方单调性明确使用两侧非负性。输出的 v 是截断平滑函数的 H² jet，并非已证明原 u 本身为 H²；其负 Laplacian 也不是直接等于原 f，截断与卷积的额外项仍由上面的真实身份保留。

声明允许任意维数、空域及零状态，不增加凸性、有界性或边界光滑性。d=0 时空和与无序二阶字段按实际类型处理，未除以 d。对原 P023 所需的维数范围，本辅助结论没有缩小状态或几何类；时间、T 和网格不进入该阶段。

## 固定版本、依赖与递归公理

三新模块的 Carleman 导入闭包共113模块，其中110旧模块与 base `a69b48ebeef0ea36e6f324c6bd2e1e7bf6659f52` 逐字节相同。关键 `CompactTestH2Jet` 的75模块闭包、`WeakPoissonConvolution` 的85模块闭包相对 [T132 / C148](T132-local-acceptance.md) 固定版本完全相同；`WeakH2BoundedTest` 的56模块闭包相对 [T131](T131-local-acceptance.md) 的 `94f7ddd96b42ac046a4dc2cb14fffb5cd97f1402` 不变；`L2BoundedMultiplierLimit` 的62模块闭包相对 [T121](T121-local-acceptance.md) 的 `4689b4942585bde7e96bc0ecfa1a360de012db2b` 不变。实际数学调用条件均已核对，未仅引用旧 PASS。

固定 root 导入三模块；新源码没有 sorry、admit、额外 axiom 或 native_decide。原稿、治理及工具链 pins 与 base 不变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定4.35.0，mathlib pin 及本机实际干净 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

实际读取 `/tmp/carleman-t133-cutoff-target.log` 的3290 jobs成功记录、`-full.log` 的3925 jobs成功记录及6968声明递归审计PASS。固定 `/tmp/carleman-t133-cutoff-local-axioms.txt` 为 **2,135,281 bytes**，SHA256 **`d72677eb1bca4ecce1ea6ad2bcabf7f52210227baf564fd85adb46e1d9d0cd8b`**。12项完整类型及公理记录均存在，依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。

全文2434条非空及8条无公理打印记录无其他公理。固定 CheckAxioms 的递归主体与 base 不变，按 privateToUserName 识别全部 Carleman 声明并递归 collectAxioms，包含生成和私有声明。末行6968项审计不是仅对12项显式接口作检查。

## 同 SHA 正式 CI 与独立原始下载

本 Agent 自行查询 [main CI 39215380428 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39215380428/attempts/1)。run 为 main/push，head SHA 精确匹配，最终 completed/success，`updated_at=2026-10-19T07:23:53Z`。三 job 全部 completed/success：lean **117937885359**、state-check **117937885597**、dashboard / snapshot **117938907972**。已等待 Lean 收尾及 dashboard 完成，没有把产物提前可下载当作三项已成功。

同 run 原始 artifact：`lean-ci-result` **12169745827**，压缩产物492 bytes，digest `sha256:4d467432f17c900fc9af53bb9fe1ec940f839d16c6aa38e4c07eec2fd7d9db4f`；`lean-declaration-evidence` **12169293096**，压缩产物196686 bytes，digest `sha256:ccbf314618e0ee9109bf6c3a990342f64175931015c77a8929d480054419fe5d`。两份 workflow_run 元数据均绑定该 run、main 和完整 proof SHA。两次独立 `gh run download 39215380428` 下载至约定 `-main-ci` 和 `-main-axioms` 目录，均 exit 0。

实际 `/tmp/carleman-t133-cutoff-main-ci/result.json` 为 **PASS**，`checked_sha=source_head_sha=c3ea3c03352de258d944bf495695b31bcef3f3b0`，targets 为 Carleman，`finished_at=2026-10-19T07:22:43.796424+00:00`，ci_url 指向上述 run/attempt。Lean 编译器提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 为上述 pin。解压 result 为537 bytes，SHA256 `93db19130f668bd24c79b04a7b727e0014e2deac1bdcc82bd3c7a42694d42fc0`。

实际 `/tmp/carleman-t133-cutoff-main-axioms/axioms.txt` 与固定本机副本独立逐字节一致：**2,135,281 bytes**，SHA256 **`d72677eb1bca4ecce1ea6ad2bcabf7f52210227baf564fd85adb46e1d9d0cd8b`**，末行为 **6968项全声明递归审计PASS**。本批12项的完整类型及基础公理均在此同版本原始证据中，未混入后续工作树。

## 验收决定

**C149：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 12项声明未发现需修复的数学缺陷。真实乘积规则、支持外导数消失、原弱 PDE 的局部卷积识别、全部 MemLp、同一截断常数与统一量词，以及真实 H² jet 和 Sym 维数因子均已核实；同 SHA 三项 CI 与独立下载原始公理证据一致。

原弱解的内部极限和边界正则性仍待，P023 不提升，原文保持 **14/26**。本次仅新增本报告，未修改实现、台账、原稿或 root，未 commit/push。签发 UTC 如上固定；最终核对并通知主 Agent 后冻结报告内容与时间戳。
