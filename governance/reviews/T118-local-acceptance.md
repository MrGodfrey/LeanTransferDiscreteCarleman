# T118 / C134 独立本机验收

- `checked_sha`: `4e727b83c3fcb821432ba4089e6f9ea0c9e0a277`
- `base_commit`: `d533b7e90f5e8cecf266e09e8faa5afab3772ed7`
- `reviewed_at`: `2026-10-19T05:14:22+00:00`
- `reviewer`: `/root/accept_section3`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：有界开凸域的原全部弱 H² 数据，由同一实际向内卷积序列在整个闭包上实现值及全部一、二阶分量的强 L² 逼近；d≤3 时得到闭包连续代表、同一序列的一致极限及代表唯一性。**P011 不提升，原文保持 14/26。**

本 Agent 直接读取固定 git 对象中的五个完整模块、12 项实际展开类型及关键依赖，核对原稿 Section 6 的 P1 设置（`paper/main.tex:1462–1505`）和 Step 2（1523–1548），并读取固定 T118 分析及 MATH_SPEC。已读 AGENTS、运行/状态协议和原稿与前次读取版本逐字节不变。执行者说明、既有报告及 CI 没有替代本次语义审查。后续工作树、metadata 提交及变化中的 `.ci/axioms.txt` 不纳入审核。

## 全部 12 项声明

以下省略名称公共前缀 `Carleman.`；模块位于 `Carleman/Spatial/`。清单与固定 C134、T118 及 `/tmp/carleman-h2-closure-declarations.json` 完全一致。展开类型行号对应固定本地和相同远端 `axioms.txt`。

| # | 声明 | 固定源码 | 展开类型行 | 独立结论 |
|---|---|---|---|---|
| 1 | `exists_inward_mollifier_sequence` | InwardMollifierSequence:15 | 25936 | PASS；对整个收缩闭包取得几何支撑阈值，φ(n)≥n 且 φ→∞。 |
| 2 | `inwardMollification` | InwardMollification:15 | 25950 | PASS；真实卷积后复合实际向内仿射映射。 |
| 3 | `inwardMollification_smooth` | InwardMollification:19 | 25954 | PASS；任意全空间 L² 输入得到真正全空间 C∞ 函数。 |
| 4 | `inwardMollification_scaled_L2_error_tendsto` | InwardMollification:24 | 25957 | PASS；任意 k 与限制集合 K，rₙᵏ 倍实际向内卷积强收敛到原 L² 输入。 |
| 5 | `IsWeakSpatialDerivative.coordinate_one_inwardMollification` | InwardMollification:39 | 25966 | PASS；真实一阶坐标导数为 rₙ 倍原弱导数的同一向内卷积。 |
| 6 | `IsWeakSpatialDerivative.coordinate_two_inwardMollification` | InwardMollification:55 | 25977 | PASS；真实二阶张量坐标为 rₙ² 倍第二弱场的同一向内卷积。 |
| 7 | `WeakSobolevJet.inward_mollification_strong_h2` | WeakH2ClosureSmoothing:14 | 25989 | PASS；原 jet 自动供应全部弱链，整个 closure S 上同一序列的值、d 个一阶及 d² 个二阶坐标强收敛。 |
| 8 | `continuousOn_memLp_compact` | L2LimitRepresentative:13 | 26026 | PASS；只需在实际紧集上连续，就有该限制体积上的真实 L² 资格。 |
| 9 | `l2_limit_ae_eq_of_ae_tendsto` | L2LimitRepresentative:19 | 26031 | PASS；任意测度上的真实强 L² 极限和 a.e. 点态极限必 a.e. 相同。 |
| 10 | `WeakSobolevJet.inward_mollification_uniform_limit` | WeakH2ClosureContinuous:16 | 26039 | PASS；低维闭包一致 Cauchy 准则给同一向内卷积的一致极限及原值代表身份。 |
| 11 | `WeakSobolevJet.exists_closure_continuous_representative` | WeakH2ClosureContinuous:50 | 26056 | PASS；最终存在性确实为 ContinuousOn f (closure S)，包含空域。 |
| 12 | `WeakSobolevJet.closure_continuous_representative_unique` | WeakH2ClosureContinuous:63 | 26066 | PASS；原开域 a.e. 身份和连续性给整个闭包上的 EqOn。 |

## 整个闭包的几何支撑与同一序列

已展开 `ConvexCompactExhaustion`、`ConvexSupportContraction` 和 `ContractionSequence`。实际比例为 rₙ=(n+1)/(n+2)，满足 1/2≤rₙ<1、rₙ>0、rₙ→1。对任意 a∈S，集合

\[
K_n=\{r_nx+(1-r_n)a:x\in\overline S\}
\]

是有界闭包的连续像，故紧；开凸性以及 a 在内部、x 在闭包给 Kₙ⊆S。该结论包括原边界、角点的全部像，不要求光滑边界、特殊盒形域或预设延拓算子。

第 1 项对每个 Kₙ 使用已证紧集在开集中的支撑缓冲，获得 N(n)，使所有 m≥N(n) 的实际缩小核对 Kₙ 合法。取 φ(n)=max(n,N(n))，同时保证 φ(n)≥n、φ→∞，以及每个 n、每个 x∈closure S、每个 y∈tsupport κφ(n) 均有 rₙx+(1−rₙ)a−y∈S。φ 无需单调；趋于无穷已足以传递卷积强极限。

第 1 项完整类型没有状态参数，故这个选择仅依赖 S、a 和固定核。第 7 项虽以每个 u 后存在 φ 的形式陈述，其证明实际调用这个几何结果，随后同一个 φ 同时用于值和所有导数分量，没有按分量或状态重新选择核。最终一、二阶身份中的支撑前提由第 1 项在整个闭包内部清偿。

## 真实向内卷积、Jacobian 与导数因子

第 2 项准确为 Uₙ(x)=(u⋆κφ(n))(rₙx+(1−rₙ)a)。这是向内映射直接复合，不是旧 `contractedFunction` 的逆伸缩复合。第 3 项由真实卷积的全空间 C∞ 性与实际仿射复合得到 C∞，输入只有 L²。

已实际读取 `ScalarAffineL2`、`StrongInwardPullback`、`InwardApproximationLimit`：标量仿射换元的平方范数因子是 rₙ^(−d)，方向正确；rₙ≥1/2 给一个只依赖维数的统一拉回算子界。任意 L² 数据的拉回强连续性先用实际光滑卷积密度，再用该统一算子界证明，没有假设任意 a.e. 代表沿收缩点列逐点收敛。连续近似的证明使用精确能量极限及已证 Fatou 准则。

第 4 项用 φ→∞ 将实际卷积强极限传给变动序列，再用拉回的统一界与 rₙᵏ→1 得到缩放后全空间强收敛。最后通过 restrict K≤volume 限制到任意 K。所有差函数都由真实 MemLp 构造；转 ENNReal.toReal 时的有限性明确供应，未利用无穷范数默认转零。

第 5、6 项调用 `InwardSmoothDerivatives` 的真实 `iteratedFDeriv` 仿射链式法则，而非自定义候选梯度：第 k 阶得到 rₙᵏ。`coordinateDerivative` 是实际张量在标准基元组上的求值。因此一阶系数为 rₙ，二阶为 rₙ²，均不是倒数。

局部卷积导数的识别使用原全部 `SpatialTest S` 的弱身份。已检查 `DomainConvolution`、`LocalHessianConvolution`：反射核的支撑合法性由上述几何条件提供；反射负号和分部积分负号相消；二阶通过两条原弱链及实际光滑核导数交换、`fderiv_clm_apply`、`iteratedFDeriv_two_apply` 识别有序坐标。没有直接对单点局部等式求导，也没有假设原弱状态点态可微。

## 原全部弱 H² 与闭包上的强极限

第 7 项输入任意 `WeakSobolevJet d 2 (volume.restrict S) S`。原 k=0 和 k=1 的 `field_weak_derivative` 自动给出全部链，目标分量是实际 `derivativeComponent` 的 L² 类；二阶指标为 `Sym.cons (v 1) (Sym.cons (v 0) Sym.nil)`，与 `coordinateDerivative v` 的有序基元组对应。Fin 2→Fin d 覆盖全部 d² 个有序坐标，包括所有混合项。

同一个 Uₙ 对以下量强收敛，测度确实是 **volume.restrict (closure S)**：值到 value u 的 L² 零延拓，一阶及二阶坐标到各原弱分量的 L² 零延拓。目标并非原限制测度 Lp 类在 S 外任意选择的代表。第 7 项在闭包上逐点应用真实导数身份，再以真实 a.e. 恒等传递第 4 项的强极限；没有将内部 K 的结论冒充闭域结论。

`zeroExtendLp` 只表示 L² 指示函数延拓，`IsWeakSpatialDerivative.zeroExtend` 保留的仍是 S 内测试族的弱身份。本批未断言它在全空间具有弱 H¹/H² 导数。强极限只取在 closure S；光滑 Uₙ 的各阶全空间可积性也没有被作为跨边界 Sobolev 延拓前提。

强逼近部分不要求 d≤3。它采用锚点 a∈S，因此该带具体序列的接口适用于非空域；最终无锚点的连续代表存在性另显式处理空域。维数 d=0 不排除：一、二阶索引族为空，没有除以 d 或遗漏需要的分量。最终表述是各实际分量的强 L² 极限，而非另外构造一个带抽象 H² 范数的全空间延拓算子。

## 一致极限、a.e. 身份与闭包唯一性

第 8 项只需 ContinuousOn f K 与 K 紧，即从限制测度上的可测性和平方范数积分得到真实 MemLp。第 9 项的测度任意，输入 f、g 和 Fₙ 均确实 L²。强误差范数趋零先变为平方误差积分趋零；对任意 ε>0，最终平方误差积分≤ε。对 Fₙ−f 的 a.e. 极限 g−f 应用已证 L² Fatou，得 ∫(g−f)²≤ε，故真实非负可积函数的积分为零，进而 g=f a.e.。这不是将两个不相关序列的极限等同，也未增加统一支配函数。

第 10 项把同一 Uₙ 和同一目标分量交给 `convex_smooth_h2_uniform_limit`。已完整读取其证明与真实点值估计：对 Uₘ−Uₙ，以正体积 V、直径 D 及固定维数张量重构常数控制每个闭包点的值，右端为值和全部有限导数坐标的 L² 误差和。有限求和趋零使整个闭包上一致 Cauchy，实数完备性和一致极限连续性给 ContinuousOn f (closure S)。没有先假设存在连续代表或点态极限。

本批内部证明 closure S 紧且凸；非空开 S 的内部点 a 供应闭包的正体积，紧性供应有限体积；D 取真实 `Metric.diam (closure S)`。这些不再是调用者另需证明的形状、体积或直径假设。点值准则的常数允许依赖此固定域的 V、D 和维数；没有声称对所有域只依维数的统一嵌入常数。d≤3 仅在真正需要低维点值估计时使用，覆盖原 d=2、3 凸多面体。

一致极限给 closure S 上逐点极限；第 8 项保证 f 真实 L²，第 9 项将它识别为同一强极限的 L² 零延拓，再限制回 S 并用 `zeroExtendLp_ae_restrict` 得 f=value u a.e.。这一过程不要求向内移动卷积对原任意代表逐点收敛。a.e. 等于零延拓不表示 f 在边界逐点等于零，源码也没有作出这种推断。

第 11 项对 S 非空选择 a 后调用第 10 项；S=∅ 时取零函数并由零限制测度供应代表身份，所以最终存在性覆盖空域。第 12 项先用原开域的正测度性质将两个连续代表的 a.e. 等式升为 S 上逐点相等，再以两者在 closure S 连续及 S 在其闭包中稠密得到整个闭包的 EqOn。已核对 mathlib `Set.EqOn.of_subset_closure` 的真实条件。唯一性不依赖 d≤3、凸性或有界性，因为那些条件只用于构造代表；它不声称闭包外的任意延续唯一。

## 原文覆盖边界

原 P1 Step 2 用 H²(Ω)→C⁰(closure Ω) 为全部弱 H² 状态定义闭单元顶点值。本批确实完成该连续代表存在/唯一性的辅助义务，包含整个闭包而非仅内部连续性；前提只为有界开凸域和 d≤3，原 d=2、3 凸多面体满足这些条件，没有新增光滑边界或全空间 H² 延拓前提。

仍未完成 H¹₀ 状态的该代表在边界取零、原全部弱状态的局部节点值/梯度误差、与真实 conforming 节点空间的组合、全域允许权求和和原 P011 的完整数值假设。现在的闭域连续性本身不替代这些义务。本阶段没有时间权、T、τ、网格或 h 的最终估计量词，故不得据本批将全局加权结论或完整 P1 标为已完成。范围保持 AUXILIARY，原文 14/26 不变。

## 版本、构建与递归公理

五个新模块的 Carleman 导入闭包共 **134** 模块，其中 **129** 个旧模块与 base 逐字节不变。进一步比较实际关键已验收版本：`InwardApproximationLimit` 的 103 模块、`InwardSmoothDerivatives` 的 106 模块闭包与 T117 的 `d533b7e90f5e8cecf266e09e8faa5afab3772ed7` 一致；`SmoothH2UniformLimit` 的 62 模块和 `WeakH2Continuous` 的 107 模块闭包与 T116 的 `fa02c379c6ee0f59172dadc1401b9a535e6d3c9c` 一致；`StrongMollifierLimit` 的 72 模块闭包与 T115 的 `f134750df6b8ef03c639f50dd5084d4c42d49272` 一致；`LocalHessianConvolution` 的 53 模块闭包与 T114 的 `a5c68e2aaa4da98efe42da31ed0c1da04ba99952` 一致。相关记录见 [T117](T117-local-acceptance.md)、[T116](T116-local-acceptance.md)、[T115](T115-local-acceptance.md)、[T114](T114-local-acceptance.md)，关键调用已另作本次实质核查。

治理协议、原稿及 pins 与 base 不变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定 4.35.0；mathlib pin 与本机实际 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 mathlib 工作树干净。固定 root 导入全部五模块；新源码无 sorry、admit、额外 axiom 或 native_decide。递归审计器与 base 不变，collectAxioms 覆盖全部 Carleman 常量及私有/生成辅助声明，仅允许 propext、Classical.choice、Quot.sound。

独立读取固定 target 日志 **3311 jobs** 成功、full 日志 **3860 jobs** 成功，末尾 **6666** 声明递归公理审计 PASS。固定本地 `axioms.txt` 的全部 **2296** 条非空公理打印记录和 **8** 条无公理记录均无不允许的公理；12 项新声明的完整类型及正常基础公理已逐项核对。显式打印记录含重复，统计不同于全环境递归审计数量。

固定 `/tmp/carleman-h2-closure-local-axioms.txt` 为 **2,004,037 bytes**，SHA256 **`af52869568eec6d15315e484edd2b27cca632ebafa8a3d5051847a2d9e933f0d`**。

## 同 SHA 实际 CI 和独立下载证据

本 Agent 自行查询 [main CI 39203179575 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39203179575/attempts/1)。实际 main/push，head SHA 精确等于本报告 checked_sha，最终 **completed/success**，run 更新时间 `2026-10-19T05:13:45Z`。三项 job 均实际查询为 completed/success：

| Job | ID | 最终结果 |
|---|---|---|
| lean | 117900301003 | success |
| state-check | 117900301158 | success |
| dashboard / snapshot | 117901056251 | success |

同 run 原始 `lean-ci-result` artifact **12164347782**（归档 492 bytes）和 `lean-declaration-evidence` artifact **12164347783**（归档 184,151 bytes）元数据均绑定该 SHA，且未过期。本 Agent 自行执行两次 `gh run download 39203179575`，实际均 exit 0，分别下载到 `/tmp/carleman-h2-closure-main-ci` 和 `/tmp/carleman-h2-closure-main-axioms`。

实际 `result.json` 为 **537 bytes**，SHA256 `208d97d20a5ef53b97a94086b678ac6fded1731f835afababf3b306d617d618b`。内容 PASS，`checked_sha=source_head_sha=4e727b83c3fcb821432ba4089e6f9ea0c9e0a277`，target Carleman，`finished_at=2026-10-19T05:12:37.616996+00:00`，ci_url 为同 run/attempt。远端 Lean 4.35.0 提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 提交与固定 pin 一致。

独立逐字节比较远端 `/tmp/carleman-h2-closure-main-axioms/axioms.txt` 与固定本地副本：**完全相同，2,004,037 bytes，SHA256 `af52869568eec6d15315e484edd2b27cca632ebafa8a3d5051847a2d9e933f0d`**。远端实际末行同样为 6666 项递归审计 PASS。原始结果、完整类型/公理产物和全部 jobs 的最终成功分别核实。

## 验收决定

**C134：PASS，可升级 REVIEWED，scope 保持 AUXILIARY。** 12 项声明的实际对象、几何支撑、强极限、导数尺度、全弱 H² 状态范围、闭包连续性与唯一性均通过独立核查；未发现需要修复的数学缺陷。同 SHA CI 与自行下载原始产物核验通过。

**P011 不提升，原文保持 14/26。** 本次仅新增本报告，未修改实现、root、台账或原稿，未 commit/push。以上签发 UTC 固定；定稿通知主 Agent 后冻结报告及 reviewed_at，不再改动。
