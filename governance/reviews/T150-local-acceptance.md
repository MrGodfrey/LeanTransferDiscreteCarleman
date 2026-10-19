# T150 / C166 独立本机验收：Gaussian 热系数的真实微分展开

- checked_sha / source_sha：`cc5e0b8ad589a03b86766a8c2c5dedc49449ced4`
- mathematical_base：`37d15b168e8c1ac3f313848be5a0c56594d2aad2`
- reviewed_at：`2026-10-19T10:25:27+00:00`
- reviewer：独立本机 Agent `/root/accept_spatial_lemma`，未参与本批实现。
- result：**PASS**；axiom_check：**PASS**；全部 **32/32** 显式声明通过。
- scope：**AUXILIARY — 全空间 C∞ 相位的系数计算准备**。C166 可登记 REVIEWED；**P024 / prop:continuousCE 不提升，原文覆盖保持 17/26**。

本报告从固定 Git 对象读取四模块全部定义和证明、32 项完整展开类型、关键依赖、原稿、MATH_SPEC、T150 分析及台账，并独立查询 GitHub 同 SHA 的最终运行和三个 job，独立下载原始 result/raw 并逐字节比较。执行者自检、规格和 CI 没有替代语义审查。动态 `.ci/axioms.txt`、后续 T151 的 MatrixEnergy / HeatRemainderBound / BLowerBound 草稿均不属于本次依据。仅新增并单独提交本报告，不改数学、根导入、审计、台账或原稿，不 push；签发通知后冻结内容与时间。

## 原文定位与实际范围

固定 `paper/main.tex:2672–2731` 的 Proposition A.3 / `prop:continuousCE` 要求任意 T>0、原 qclass 的 C² 时间权、两种时间方向、全部原周期 H¹(0,T;H)∩L²(0,T;D(A)) 轨道和统一观测估计。本批对应 `2684–2702` 的 ψ、φ、ρ、ℓ、Ψ 选择及 `2711–2718` 在估计之前的系数计算，不是 `eq:heatcross` 不等式本身。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未改稿。

另直接目视核对本地原书 Fu–Lü–Zhang (2019) Corollary 3.1、印刷第 60 页 / PDF 第 69 页的 (3.3)–(3.5)，使用原页图 `/tmp/carleman-fu2019-cor31.png`。在 p^{jk}=δjk、Φ=0 时，A=∇ℓ·∇ℓ−Δℓ−Ψ，k=ℓ_t+A；原 B 正是 k_t+2div(k∇ℓ)+2kΨ。固定 `PointwiseHeatConjugation.lean:64` 另以真实乘积微分展开成原书的 A、ℓ_t 六项，因而本批计算的 B 是同一个原系数。Lean 参数 `p` 在这些接口中代表 Ψ，不代表扩散矩阵 p^{jk}。

时间微分相关结论明确要求 `ContDiff ℝ ∞ q`，一般分离相位还要求空间因子 C∞。这是相对原最终命题更强的正则性，作为当前辅助阶段保留，不能以 `extra_hypotheses=[]` 或已审核状态将它解释为原全允许权族已完成。周期性两项单独以 `Function.Periodic q T` 为前提；点态恒等式不需要周期性、qclass、q 正、λ 正、T 正、空间域或状态前提。它们允许任意实 λ、任意中心、所有时空点及任意自然数维数；没有除以 λ、q、距离或维数，λ=0、q(t)=0 和 d=0 不被暗中排除。

## 全部声明逐项核查

下表路径前缀为 `Carleman/`，行号均指 checked_sha。完整名称及顺序与固定 C166、T150 和 `/tmp/carleman-t150-gaussian-coefficients-declarations.json` 完全一致。四模块均已由固定 `Carleman.lean` 导入，32 项均有 `tools/CheckAxioms.lean` 的 `#check @...` / `#print axioms ...`，并在同次远端 raw 中实际出现。记 s=‖x−c‖²、φ=exp(−λs)、ρ=φ−2、G=∇ρ·∇ρ，以下只是报告缩写，不改变实际声明对象。

| # | 完整声明 | 固定源码位置 | 独立数学核查结论 |
|---|---|---|---|
| 1 | `Carleman.interiorCarlemanProfile_laplacian` | `Weights/InteriorGaussianDifferential.lean:12` | PASS。真实 Hessian 按全部 Euclidean 基向量取迹，得到 Δρ=(4λ²s−2dλ)φ；维数来自完整基数。 |
| 2 | `Carleman.interiorCarlemanProfile_energy` | `Weights/InteriorGaussianDifferential.lean:29` | PASS。实际方向导数逐项平方并求和，G=4λ²φ²s，不是另行定义的代用能量。 |
| 3 | `Carleman.interiorCarlemanProfile_energy_fderiv` | `Weights/InteriorGaussianDifferential.lean:39` | PASS。先证明整个能量函数相等，再对同一函数实际求 fderiv；DG[v]=8λ²φ²(1−2λs)⟨x−c,v⟩。 |
| 4 | `Carleman.interiorCarlemanProfile_laplacian_fderiv` | `Weights/InteriorGaussianDifferential.lean:56` | PASS。真实 Δρ 函数的导数为 [−8λ³s+(4d+8)λ²]φ⟨x−c,v⟩，三阶计算保留维数项。 |
| 5 | `Carleman.interiorCarlemanProfile_energy_pair` | `Weights/InteriorGaussianDifferential.lean:72` | PASS。逐坐标实际 DG 与 Dρ 配对，∇G·∇ρ=32λ⁴φ³s²−16λ³φ³s，所有坐标各计一次。 |
| 6 | `Carleman.interiorCarlemanProfile_gaussian_pair` | `Weights/InteriorGaussianDifferential.lean:90` | PASS。由实际 Dφ=Dρ 逐项得到 ∇φ·∇ρ=G；不以梯度身份作额外前提。 |
| 7 | `Carleman.separableHeatPhase` | `Spatial/SeparableHeatPhase.lean:11` | PASS。实际函数定义为 (t,x)↦q(t)f(x)，无任意导数字段。 |
| 8 | `Carleman.separableHeatPhase_contDiff` | `Spatial/SeparableHeatPhase.lean:14` | PASS。由 fst/snd 的真实复合和乘积规则证明 C∞。 |
| 9 | `Carleman.separableHeatPhase_timeD` | `Spatial/SeparableHeatPhase.lean:19` | PASS。真实时空方向 (1,0) 导数，经时间切片 HasDerivAt 得 q′(t)f(x)。 |
| 10 | `Carleman.separableHeatPhase_spatialD` | `Spatial/SeparableHeatPhase.lean:25` | PASS。真实方向 (0,v) 导数=q(t)Df(x)[v]；求空间导数时 q(t) 固定。 |
| 11 | `Carleman.separableHeatPhase_lap` | `Spatial/SeparableHeatPhase.lean:33` | PASS。对第一方向导数的全函数等式再次微分，得到真实时空空间 Laplacian=q(t)Δf。 |
| 12 | `Carleman.separableHeatPhase_energy` | `Spatial/SeparableHeatPhase.lean:45` | PASS。实际方向导数平方和=q(t)²∇f·∇f，无 q 正性需求。 |
| 13 | `Carleman.separableHeatPhase_pair` | `Spatial/SeparableHeatPhase.lean:52` | PASS。两个独立时间因子和空间因子的真实配对等于 q(t)r(t)∇f·∇g。 |
| 14 | `Carleman.directionalPair_add_left` | `Spatial/SeparableHeatPhase.lean:64` | PASS。左侧真实 C∞ 函数导数可加；右侧 z 可任意，因为这里只对其已有 fderiv 值作代数运算。 |
| 15 | `Carleman.directionalPair_const_mul_left` | `Spatial/SeparableHeatPhase.lean:70` | PASS。左侧实际常数倍导数给配对齐次性，未要求无关的右因子正则性。 |
| 16 | `Carleman.interiorGaussianHeatPhase` | `Weights/InteriorHeatCoefficients.lean:13` | PASS。同一实际 L=qρ，空间因子调用既有原 Gaussian profile。 |
| 17 | `Carleman.interiorGaussianHeatPsi` | `Weights/InteriorHeatCoefficients.lean:17` | PASS。定义使用同一 L 的实际空间 Laplacian：Ψ=−ΔL−8λqφ。 |
| 18 | `Carleman.interiorGaussianHeatPhase_contDiff` | `Weights/InteriorHeatCoefficients.lean:22` | PASS。q C∞ 和已证明的 ρ C∞ 内部供应实际 L C∞。 |
| 19 | `Carleman.interiorGaussianHeatPsi_contDiff` | `Weights/InteriorHeatCoefficients.lean:27` | PASS。对真实 ΔL 的光滑性和真实分离乘积闭包证明 Ψ C∞。 |
| 20 | `Carleman.interiorGaussianHeatPhase_periodic` | `Weights/InteriorHeatCoefficients.lean:33` | PASS。原 q 的周期性直接给 L 对时空平移 (T,0) 的函数周期性。 |
| 21 | `Carleman.interiorGaussianHeatPsi_periodic` | `Weights/InteriorHeatCoefficients.lean:40` | PASS。真实 fderiv 平移相容与 ΔL 的周期性给 Ψ 周期性；未把导数端点相等另作假设。 |
| 22 | `Carleman.interiorGaussianHeatPsi_formula` | `Weights/InteriorHeatCoefficients.lean:48` | PASS。实际定义展开为 q[−4λ²s+(2d−8)λ]φ，符号和维数正确。 |
| 23 | `Carleman.interiorGaussianHeatPsi_eq_spatial` | `Weights/InteriorHeatCoefficients.lean:59` | PASS。通过真实时空 Laplacian 与空间切片 Laplacian 身份，严格等于 T144 的 `interiorHeatPsi c λ (q t) x`。 |
| 24 | `Carleman.interiorGaussianHeatK_formula` | `Weights/InteriorHeatCoefficients.lean:68` | PASS。同一原 `heatConjugationK` 内 ΔL 与 Ψ 消去，k=q′ρ+q²G+8λqφ。 |
| 25 | `Carleman.interiorGaussianHeatK_explicit` | `Weights/InteriorHeatCoefficients.lean:81` | PASS。仅代入真实 G，得到 k=q′ρ+4q²λ²φ²s+8λqφ。 |
| 26 | `Carleman.interiorGaussianHeatPsi_spatialD` | `Weights/InteriorHeatCoefficients.lean:91` | PASS。实际空间 fderiv 给 q[8λ³s+(8−4d)λ²]φ⟨x−c,v⟩；没有丢弃维数项。 |
| 27 | `Carleman.interiorGaussianHeatPsi_energy` | `Weights/InteriorHeatCoefficients.lean:108` | PASS。真实全部方向导数平方和为 q²[8λ³s+(8−4d)λ²]²φ²s。 |
| 28 | `Carleman.pointwiseHeatB_lap_cancel` | `Weights/InteriorHeatB.lean:11` | PASS。任意真实 C∞ L/k 和修正函数 r 下，原 B 在 Ψ=−ΔL−r 时等于 k_t+2∇k·∇L−2kr，来源为实际乘积微分。 |
| 29 | `Carleman.interiorGaussianHeatK_timeD` | `Weights/InteriorHeatB.lean:20` | PASS。实际同一 k 的时间导数=q″ρ+2qq′G+8λq′φ；q′ C∞ 和 (q²)′=2qq′ 内部证明。 |
| 30 | `Carleman.interiorGaussianHeatK_pair` | `Weights/InteriorHeatB.lean:52` | PASS。实际 ∇k·∇L=qq′G+q³∇G·∇ρ+8λq²G；没有给 k 另配独立空间导数。 |
| 31 | `Carleman.interiorGaussianHeatB_formula` | `Weights/InteriorHeatB.lean:91` | PASS。代入第 28–30 项和真实空间导数，完整展开三次、二次、q′、q″ 四类项，包含全部负项。 |
| 32 | `Carleman.interiorGaussianHeatB_leading` | `Weights/InteriorHeatB.lean:116` | PASS。用实际 Riesz 梯度范数平方 g=4s 将同一 B 改写为 4q³λ³φ³g(λg−6) 加完整余项；不是假定 g 或删掉低阶项。 |

## 核心推导、符号和统一性

真实空间微分的逻辑是先用 T144 的 HasFDerivAt / Hessian，按 Euclidean 正交基计算 Δρ 和 G，再以完整函数相等替换到 fderiv 内；对 φ²、‖x−c‖² 的乘积执行 HasFDerivAt 规则。它既未把逐点等式误当邻域等式，也没有将微分预先指定为期望的多项式。每个平方和都用 `EuclideanSpace.real_norm_sq_eq`，维数 d 来自真实全部坐标，d=0 的空和也相容。

分离相位的二阶空间公式先对每个方向证明全时空第一导数函数等式，再用 `smoothD_contDiff` 对同一第一导数求导。`interiorGaussianHeatK_timeD` 也先构造全函数恒等式 k=separable(q′,ρ)+separable(q²,G)+8λseparable(q,φ)，而不是只在固定点替换后求导。`deriv q` 的 C∞ 来自真实一维 `smoothD`，q² 的导数由 HasDerivAt.pow 得到；两个时间阶均是真正 `deriv`。

原 B 的抵消可以独立复算为

```text
B = k_t + 2 div(k∇L) + 2kΨ
  = k_t + 2∇k·∇L − 16λqφk,
k = q′ρ + q²G + 8λqφ,
k_t = q″ρ + 2qq′G + 8λq′φ,
∇k·∇L = qq′G + q³(32λ⁴φ³s²−16λ³φ³s) + 8λq²G.
```

因此三次项为 `64q³λ⁴φ³s²−96q³λ³φ³s`，二次项为 `q²(64λ³φ²s−128λ²φ²)`，时间项为 `q′(16qλ²φ²s+8λφ−16λqφρ)+q″ρ`。以真实 `g=‖gradient (interiorQuadratic c) x‖²=4s` 代入，三次项严格为 `4q³λ³φ³g(λg−6)`。所有项均与实际 `pointwiseHeatB` 同一对象相等。常数 6 与 λ、q、T、维数无关，没有隐藏的目标界或选参前提。

维数只在特定的 ΔL / Ψ 组合中抵消；Ψ 的实际空间导数仍含 `(8−4d)λ²`，其平方和保持完整。后续对 `−2z∇Ψ·∇z` 作 Young 估计时不能忽略这部分。**本报告的 6 是精确 B 恒等式的系数，不等于已经证明原 heatcross 中完成混合项估计后的统一 C。** 本批没有证明任何时空积分下界、qclass 余项界、λ/β/q_c 选择或最终观察估计；因此也没有将成员资格常数、空间光滑性或计算恒等式冒充最终 T 统一性。

## 固定依赖闭包

按固定 `public import` / `import` 递归检查四模块共有 **91** 个 Carleman 源文件，其中 **87** 个既有文件与 mathematical_base 逐字节相同。对正式依赖另按各自已验收声明版本检查完整源闭包：

| 依赖 | 已验收版本 | 本次复核 |
|---|---|---|
| C160 / T144，实际 Gaussian / Hessian / 梯度及空间 Ψ | `2cd92104c803b6a2e586be26a9685e4b2c7fc976` | `InteriorHeatMatrix.lean` 的 81 文件闭包全相同；重新核对真实梯度、Hessian 及 Ψ 定义，正确供本批取迹、求导、真实 g 和空间身份。见 [T144 报告](T144-local-acceptance.md)。 |
| C161 / T145，实际方向微分、时空桥、原 k/B | `ccbd7a887ed37afbc4d4e530d06b885350e74b3a` | `SpacetimeHeatIdentity.lean` 的 81 文件闭包全相同；实际 `smoothD=fderiv`、空间方向、乘积散度与原书 B 展开直接核查，调用时光滑前提均内部供应。见 [T145 报告](T145-local-acceptance.md)。 |
| C162 / T146，真实周期导数 | `c598090a2e592f2e2a5441e5d05eaec994e9b1b3` | `PeriodicHeatFlux.lean` 的 82 文件闭包全相同；`fderiv_comp_add_right` 从全函数周期性推导导数周期性，本批 ΔL 周期调用正确。见 [T146 报告](T146-local-acceptance.md)。 |

已读取基线 [T149 报告](T149-local-acceptance.md)，其真实光滑盒积分不等式可供下一阶段连接，但它不是本批四模块的直接数学依赖，也未由本批再次实例化并估计。T150 的点态 B 与 T149 使用的 `pointwiseHeatB` 定义相同；从这点到可积分的最终权下界仍有实质证明义务。

## 构建、公理与独立远端证据

本机固定 `/tmp/carleman-t150-gaussian-coefficients-build.log` 记录根目标 **4012 jobs** 成功；`/tmp/carleman-t150-heat-B-final-target2.log` 记录定向 **3238 jobs** 成功。本次不重新构建变动中的工作树。实际 Lean 4.35.0，CI 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；固定 manifest、实际 mathlib checkout 与远端 result 一致为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

独立通过 GitHub API 读取 [main CI run 39236637373 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39236637373/attempts/1)：head 为 checked_sha，主分支 main，run 最终 `completed/success`。三个实际 job 均是该 SHA：

| job | 实际 ID | 最终结论 | completed_at UTC |
|---|---|---|---|
| state-check | `118007189211` | completed / success | `2026-10-19T10:19:42Z` |
| lean | `118007189478` | completed / success | `2026-10-19T10:22:48Z` |
| dashboard / snapshot | `118008496401` | completed / success | `2026-10-19T10:22:58Z` |

由本 Agent 分别执行 `gh run download 39236637373 --name lean-ci-result` 和 `--name lean-declaration-evidence`，下载到独立约定目录；实际 API 工件所属 run、main 和 head 均一致，均未过期：

- `lean-ci-result` artifact **12178703807**（API 压缩大小 493 bytes）。原始文件 `/tmp/carleman-t150-gaussian-coefficients-main-ci/result.json`：**537 bytes**，SHA256 **`88e03d8fb64458e7ed5772b813e57ec514606b07038ab15f1437f62594362c99`**；实际 `status=PASS`，`checked_sha=source_head_sha=cc5e0b8ad589a03b86766a8c2c5dedc49449ced4`，`targets=[Carleman]`，`finished_at=2026-10-19T10:21:41.810870+00:00`。result 的生成早于 job 结束；验收以已查询到的三个最终成功结论为准。
- `lean-declaration-evidence` artifact **12178743753**（API 压缩大小 215461 bytes）。原始 `/tmp/carleman-t150-gaussian-coefficients-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t150-gaussian-coefficients-local-axioms.txt` **逐字节完全一致**：**2322819 bytes**，SHA256 **`0cac9584b0f3a9f9d43f52e43e9e2a0e480d1627147875e6155b5ec0805412b8`**。

实际 raw 中 32 项各只有 `propext`、`Classical.choice`、`Quot.sound`。全部显式打印记录为 2794 条标准基础公理依赖和 9 条无公理记录，未发现其它公理；这个打印数量不冒充递归全库数量。末尾实际输出 `Axiom audit passed for all 7530 Carleman declarations.`；已核对固定审计器确实枚举全部 Carleman 常量（含 privateToUserName）并执行 `collectAxioms`，白名单仅上述三项。本批源码无 sorry / admit / 新增 axiom，32 项无未清偿占位。

## 签发结论与未完成边界

**32/32 PASS，无阻断本批 AUXILIARY 验收的数学缺陷。** 原 Gaussian 的真实 Laplacian、能量、三阶系数导数、分离相位、同一 L/Ψ/k/B、周期性、准确维数项和完整时间余项均已核对，公理与固定版本证据通过。

本结论只允许将 C166 记为 REVIEWED / AUXILIARY。尚未完成原 C² q 的全允许权族、qclass 下统一余项和混合项 Young、矩阵/观测吸收、一般凸多面体的弱 Green 步骤、原全部 Sobolev 轨道密度以及两方向最终 CE。不得以精确主项或已存在的光滑盒积分辅助结果提升 P024；原文计数保持 17/26。报告及 `reviewed_at` 在签发通知后固定。
