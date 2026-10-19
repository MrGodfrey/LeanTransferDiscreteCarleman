# T151 / C167 独立本机验收

- `checked_sha`: `8e740040ffe3ce75cb89b5868d5998b5ad8cd74c`
- `base_commit`: `cc5e0b8ad589a03b86766a8c2c5dedc49449ced4`
- `reviewed_at`: `2026-10-19T10:32:51+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：实际 Gaussian 热权的矩阵、完整 B 余项、真实 Ψ 梯度 Young 界和同一 bulk 的统一下界，及全空间 C∞ 周期盒状态上的原形状 heatcross。**P024 / prop:continuousCE 不提升，原文覆盖保持 17/26。**

本 Agent 直接读取固定 Git 对象中八模块全部证明、15 项公开声明完整展开类型及私有有限矩阵求和引理，核对原 `paper/main.tex:2672–2731`、原 qclass、T151 分析、MATH_SPEC、C167/T151 清单和关键依赖。AGENTS、PROJECT_OPERATIONS、state/README 与本 Agent 已读固定协议逐字节相同。独立查询同 SHA 正式 CI、自行下载原始工件后逐字节比较。执行者说明、历史验收和 CI 未替代数学判断；后续 T152 草稿及动态 `.ci/axioms.txt` 排除。

## 原稿对应与范围

本批直接对应原 `2706–2721` 的矩阵表达式、Young 控制及 `eq:heatcross`，并复用已证明的周期时间通量消失和盒域空间通量非正。原几何权仍是 ψ=−‖x−c‖²、φ=exp(λψ)、ρ=φ−2，L=qρ；p 是原 Ψ=−ΔL−8qλφ，k=Lₜ+|∇L|²−ΔL−Ψ。它们由同一实际相位定义，未外给任意系数来替代原权。

最终输入为任意正维正坐标盒、内部中心 c、任意 λ>0，以及全空间 C∞ 的 q 和 u、真实周期性、原 frontier 上全部时间的逐点零边值。原 qclass 的实际界 |q′|≤βq²、|q″|≤β²q³ 与 q≥1 在 Icc(0,T) 上逐点使用。β 只要求非负，未收紧成 β≤1；q_c 和 q_max 未出现在条件或常数中，因为此阶段只需 q≥1，省去未用上/下界是加强这一辅助结论。

当前 C∞ 全局周期输入比原 C²([0,T]) 时间权、端点匹配及完整 Sobolev 轨道更强；一般多面体、低正则 Green、观察区域吸收、从 z 返回 u、密度和反向时间结论仍待。本批仅在此明确辅助范围内 PASS，不能提升完整 P024。

## 全部 15 项公开声明

名称省略 `Carleman.`；源码位置相对于该目录。源行来自固定提交，完整类型行来自本次独立下载的原始 `axioms.txt`。顺序与固定台账两处及交付清单相同。

| # | 声明 | 固定源位置 / 完整类型行 | 独立结论 |
|---|---|---|---|
| 1 | `interiorGaussianHeatPhase_second_spatialD` | `Weights/InteriorHeatMatrixEnergy.lean:11` / 30326 | PASS；真实相位的两次空间 Fréchet 方向微分，按任意 v、w 给出实际 Gaussian Hessian。 |
| 2 | `interiorGaussianHeatMatrixEnergy_formula` | `Weights/InteriorHeatMatrixEnergy.lean:40` / 30334 | PASS；实际矩阵二次型精确为 4qλφE 加 8qλ²φ 的径向平方；使用同一 Ψ。 |
| 3 | `interiorGaussianHeatMatrixEnergy_coercive` | `Weights/InteriorHeatMatrixEnergy.lean:72` / 30344 | PASS；q≥0 时仅去掉非负径向平方，未将矩阵强制性作为输入。 |
| 4 | `heat_remainder_bound` | `Weights/HeatRemainderBound.lean:9` / 30354 | PASS；全部 Q²、Q₁、Q₂ 余项以 2K[Q²+(β+β²)Q³] 控制，使用 Q≥1、β≥0，不加 β≤1。 |
| 5 | `interiorHeatLeadingCoefficient` | `Weights/InteriorHeatBLowerBound.lean:12` / 30364 | PASS；定义真实 4Q³λ³φ³g(λg−6)，g=实际 ‖gradient ψ‖²；不宣称它处处非负。 |
| 6 | `interiorGaussianHeatB_uniform_lower_bound` | `Weights/InteriorHeatBLowerBound.lean:17` / 30367 | PASS；实际 B 展开的四个空间系数在紧闭包内部统一有界，C 先于 q、β、t、x。 |
| 7 | `directionalEnergy_nonneg` | `Spatial/DirectionalYoung.lean:12` / 30389 | PASS；真实有限方向导数平方和非负。 |
| 8 | `directionalPair_young` | `Spatial/DirectionalYoung.lean:15` / 30392 | PASS；有限个真实平方求和证明 Young；正 a 和实际 Ψ 能量界给正确交叉项方向。 |
| 9 | `interiorGaussianHeatPsi_uniform_energy_bound` | `Weights/InteriorHeatMixedTerm.lean:13` / 30398 | PASS；以实际 Ψ 梯度能量公式及空间紧集界供应 Cq²·(qλφ)，λ>0、q≥1 的用途准确。 |
| 10 | `interiorGaussianHeat_mixed_term_bound` | `Weights/InteriorHeatMixedTerm.lean:48` / 30413 | PASS；取 a=qλφ>0 后由前两项内部证明真实 2〈∇Ψ,∇z〉z≤qλφE+Cq²z²。 |
| 11 | `interiorGaussianHeat_bulk_lower_bound` | `Weights/InteriorHeatBulkLowerBound.lean:15` / 30432 | PASS；在同一实际 bulk 中组合矩阵、完整 B 和混合项，保留有符号主项得到 4qλφE 下界。 |
| 12 | `boxTimeIntegral_const_mul` | `Spatial/BoxTimeIntegralOrder.lean:11` / 30456 | PASS；真实柱域受限乘积测度上的实常数积分线性。 |
| 13 | `boxTimeIntegral_mono_on` | `Spatial/BoxTimeIntegralOrder.lean:16` / 30459 | PASS；只在实际柱体内要求点态比较；两个实际函数的可积性由紧柱连续性内部供应。 |
| 14 | `interiorHeatLeadingCoefficient_continuous` | `Spatial/BoxGaussianHeatCross.lean:15` / 30465 | PASS；用真实 g=4‖x−c‖² 身份证明主系数在时空连续；不需要其符号。 |
| 15 | `box_smooth_gaussian_heat_cross` | `Spatial/BoxGaussianHeatCross.lean:22` / 30468 | PASS；内部设置 L=qρ、z=exp(L)u、原 Ψ/k，对同一 bulk 积分并除4，主项常数6、残差1/4，C 先于全部 T/q/β/u。 |

另独立读完 `InteriorHeatMatrixEnergy.lean` 的私有 `finite_radial_matrix`：逐项分离秩一双和与 Kronecker 对角和，真实有限和重排得 A(Σrᵢvᵢ)²−BΣvᵢ²；没有使用矩阵结论作为假设。该私有声明虽不列入15项公开清单，仍受全环境递归公理审计覆盖。

## 实际矩阵与完整 B 余项

真实 Hessian 为 q[4λ²φ〈x−c,v〉〈x−c,w〉−2λφ〈w,v〉]。将空间标准基代入，同一 Ψ 与 ΔL 相消，得到原 c 二次型

c[∇z,∇z]=4qλφE+8qλ²φ(Σᵢ(x−c)ᵢDᵢz)²，E=Σᵢ(Dᵢz)²。

这正是原 4qλφ Id+2qλ²φ∇ψ⊗∇ψ 的收缩，因为 ∇ψ=−2(x−c)。径向平方的非负性只需 q≥0 和 φ>0；本辅助强制性引理允许任意实 λ，其较广范围不影响最终 λ>0 情形。原 bulk 中另有外层 **2c**，没有漏掉该系数。

已直接重读固定 `InteriorHeatB` 的实际导数与精确展开。记 r²=‖x−c‖²、g=‖gradient ψ‖²=4r²，完整 B 为

B=4q³λ³φ³g(λg−6)+q²A₂+q′(qA₁+A₀)+q″ρ，

其中 A₂=64λ³φ²r²−128λ²φ²，A₁=16λ²φ²r²−16λφρ，A₀=8λφ。所有 q² 项、两个 q′ 系数和 q″ρ 都保留；主项常数 **6** 来自真实导数精确化简，不是依赖 λ 的未知常数。

对固定有界 S、c、λ，构造连续函数 H=|A₂|+|A₁|+|A₀|+|ρ|，在实际紧闭包上取界，再置 K=|K₀|+1>0。这个 K 在 q、β、t、状态之前选定，即使 S 为空也可取正界；不输入任何关于解或时间的统一支配函数。标量引理使用 q≥1 得 |qA₁+A₀|≤2Kq，再逐项得到 Kq²、2Kβq³、Kβ²q³，最终由 2K[q²+(β+β²)q³] 控制。取绝对值下界给 B≥主项−余项，无错误改变符号或 β 的幂次。

## Ψ 的真实梯度与 Young 界

已核对实际空间微分得到

|∇Ψ|²=q²φ²[8λ³r²+(8−4n)λ²]²r²，

n 为实际空间维数。定义 P=8λ³r²+(8−4n)λ² 和 H=φP²r²/λ。λ>0 保证除法合法，固定空间紧闭包上的连续界给 H≤C；实际能量恒等式为 |∇Ψ|²=q²λφH。再用 q≥1 得 |∇Ψ|²≤(Cq²)(qλφ)。C 只依赖固定空间数据和 λ，先于 q、t、z。

`directionalPair_young` 不是输入任意梯度数组的假定结论：它对实际 fderiv 方向值求和 Σᵢ(aDᵢz−DᵢΨ·z)²≥0，结合实际能量界 |∇Ψ|²≤Ca 和 a>0 得 2〈∇Ψ,∇z〉z≤aE+Cz²。本次代入 a=qλφ>0、C→Cq²，得到所需混合项界；无需任何 z 正负假设。该代数引理及部分点态辅助项允许任意 z，最终积分入口内部供应同一 z 的 C∞，没有把缺少可微性的任意 z 当作原弱轨道证明。

## 同一 bulk、符号与最终系数

实际 `heatCarlemanBulk` 是 (Δz+kz)²+2c[∇z,∇z]−2〈∇Ψ,∇z〉z+Bz²。由矩阵下界提供 8qλφE，Young 最多扣除 qλφE，因此在余项之外至少剩 **7qλφE**。代码用 E≥0、q≥1、λ>0、φ>0 合法放宽到 **4qλφE**，并用 [q²+(β+β²)q³]≥q² 合并 C₁、C₂。丢掉的只有已证明非负的平方及梯度余量。

特别核对有符号项 g(λg−6)z²：它在靠近中心的区域可能为负，本批没有假定 λg≥6、没有取绝对值后冒充正主项，也没有在单调积分时把它删除。点态下界和最终积分中始终保留完全相同的主项。这也是后续观察区分解与吸收仍待的实质原因。

最终令 G=qλφE、A=q³λ³φ³g(λg−6)z²、W=[q²+(β+β²)q³]z²。点态结论是 4(G+A)≤bulk+KW；积分后结合已验收且实际重读的 ∫bulk≤∫|exp(L)(∂ₜ−Δ)u|²，除以正数4得到

∫G+∫A≤(1/4)∫|exp(L)(∂ₜ−Δ)u|²+(K/4)∫W。

因此最终主项中的 **6** 与残差系数 **1/4** 都独立于 λ、β、T；余项常数为正 C=K/4，可依赖固定维数、盒、中心与 λ。若写成原稿共用的未知 C 形式，可增大数值常数，所示具体估计更精确。未把 C(λ) 的 λ 依赖隐藏到主项常数中。

## 真实柱积分、统一量词和边界范围

`boxTimeIntegral` 是真实 (volume.restrict Icc(0,T))×(volume.restrict Ω) 上的 Bochner 积分。`boxTimeIntegral_mono_on` 只在这一柱域中使用实际点态不等式，先由紧时间区间×闭盒的连续性给两个函数真实可积，再通过 Measure.prod_restrict 和 setIntegral_mono_on 比较。它不要求界在空间域外或时间段外成立，也不依赖不可积函数默认积分值。

主系数即使有符号仍连续；代码内部分别证明 G、A、W、bulk 连续，所有加法和常数积分拆分均有真实可积性。已重读依赖的 Fubini、周期导数积分消失、同一空间通量非正以及 bulk 定义。原 q、L、Ψ、k、u、z 的周期性与实际导数关系匹配；没有用另一个通量或另一个权的积分界拼接。

完整展开类型为：固定 d、a、b、c、λ>0 后，先 ∃C>0，再 ∀T≥0、∀q、∀β≥0、∀u。所有 q′、q″ 和 q≥1 条件仅在 Icc(0,T) 上要求；T=0 亦包含且体积分退化为零。积分入口的空间维数为 d+1，覆盖一维及所有正维盒。常数不依赖 T、q、β、q_c、q_max、状态或网格。没有声称对原完整低正则权族和两时间方向已完成统一 CE。

## 固定依赖、公理和构建

八模块公开声明数 3+1+2+2+2+1+2+2=15，全部由固定 `Carleman.lean` 导入、在固定 `tools/CheckAxioms.lean` 中有完整类型及公理记录。所有公开定义/定理与清单及 C167/T151 台账一致；另一个私有引理已实际读证明。新模块未出现 sorry、admit、新数学 axiom 或 native_decide。

递归 Carleman import 闭包共 **119** 模块，其中 **111** 个旧模块均与基线逐字节相同。`InteriorHeatB` 的 **91** 模块闭包与 C166 的基线已验收版本完全相同；`BoxIntegratedHeatIdentity` 的 **106** 模块闭包与 C165 的 `37d15b168e8c1ac3f313848be5a0c56594d2aad2` 完全相同。关键实际 B/Ψ/K 导数、热 bulk、柱测度和积分衔接已独立重读；旧验收仅供版本追溯，见 [T150](T150-local-acceptance.md)、[T149](T149-local-acceptance.md)。

Lean pin 为 4.35.0；mathlib pin 与本机实际 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，依赖工作树干净。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。实际读取定向 `/tmp/carleman-t151-heat-cross-target2.log`：3280 jobs 成功；`/tmp/carleman-t151-gaussian-heat-cross-build.log`：4020 jobs 成功；`-axioms.log`：7550 全量递归声明审计成功。

审计主体与基线相同，按 privateToUserName 遍历全部 Carleman 环境常量并递归 collectAxioms，只容许 propext、Classical.choice、Quot.sound；私有有限矩阵引理也被覆盖。原始产物实报 **7550** 项递归 PASS；另有 2809 条非空公理打印记录和 9 条无公理打印记录，未混同两种计数。15 项公开声明均有实际类型和正常基础公理记录。

## 独立正式 CI 与原始工件

本 Agent 实际查询 [main CI run 39237769364 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39237769364/attempts/1)：event=push、head_branch=main、head_sha=`8e740040ffe3ce75cb89b5868d5998b5ad8cd74c`，顶层 completed/success，updated_at=`2026-10-19T10:32:23Z`。三项 job 均 completed/success：

| job | 实际 ID | 最终结果 |
|---|---:|---|
| state-check | 118010927316 | success |
| lean | 118010927477 | success |
| dashboard / snapshot | 118012192379 | success |

本 Agent 从同 run 独立 gh run download 两份原始工件，两个下载进程 exit 0；实际 artifact 元数据均绑定同 SHA：

| 工件 | 实际 artifact ID | 归档 bytes | 归档 SHA256 |
|---|---:|---:|---|
| lean-ci-result | 12180610040 | 493 | `5da056f16af1f5ef24b99c3456c21e119083b4afa45ead9f959926d0f98376a0` |
| lean-declaration-evidence | 12180185808 | 216706 | `8bf9f50a2b7cde7e9d9edcee61587398e381dc2c4a224caebaddf5e2afff25e6` |

实际读取 `/tmp/carleman-t151-gaussian-heat-cross-main-ci/result.json`：status=PASS；checked_sha 与 source_head_sha 均等于本报告固定 SHA；ci_url 为同 run/attempt；finished_at=`2026-10-19T10:31:13.489150+00:00`；targets=[Carleman]；Linux Lean 4.35.0 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 与上述 pin 一致。

实际下载 `/tmp/carleman-t151-gaussian-heat-cross-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t151-gaussian-heat-cross-local-axioms.txt` **逐字节相同**，均 **2335115 bytes**，原始 SHA256 **`986062c9e4600c5ca094723a3d13273c5dc8cba84ab415126b288ed14ff95628`**。原始文件 hash 与 ZIP 归档 hash 分开记录；远端 raw 含全部15项完整类型及7550项递归公理 PASS。

## 签发结论

**T151 / C167 可在该固定版本登记为 REVIEWED，scope 保持 AUXILIARY。** 本批15项公开声明及私有辅助证明的语义、公理和证据均 PASS，未发现需修复缺陷。仍需观察区吸收、从 z 返回 u、原 C² 时间权和全部弱轨道的恢复、一般多面体 Green 与时间反射；不得提升完整 P024。原文覆盖保持17/26。定稿后冻结内容与 reviewed_at，仅提交报告，不改数学、台账、root/audit 或原稿，不推送。
