# T163 / C179 独立本机验收：真实弱梯度与加权热能量连续性

- checked_sha / source_sha: `61ddd47f394ef2a5c61e3ccc317ace118ab816b5`
- mathematical_base: `5ec78c3027e714324439187119dfbfe4765a2af6`
- reviewed_at: `2026-10-19T12:23:07+00:00`
- reviewer: 独立本机 Agent `/root/accept_spatial_foundations`
- result: **PASS**；axiom_check: **PASS**；scope: **AUXILIARY**。
- 五模块十八项声明通过固定版本验收。C179 可以升级为 REVIEWED 并保持 AUXILIARY；最终传递引理的光滑 core 估计 `hCE` 仍是显式前提，P024 / 完整弱连续 CE 不提升，原文完整结果覆盖保持 **17/26**。

## 原文、实际对象和范围

逐项读取固定 Git 对象中的五模块、十八项完整展开类型、真实证明与关键旧依赖，对照原 `paper/main.tex:2672–2675` 的全部弱周期状态、双方向及指数 `(3,1;3)`，以及 `2696–2730` 从光滑热估计到弱状态的密度步骤。原命题要求实际 `ε∂t−Δ` 残差、原空间梯度和真实观察区域。本批构造并识别原周期图的能量/梯度字段，证明相应四项 Bochner 加权能量连续，并证明保持同一常数的密度传递。它尚未用原光滑柱积分估计清偿传递前提。

已读取固定 `governance/analysis/T163-weak-heat-continuity.md`、`governance/MATH_SPEC.md` 对应段、C179 台账及声明清单，遵循根 AGENTS 和适用治理协议。规格与 CI 不代替数学核验。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未修改。未来工作树的 BochnerBoxIntegral 等增量及动态 `.ci/axioms.txt` 均排除。

## 十八项声明逐项验收

下表位置全部指 checked_sha，顺序与固定 `/tmp/carleman-t163-weak-heat-continuity-declarations.json` 和 C179 的 `lean_declarations` 一致。五模块均在固定 `Carleman.lean` 导入，十八项均在固定 `tools/CheckAxioms.lean` 审计；已逐项读取完整展开类型。

| # | 显式声明 | 固定源码位置 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.SpatialProfile.weightedTimeCLM` | `Carleman/Spatial/WeightedTimeContinuity.lean:13` | PASS。用真实 timeMap 及其实际范数界构造嵌套 Bochner L² 上的 CLM，未替换为空间抽象范数族。 |
| 2 | `Carleman.SpatialProfile.timeSq_eq_weightedTimeCLM_norm_sq` | `Carleman/Spatial/WeightedTimeContinuity.lean:18` | PASS。任意实指数 s 的原 timeSq 精确等于同一加权映射指数 `τ+s/2` 的范数平方，所有可积性由原 MemLp 映射保证。 |
| 3 | `Carleman.SpatialProfile.continuous_timeSq` | `Carleman/Spatial/WeightedTimeContinuity.lean:24` | PASS。固定权且 q a.e. 强可测时，由真实 CLM 范数平方得到连续性；不要求 q 光滑。 |
| 4 | `Carleman.CoerciveForm.periodicEnergy` | `Carleman/Continuous/PeriodicEnergyField.lean:14` | PASS。实际 `resolventEnergy(1)` 的 Bochner CLM 作用于原 A 字段与值字段之和，输出原能量空间 V 的 L² 字段。 |
| 5 | `Carleman.CoerciveForm.periodicEnergy_eq` | `Carleman/Continuous/PeriodicEnergyField.lean:18` | PASS。定义上就是原 timeEnergy 对同一 pathL2 和 A 字段的构造。 |
| 6 | `Carleman.CoerciveForm.periodicEnergy_embed` | `Carleman/Continuous/PeriodicEnergyField.lean:21` | PASS。原时间算子图关系内部给能量字段嵌回恰为原 pathL2，无附加能量代表假设。 |
| 7 | `Carleman.CoerciveForm.periodicEnergy_embed_ae` | `Carleman/Continuous/PeriodicEnergyField.lean:25` | PASS。真实 compLp 代表身份给正确方向的时间 a.e. 嵌入等式。 |
| 8 | `Carleman.SpatialTest.sobolevJet_component_ae` | `Carleman/Spatial/SmoothWeakGradientIdentity.lean:13` | PASS。原实际 SpatialTest H¹ jet 的各一阶分量等于其 Fréchet 导数作用于对应欧氏基向量。 |
| 9 | `Carleman.WeakSobolevJet.component_eq_smooth_derivative` | `Carleman/Spatial/SmoothWeakGradientIdentity.lean:25` | PASS。任意有界开域的原弱 H¹ jet 与同值 C∞ 函数，通过真实紧支截断和弱 jet 唯一性识别全部一阶坐标导数。 |
| 10 | `Carleman.WeakSobolevJet.gradient_norm_sq_eq_smooth` | `Carleman/Spatial/SmoothWeakGradientIdentity.lean:52` | PASS。实际 DerivativeFiber 的全部分量平方和经 `Sym.oneEquiv` 精确等于经典 gradient 范数平方，系数为 1。 |
| 11 | `Carleman.dirichletPeriodicGradient` | `Carleman/Spatial/DirichletPeriodicGradient.lean:16` | PASS。原 dirichletGradient 的真实 Bochner CLM 复合 periodicEnergy，得到完整周期图上的连续弱梯度字段。 |
| 12 | `Carleman.dirichletPeriodicGradient_ae` | `Carleman/Spatial/DirichletPeriodicGradient.lean:22` | PASS。时间 a.e. 的嵌套 Lp 代表正是原能量元素的真实弱梯度。 |
| 13 | `Carleman.dirichletPeriodicGradient_smooth_norm` | `Carleman/Spatial/DirichletPeriodicGradient.lean:28` | PASS。以同一个 F 的闭区间每时刻迹身份，得到时间 a.e./空间 a.e. 的真实弱梯度平方与 F 空间梯度平方相等。 |
| 14 | `Carleman.dirichletHeatLeft` | `Carleman/Spatial/DirichletHeatContinuity.lean:18` | PASS。定义原 q³ 加权值项与 q 加权弱梯度项之和；梯度在乘权之前，未改成共轭梯度。 |
| 15 | `Carleman.dirichletHeatRight` | `Carleman/Spatial/DirichletHeatContinuity.lean:23` | PASS。定义真实 `ε·weak_dtime+actual_A` 的零次 q 残差项，以及原 q³ 观察 cutoff 值项。 |
| 16 | `Carleman.continuous_dirichletHeatLeft` | `Carleman/Spatial/DirichletHeatContinuity.lean:29` | PASS。值字段与实际弱梯度的 CLM 连续性复合第 3 项，给完整原图上的连续性。 |
| 17 | `Carleman.continuous_dirichletHeatRight` | `Carleman/Spatial/DirichletHeatContinuity.lean:36` | PASS。残差和观察限制均为真实 CLM；只要求 W 可测，不要求示性函数连续或观察边界零测。 |
| 18 | `Carleman.box_dirichletHeat_le_of_classical` | `Carleman/Spatial/DirichletHeatContinuity.lean:47` | PASS。明确以全部 classicalDirichletTimeCore 上的同一个 C 估计为前提，利用完整图稠密性与闭不等式集延拓到任意原 p，参数与 C 不变。 |

## 实际能量字段与原算子图

固定 `PeriodicGraph` 的字段为真实连续 H 迹、弱时间导数 L² 类和原 associated operator 的 L² 类，其范数为连续迹一致范数与两个 L² 范数的乘积最大范数。原 a.e. 时间算子图通过真实 resolvent 等式刻画，未把任意命名字段当作 Au。第 4 项取

`E(p) = resolventEnergy(1).compLp (p.operator + pathL2(p.trace))`。

这是实际 V 值 Bochner 类；V 的完备性来自原 CoerciveForm 能量空间。其连续性由原连续 resolvent、两个原图字段的 CLM 和 compLpL 复合提供。固定 `FormEnergyClass.timeEnergy_embed` 在原 `(u,a)∈timeOperatorGraph` 条件下使用实际 `resolventH(a+u)=u`，故第 6 项输出恰是同一个 u，而不是某个近似或较小状态类。

实际读取了 `FormEnergyClass`、`DirichletForm` 及 `Section3/OriginalForm`。DirichletEnergy 是原 H¹₀ 值空间的完整 Sobolev Hilbert 实现，嵌入为真实 zeroth Lp 字段；dirichletGradient 是 `SobolevHilbert.toJet` 后的实际一阶 fieldCLM。形式本身为这一完整梯度的 L² 内积，原 operator 是该闭形式的全变分域/action，不是预先缩成光滑域或有限维域。周期能量构造因此内部供应原弱状态的实际 L²_t H¹₀ 字段，不需新加 H¹₀ 时间可积性或能量代表选择假设。

第 11 项将 dirichletGradient 的 compLpL 与 E 复合；第 12 项保留其真实时间 a.e. 代表身份。第 13 项在同时满足嵌入、pathL2 代表和 Ioo 时间定位的满测集上，取能量元素的真实 H¹ jet。其 value 经原 clampPath 在闭区间的恢复精确等于该时刻的原 p.trace；随后使用所给同一 F 的每时刻迹身份。未要求原状态在每个时间属于 D(A)，未由空间零测边界推导点值，也未把任意 F 视作 p 的代表。

## 全弱梯度与经典梯度的识别

第 8 项展开原 SpatialTest.sobolevJet 的 `derivativeOneFiber` 构造，使用实际 CLM 作用于欧氏基向量的 Lp 身份及 fderivLp 代表身份。各分量对应完整 `Fin d`，不是只选一个方向。

第 9 项的输入仅为开、有界 S、原弱 H¹ jet u、全局 C∞ F 和其与 u.value 的空间 a.e. 等式。由 closure S 紧，实际 `exists_spatialTest_eq_one_on_compact` 构造紧支 η，在 closure S 上为 1；令 φ=ηF。φ 为真实全空间 SpatialTest，在 S 上精确等于 F。限制 φ 的实际 H¹ jet 后，value 与 u 相同；原 `WeakSobolevJet.value_injective` 用全部弱测试唯一性证明两个 jet 完全相同。再用真实限制分量身份及开放集上的局部导数相等，得到每个原弱一阶分量等于 F 的真实 Fréchet 方向导数。没有假设原 u 光滑、事先给定其梯度或要求全空间 H¹ 零延拓。

第 10 项利用有限坐标的 a.e. 全称合并和 `Sym.oneEquiv : Fin d ≃ Sym (Fin d) 1` 重排全部分量。DerivativeFiber 是真实有限维 Hilbert 纤维，其 norm² 为完整分量平方和；固定 `spatial_directionalEnergy_gradient` 通过真实 Riesz gradient 身份把该和识别为 `‖gradient F‖²`。因此没有 d、d+1、算子范数到纤维范数比较或遗漏分量造成的额外系数。最终第 13 项声明准确是时间 a.e. 内嵌空间 a.e. 的范数平方身份；未声称已完成后续产品测度积分的形式化对接。

一般空间辅助引理允许空域及 d=0 的合法输入；有限坐标平方和在 d=0 时为空和。Dirichlet 周期模型及最后盒引理明确要求 hd>0，正边长盒的几何由原接口内部供应；本报告不将其扩为 d=0 的完整 Dirichlet 估计。局部 `backward.isDefEq.respectTransparency false` 是定义展开设置，完整实际声明及内核公理依赖已核实，没有产生新的数学公理或跳过证明。

## 真实权能量、指数及观察区域

固定 TimeWeight 要求全部实时间 `1≤q(t)≤w.max`；SpatialProfile 是实际有界可测空间函数。原 multiplier 的值为 `q(t)^τ exp(ρ(x)q(t))`。已读取 `TimeL2Multiplier`、`WeightedTime`、`MultiplierContinuity`、`AllowedWeight` 和 `Observation`：timeMap 是该实际空间乘法逐时间作用后的 Bochner Lp 类，a.e. 强可测性由真实算子范数连续性与 q/u 的强可测性供应。有限加权 L² 由真实全局界与 MemLp 证明，未利用 totalized integral 在不可积情形的默认值。

第 1 项使用的界为 `max(1,w.max^τ) exp(ρ.bound·w.max)`。q≥1 保证任意实指数合法，也保证负 τ 时相应全局界。第 2 项使用原正 q 的幂恒等式 `(q^(s/2))²=q^s`，得到准确的指数平移 τ+s/2，随后由真实 L² 内积积分给 timeSq=norm²。它是同一函数的精确身份，未更换允许权或把 s 错当成 2s。第 3 项由连续线性映射范数平方推出连续性，所需假设仅为固定 q 的 a.e. 强可测性。

记 u=pathL2(p.trace)、D=p.weak_dtime、A=p.actual_A、G=dirichletPeriodicGradient(p)、θ=exp(qρ)。新定义中的四项对应如下原 Bochner 能量：

| 项 | timeSq 指数 / 实际输入 | 对应原量 |
|---|---|---|
| 值 | s=3，u，τ=0 | 时间积分 `q³‖θu‖²L²(S)` |
| 梯度 | s=1，G，τ=0 | 时间积分 `q‖θG‖²L²(S)`；光滑代表时 G 的范数平方为原空间 gradient 的范数平方 |
| 残差 | s=0，εD+A，τ=0 | 时间积分 `‖θ(εD+A)‖²L²(S)`；经典 core 中 A=−Δ，故符号为原 ε∂t−Δ |
| 观察 | s=3，cutoff(W)u，τ=0 | 时间积分 `q³‖θ1_Wu‖²L²(S)`，即原观察区域 S∩W 的空间限制 |

固定 `BoundedMultiplier.cutoff W hW` 的真实值为 `1_W`，界为 1；其 a.e. map 身份和 observation_sq_integral 已证明实际空间限制积分。W 仅需可测；在 W⊆S 的原应用中观察区域就是 W。示性函数的空间不连续性不会阻碍固定乘法算子的 L² 连续性。新定义使用同一 θ、同一 q 和同一 p，未将梯度变成 ∇(θu)，也未把 ε·dtime+A 的两个字段分开估计而引入额外因子。

固定 C178 的 classicalDirichletTimeCore 输出同一 F 的真实时间导数和负空间 Laplacian 字段。已读取 ClassicalDirichletTimeCore、ClassicalHarmonicTimeCore、HarmonicGraphFields、BoxClassicalTimeDensity，核对了两层 a.e. 代表运算、实际 cos/sin 时间微分及负 Laplacian 线性性。其完整图稠密性已接受且在本版本未变。将上述嵌套 Bochner 量与已有 boxTimeIntegral 的四个真实柱积分逐项连接，仍是后续接口工作；本报告不把数学对应关系冒充该形式化连接已经完成。

## 同一常数的密度传递及明确剩余前提

第 16–17 项分别把连续 timeSq 与原值、实际梯度、`ε·fieldsDerivative+fieldsOperator`、真实 cutoff 的 CLM 复合，得到完整 PeriodicGraph 上的连续实函数。权映射界可以依赖本次固定的 w.max、ρ.bound、τ，原图上的连续性常数也可以依赖 T；这些只证明固定参数下的极限合法，没有进入估计常数 C。

第 18 项先固定 hd、g、w、正盒、ρ、hq、ε、C、W、hW，再假设对全部 classicalDirichletTimeCore 元素成立同一 `Left≤C·Right`。两个连续实函数使该不等式集闭；真实 core 在完整图空间稠密，故 `closure_minimal` 把原不等式传到任意 p。没有扩大 C、没有更改 ε 或权，没有只传到有限谐波/光滑状态，也没有把逼近中出现的 T 或权上界带入原 C。实数 C 无需正性：固定常数乘连续函数仍连续，闭集传递本身无需任何除法或正号假设。任意实 ε 的结论同时覆盖原 ±1 两个符号，但不单独证明任何方向的光滑 CE。

**剩余前提必须保留：** `hCE` 是对光滑 classical core 的实际四项 Bochner 不等式。当前定理并未构造原 ρ/β/qc/C，也没有从既有 C² 时间权的光滑柱积分估计推得 hCE。因此本批仅接受所述连续性和条件传递辅助结果；不认证完整弱 CE，不提升 P024，也不覆盖一般凸多面体。此限制与固定规格、展开类型一致，未发现本批辅助目标的实质弱化或隐藏假设。

## 固定依赖、公理及本机证据

五模块的递归 Carleman import 闭包为 315 个文件，其中 310 个旧文件与 mathematical_base 逐文件内容完全相同。对关键已接受 declaration_version 的相关完整闭包又逐文件比较，均无内容变化：

| 依赖 | declaration_version | 实际比较入口 / 闭包文件数 |
|---|---|---|
| C178 | `5ec78c3027e714324439187119dfbfe4765a2af6` | `Spatial/BoxClassicalTimeDensity` / 295 |
| C176 | `d5a8ab859e4413c6eb950702df73990e356c3786` | `Spatial/BoxCompactSmoothDensity` / 254 |
| C168 | `86686ea4d106798727d898bf61abc238812a8cb8` | `Weights/InteriorHeatGradientReturn` / 93 |
| C150 | `3d418d76a4959a094dcd26d2d157c213f297531d` | `Spatial/InteriorSmoothCutoff` / 26 |
| C056 | `4f669626b3228adea39a16fbf6c1d22313763331` | `Spatial/DirichletForm` / 49 |
| C055 | `fa61af9d4b260cac83d599ef4e228af88f67aee8` | `Spatial/SpatialTestSobolev` / 28 |
| C032 | `87363270f74e4955f5afbb8ecc20ae2990d449f5` | `Weights/TimeL2Multiplier` / 38 |
| C029 | `13b774fecc0ad449d8ae9a0b958069e095c24e59` | `Continuous/FormEnergyClass` / 19 |
| C023 | `e4b308fc21cd669906716aa9af53f1c2a263b1a7` | `Spatial/WeightedTime` / 28 |
| C022 | `a6c199412758d406be8c3f8d1e76587b9f820bc1` | `Spatial/SobolevRealization` / 25 |

Lean 固定为 `leanprover/lean4:v4.35.0`，CI 实际版本 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机该 checkout 的 HEAD 同值且工作树干净。本批未修改工具链、引入新库版本或新增数学公理。

实际读取 `/tmp/carleman-t163-heat-continuity-target.log`：最终 DirichletHeatContinuity 定向 **3523 jobs** 成功；读取 `/tmp/carleman-t163-weak-heat-continuity-build.log`：根目标 **4072 jobs** 成功。`-axioms.log` 实际为空，不将空 stderr 当作独立审计成功证据。完整固定 raw 末行为 `Axiom audit passed for all 7913 Carleman declarations.`。

固定 raw 有 2992 个公理打印记录、2988 个不同显式名称；递归检查覆盖 **7913** 项 Carleman 声明。全部打印记录仅依赖正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理；未见 sorryAx 或新增非基础公理。十八项新声明的完整类型和公理集合均逐项核实，显式记录数与递归审计总数不混同。

## 独立正式 CI 与原始产物

独立通过 GitHub API 查询 [run 39250961568 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39250961568/attempts/1)：`head_sha=61ddd47f394ef2a5c61e3ccc317ace118ab816b5`，最终 run 为 `completed / success`，最后更新 `2026-10-19T12:22:06Z`。实际三个作业均已最终成功：

| 作业 | job ID | 实际结果 |
|---|---|---|
| state-check | `118054347917` | completed / success |
| lean | `118054348356` | completed / success |
| dashboard / snapshot | `118056050110` | completed / success |

验收者自行用 `gh run download` 下载同 run 的两个原始产物，未用主执行者副本代替独立下载：

| 产物 | artifact ID | 独立本机位置 |
|---|---|---|
| lean-ci-result | `12185193007` | `/tmp/carleman-t163-weak-heat-continuity-main-ci/result.json` |
| lean-declaration-evidence | `12185262895` | `/tmp/carleman-t163-weak-heat-continuity-main-axioms/axioms.txt` |

实际 result.json 为 `status=PASS`，`checked_sha=source_head_sha=61ddd47f394ef2a5c61e3ccc317ace118ab816b5`，目标 `Carleman`，`finished_at=2026-10-19T12:20:44.074143+00:00`；Lean/mathlib 与固定 pin 一致。两个 artifact 的 workflow head SHA 同值。

远端 raw 与固定 `/tmp/carleman-t163-weak-heat-continuity-local-axioms.txt` 经独立逐字节比较：**完全相同**，均为 **2444719 bytes**，SHA256 均为 `65ab097409a6076273393439769492a7f538cc41933722dc994ea7e30d7dfdf0`。比较未使用后续阶段动态 `.ci/axioms.txt`。

## 签发

**C179：PASS / AUXILIARY。** 十八项真实声明未发现阻断性数学、量词、对象身份、范数、依赖或公理问题。真实能量/梯度字段、四项原指数加权能量连续性及保留同一 C 的密度传递通过；`hCE` 的实际光滑柱积分清偿、完整弱 CE 和一般凸多面体仍待。正文与 reviewed_at 随本报告提交冻结，仅提交报告，不修改实现或全局台账，不推送。
