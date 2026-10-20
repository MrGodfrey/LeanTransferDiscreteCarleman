# T239 / C255 独立本机验收

- checked_sha: `5f61d27fd056feaadbafcf3363d7c25f88036481`
- mathematical_base: `8cf9572cab17a3474e176724f820509861b8bf09`
- reviewed_at: `2026-10-20T08:07:12+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，6/6 定理，未发现阻断缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；给定真实图剪切的二阶弱传输及同一原状态的反向 H² 恢复。覆盖保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Spatial/GraphShearHessianTransport.lean`、6 项 raw 完整类型、公理、analysis/MATH_SPEC/声明清单及原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 是凸多面体或盒上完整 Dirichlet 实现；本批只清偿给定图坐标的双向 H² 传输，不证明原域图已构造或原 PDE 已变换。核对固定本地执行记录，未查询 CI/看板，未重新构建不变闭包。

## 实际数学核对

1. **完整二阶弱链式，未预设目标导数。** T 是任意原开放空间域，F(x)=x+ψ(x)e_r，S=F⁻¹T，P 是两端实际限制体积之间的 L² 复合等距。对原完整 H² jet U，记 G_i=D_iU、H_ij=D_jG_i；实现使用原 `U.property 1` 的全部真实弱链，分别在 j 和 r 方向调用已证明的 T238 弱拉回，得到
   `D_j(PG_i)=Q_ij=PH_ij+w_j PH_ir`，
   其中 w_i=D_iψ 是原真实斜率。被二次求导的状态 v 已固定为 T238 的完整 H¹ 拉回，其梯度是 PG_i+w_i PG_r。这里没有将 G_i 当作经典光滑函数，也没有假设变换后存在二阶 jet。
2. **斜率导数是实际有界乘子。** `dw i j` 由同一斜率的 `spatialDerivativeOn` 构造，值为真实 Fréchet 导数 D_jw_i，bound 恰为给定 B_i。已重读该定义：S 开放与斜率 C∞ 给限制测度下的可测性，原全空间 LipschitzWith B_i w_i 和单位坐标范数给导数上界。限制乘子 w_i 保留原值和 bound=C；其导数身份不是任意候选函数，而是定义等式。真实弱乘积通过 S 内紧支光滑测试 w_iφ 合法建立，给
   `D_j(PG_i+w_i PG_r)=Q_ij+w_i Q_rj+(D_jw_i)PG_r`。
   展开后包含 PH_ij、w_j PH_ir、w_i PH_rj、w_iw_j PH_rr 和 (D_jw_i)PG_r 五项。两个交叉项、二次斜率项与曲率项全部保留，索引和正号正确；没有漏掉非线性坐标的二阶项。
3. **实际 L² 界和完整对称组装。** P 严格等距，原 `derivativeComponent_norm_le` 控制每个原一/二阶分量；w_i 与 dw_ij 的实际乘子范数分别由 C 和 B_i 控制。因此
   `‖Q_ij‖≤(1+C)‖field₂U‖`，
   `‖D_j(D_iv)‖≤(1+C)²‖field₂U‖+B_i‖field₁U‖≤L`，
   其中 L=(1+C)²‖field₂U‖+(Σ_i B_i)‖field₁U‖。B_i≤ΣB_k 的使用由每项非负保证；L≥0 内部推出，零值不需除法或排除。全部真实弱身份对每个 SpatialTest S 给绝对配对界 L‖φ‖。已直接核对所调用的 H² 判据：实际有界测试 Riesz 表示、混合弱导数唯一性、Sym₂ 提升及真实 field assembly 给完整 V，准确保留 `truncate¹ V=v`，并得到
   `‖field₂V‖²≤card(Sym(Fin d,2))L²`。
   该计数是现有无序二阶多指标纤维的真实平方和；没有误将其与有序 d² 矩阵范数无因子地认同。原 0、1 阶字段字面保留，全部弱链均在，所得 V 不是只附有一个二阶范数标签的占位对象。
4. **原值的真实 AE 身份。** 第二定理由精确 H¹ 截断身份取 value，再用 T238 的严格值等式及真实 P 的 AE 代表公式，得到 value V=ᵐ_S value U∘F，并保留同一个 Hessian 界。没有任意 Lp 代表的点值、额外连续代表或全空间二阶延拓前提。S 与两个实际限制测度均未替换。
5. **真实逆坐标与常数不变。** 负高度剪切通过 Homeomorph.ext 与实际公式证明恰为 F⁻¹；负高度斜率用真实 `fderiv_fun_neg` 证明等于 −w_i。故 −ψ 仍使用同一个 C，每个负斜率仍使用同一个 B_i；负高度的法向不变由原 htrans 取负得到。不是为逆变换重新选择未控制的几何常数，也没有假设一个独立逆图。该部分两定理分别只需要其实际写明的连续或 C∞ 资格。
6. **反向恢复准确为同一原 u。** 反向输入仅为原 u∈H¹(T) 和一个 H²(S) 的 V，其完整 H¹ 截断等于原 u 的真实拉回；原 u 的 H² 不作为前提。对 V 调用已经证明的正向定理，但使用 −ψ 和 S。双射身份内部证明 F.symm⁻¹S=T，依此传输所得 jet 的域和实际限制测度。正向 AE 值身份通过真正保测度逆的 quasiMeasurePreserving 拉回，与反向所得值身份在同一原 T 测度下合并，恢复 value U=value u 的严格 Lp 等式。随后原开域上的 `WeakSobolevJet.value_injective` 用完整弱导数唯一性推出 `truncate¹ U=u`，并保留以原 V 的 field₂、field₁ 写出的同一常数形式。没有从单纯相同值直接认同未经验证的梯度；两边均为已构造的真实 H¹ jet。最后 iff 正向用实际 H² U 构造 V，反向用上述恢复，不偷换原状态或解。

给定 ψ 的全空间 C∞、法向全平移不变、全空间高度 Lipschitz C，以及**每个实际斜率的全空间 Lipschitz B_i**，均是明确几何输入。B_i 不由第一导数有界或 C∞ 自动推出。本批没有从原域边界供应这些输入。C、B 在全部状态之前给定，定量系数只含它们和固定维数；无逼近、差商步长或状态后选常数。T 是空间集合，不是时间周期。无需域有界或总体积有限；空开域允许，r:Fin d 明确要求有实际法向，未虚构零维方向。

当前六项定理本身不要求 H¹₀；若原 u 属于 H¹₀，可由 T238 的闭包保持及这些精确截断身份保留相应成员资格。这不等于本批已变换原椭圆 PDE、建立图系数椭圆性、构造/局部化原边界图或完成凸域统一 Hessian 估计。上述工作仍待，不能将本批等价性单独视为原一般域正则性证明。

## 逐声明结论

源码行为固定 `GraphShearHessianTransport.lean`；raw 行为本批固定审计文件完整类型起始行。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 14 / 42759 | `Carleman.exists_graphShearPullback_H2` | PASS；全部二阶弱链、曲率项、真实 L² 界和同一 H¹ 拉回的完整 H² 组装。 |
| 88 / 42774 | `Carleman.exists_graphShearPullback_H2_ae` | PASS；同一原值的实际 AE 复合及 Hessian 界。 |
| 107 / 42790 | `Carleman.spatialGraphShear_neg_eq_symm` | PASS；负高度的实际 homeomorphism 恰为原逆。 |
| 117 / 42795 | `Carleman.graphSlopeMultiplier_neg` | PASS；真实负斜率身份，允许沿用原 Lipschitz 界。 |
| 126 / 42800 | `Carleman.exists_H2_of_graphShearPullback_H2` | PASS；仅原 H¹ 输入、真实逆 AE 传输、值唯一性恢复同一原状态和明确界。 |
| 175 / 42817 | `Carleman.graphShearPullback_H2_iff` | PASS；同一原 u 与其真实拉回的双向 H² 成员等价。 |

## 依赖和固定本地证据

T238 冻结报告已全文读取：提交 `acd021cd36f0378734f13e4b9ffc9b6ddcdb8907`，checked_sha 为本批 base，reviewed_at=`2026-10-20T07:57:49+00:00`，11/11 PASS。本次直接全文读取其 `GraphShearWeakTransport` 实现，核对实际全测试链式、原 P/斜率、完整 H¹ 字段及闭包保持；另重读 `WeakProduct`、实际斜率导数乘子、限制乘子、`WeakH2BoundedTest`/`SecondOrderJetAssembly`、分量范数界和 `value_injective`。T237 同一图剪切及保体积实现保持已核验版本。导入闭包 **208 个 Carleman 文件**，其中 **207 个旧文件**相对 base 的 Git blob 全部不变。

- `/tmp/carleman-t239-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T07:59:37.719848+00:00`；实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 记录均 exit 0。本验收核对真实执行记录，没有声称重跑全库。
- `/tmp/carleman-t239-local-source-manifest.txt`：**1036 项、112441 bytes**，SHA256 `693b33295f7a4d7058c040d05aa1aa91740b7464727ec2d85286dd63388d276b`。独立枚举固定 proof 的全部 tracked `.lean` 及三项工具链配置，路径集合完整、无重复，每项摘要与固定 Git blob 一致。
- `/tmp/carleman-t239-target-build.log`：**3388 jobs** 成功，115 bytes，SHA256 `bb44e03bd2d00f45fef7c4da80f85a7b9ab2928e1bbff8cb0c350e14ec25551d`。`/tmp/carleman-t239-build.log`：**4278 jobs** 成功，80 bytes，SHA256 `392526571b3b7aaf2251f1bb282b0ebf90864e487b3f18cdb17ecf56b88f9d34`。`/tmp/carleman-t239-axioms.log` 为 0 bytes。
- `/tmp/carleman-t239-graph-hessian-transport-local-axioms.txt`：**3291849 bytes**，SHA256 `ea2fdfbf38e06b94d8018a740fdc027bd02f07c5815746b0259c416b6e1d3977`，与固定摘要一致。6 项完整类型逐一核对；全部 **3873 个显式公理列表及 10 个无公理记录**仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。全命名空间递归白名单逻辑与 base 不变，实际末行确认 **9834 声明审计 PASS**，无 sorryAx 或额外数学公理。
- 根导入及 6 项 `#check`/`#print axioms` 完整。Lean 4.35.0、编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；实际 mathlib checkout 无修改，与固定 lock 一致为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿与 base 相同，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；AGENTS/operations/state 协议保持已读取版本。

无修复项。接受本批 **AUXILIARY 双向弱 H² 图坐标传输**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、审计或其他报告，不 push。
