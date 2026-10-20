# T241 / C257 独立本机验收

- checked_sha: `e445f7d9d5e46db8b7a68a46769ac05442ee75bc`
- mathematical_base: `9160cd18d129e8d33ef644a71f5794f9df54a1c2`
- reviewed_at: `2026-10-20T08:23:52+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，4/4 定理，未发现阻断缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；给定实际上下图域上原 H¹₀ 弱 Poisson 解的同状态全局 H² 成员资格。覆盖保持 18/26，P023 不提升。**

已全文读取固定 `Carleman/Spatial/GraphDomainRegularity.lean`、全部 raw 完整类型与公理、analysis/MATH_SPEC/清单，并对照原稿 `paper/main.tex:2659–2665`。Corollary A.2 要求原一般凸多面体或盒上的完整 Dirichlet 实现及椭圆估计；本批只组合给定图域的真实正则性。T240 在本次签发前已独立冻结，报告和实际实现均已读取。只核对固定本地执行证据，没有重跑全库或查询 CI/看板。

## 实际数学与原输入

1. **输入是同一原 H¹₀ 弱解。** u 是完整 `WeakSobolevJet d 1 (volume.restrict T) T`，hu 是原 `dirichletJetSpace T` 的真实测试闭包成员，f 是原 T 上任意 L² 类。已直接重读 `IsWeakNegativeLaplacian`：它要求每个原 `SpatialTest T` 满足 `weakGradientPairing u φ.sobolevJet=⟨f,φ⟩`，正是 −Δu=f 的正梯度配对。没有原 H²、变换后 PDE、额外梯度预算或光滑状态假设。
2. **真实域、状态与边界条件的传输。** 通用定理令 F 为原实际剪切，S 字面等于 F⁻¹T；T 开放和 F 连续内部给 S 开放。v 是 T238 的实际 H¹ 拉回，值为原 u 的 L² 复合，所有梯度分量都是真实弱链式；hu 经原测试闭包的传输内部给 v∈H¹₀(S)。只有这一合法一阶状态用于原 H¹₀ 零延拓和差商测试，不将原梯度自动当作可全空间 H¹ 延拓的对象。P 使用已证 Jacobian=1 的限制体积保测度映射；载荷为同一个 f 的真实 L² 拉回 Pf。
3. **系数资格全部内部供应。** a 取 T240 的实际 Gram 系数：b=Dψ、B_bξ=ξ−ξ_r b、a_ij=⟨B_b e_i,B_b e_j⟩。本次已直接完整读取 `GraphEllipticForm`，确认实际弱梯度逆方向、完整双线性型与系数界，未只引用报告。由原高度 Lipschitz C 和实际各斜率 Lipschitz B_i，内部得到全空间有界系数、全局 C∞、每项 Lipschitz 常数
   `L_ij=2(1+d C)Σ_i B_i`，
   以及每个 x、每个 ξ 的椭圆下界，取
   `κ=((1+d C)²)⁻¹>0`。
   严格正性由 C≥0 内部推出；处处椭圆性再转为全空间 AE 资格，符合 T236 的真实输入。没有任意替代矩阵、系数延拓前提或额外的椭圆/导数假设。系数和这些常数只由给定几何确定，不依赖原状态或载荷。
4. **原全部测试方程准确接到差商接口。** 对每个 φ∈SpatialTest S，T240 从原 hf 取实际逆测试 χ=φ∘F⁻¹，完整矩阵能量和真实换元给
   `Σ_ij ∫_S a_ij D_i v D_jφ=⟨Pf,φ⟩`。
   本批先用 `matrixGradientPairing_test_integral` 将 `B_a(E₀v,φ.fullJet)` 精确识别为同一有限积分和，再调用该方程。已重读此身份的实际零延拓/限制代表和测试 Fréchet 导数实现；矩阵索引、载荷和正梯度符号一致。各项由有界系数与 L²×L² 可积性支持，即使图域无界，也不是借全定义积分的默认值建立方程。不存在外加“变换方程成立”或只对少数测试成立的输入。
5. **由原方程取得拉回 H²，再恢复同一原 u。** 通用定理明确保留 S 的全部切向实平移原像包含 hSS；其余 T236 资格由上述构造给齐。实际调用 `exists_variable_dirichlet_H2_of_tangential_invariance`，从合法 H¹₀ 二次差商和原弱方程取得全部切向/混合导数，内部恢复法向通量及法向二阶导数，输出完整 V∈H²(S) 且 `truncate¹ V=v`。这里不是把目标 H² 当作输入。再调用 T239 的真实反向 H² 传输，使用同一 ψ、C、B_i、原 u 和刚取得的 hV，得到 U∈H²(T) 且严格 `truncate¹ U=u`。已核对该反向接口：实际 −ψ 逆剪切、限制测度域等式、AE 复合和弱 jet 值唯一性恢复的是同一原 H¹ 字段。原零边界资格与弱方程因此仍属于原状态，没有重选解或改换 f。
6. **上图域的全部几何资格内部清偿。** 对 T={ψ(x)<x_r}，开放性由原 ψ 连续和坐标连续给出。已证 F⁻¹T={x_r>0} 后，任意 j≠r 和任意实 t 的平移不改变 r 坐标；实际基向量坐标公式给 hSS。最终具体上图定理没有留下开放性、半空间对应、切向不变、矩阵/PDE 或目标 H² 作为额外输入。
7. **下图域与方向正确。** 新下图原像定理先用 ψ(Fx)=ψ(x)、F(x)_r=x_r+ψ(x)，精确推出 F⁻¹{x_r<ψ(x)}={x_r<0}；该身份只要求 ψ 连续及法向平移不变。具体下图定理由坐标连续性给开放性，并用同一 j≠r 坐标计算证明负半空间的 hSS。它调用的是 T236 的一般切向不变域版本，不是把负半空间错误代入仅适用于正半空间的陈述，也不需要新增方向反射或改变原 PDE 的符号。

几何输入仍明确为给定全空间 C∞ 的 ψ、沿 r 的全部实平移不变、全空间高度 Lipschitz C、每个实际斜率的全空间 Lipschitz B_i。不能从仅局部光滑边界或斜率有界自动得到这些输入。通用第一定理另显式保留 hSS；两个具体图域定理已内部清偿。r:Fin d 要求实际法向，d=1 时切向条件为空而法向恢复仍适用，不虚构零维法向。

结论针对任意**已给定且满足原弱方程**的 H¹₀ 解，给原域上的全局 H² 成员资格；并非断言无界图域对每个 f 都存在 H¹₀ 解。本批 wrapper 明确丢弃两个依赖返回的定量 `_hbound`，只输出准确截断身份，没有额外声称一个新的统一凸域椭圆常数或强算子图定理。原边界图构造、局部化/拼接和原凸域统一 Hessian 估计尚待，故 P023 不提升。

## 全部声明逐项结论

源码行为固定 `GraphDomainRegularity.lean`；raw 行为本批固定审计文件的完整类型起始行。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 13 / 42992 | `Carleman.exists_dirichlet_H2_of_graph_tangential_invariance` | PASS；真实原解、内部系数与方程、原 hSS、H¹₀ 差商正则性和同状态反向恢复。 |
| 50 / 43013 | `Carleman.exists_graphEpigraph_dirichlet_H2` | PASS；真实上图域及全部切向几何资格内部供应，无目标 H² 前提。 |
| 71 / 43026 | `Carleman.spatialGraphShear_hypograph` | PASS；同一剪切对实际下图域的精确负半空间原像。 |
| 81 / 43031 | `Carleman.exists_graphHypograph_dirichlet_H2` | PASS；真实下图域原弱解恢复同一原 H²，方向与接口正确。 |

## 依赖和固定本地证据

T240 正式报告已全文读取并核对其冻结单文件提交 `d81a68b7cfd6153ad7b5d45a5be5f42c038ef519`：checked_sha 为本批 base，reviewed_at=`2026-10-20T08:20:41+00:00`，31/31 PASS，AUXILIARY。报告 11683 bytes，SHA256 `45a6d1c70e8ce177caaa2366dba43057059684446a37018eddcb31c591ca16fa`，提交内容与当前文件一致。实际 T240 模块已全文直接读取；另核对原 `IsWeakNegativeLaplacian`、全空间/限制矩阵配对、T236 的具体输入和法向组装，以及已验收 T238/T239 的同状态 H¹₀/H² 传输调用。导入闭包 **210 个 Carleman 文件**，其中 **209 个旧文件**相对 base 的 Git blob 全部不变。

- `/tmp/carleman-t241-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T08:18:59.407565+00:00`；实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 记录均 exit 0。本验收核对真实执行记录，没有声称重跑全库。
- `/tmp/carleman-t241-local-source-manifest.txt`：**1038 项、112655 bytes**，SHA256 `733624ff0a5fd3eaf8dc093ea67e632963e6296a18c947fbae43e1a2cd2dcdf0`。独立枚举固定 proof 全部 tracked `.lean` 及三项工具链配置，路径集合完整、无重复，逐项摘要与固定 Git blob 全部一致。
- `/tmp/carleman-t241-target-build.log`：**3390 jobs** 成功，110 bytes，SHA256 `c279fdf123c78263e4d34d5716b7c089ed363b6fa1e16d8ddb5d64dd0c6d065f`。`/tmp/carleman-t241-build.log`：**4280 jobs** 成功，80 bytes，SHA256 `164fa6ef07a0b5808f3018e83c111cd0ff1bc4dd3616daad706cd4708c20af6f`。`/tmp/carleman-t241-axioms.log` 为 0 bytes。
- `/tmp/carleman-t241-graph-domain-regularity-local-axioms.txt`：**3310005 bytes**，SHA256 `a752259c3fa935218ce91a01e085b57ed01613e9e7b9afdcd95407549434c202`，与固定摘要一致。4 项完整类型逐一核对；全部 **3908 个显式公理列表及 10 个无公理记录**仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。全命名空间递归白名单与 base 不变，实际末行确认 **9883 声明审计 PASS**，无 sorryAx 或额外数学公理。
- 根导入及全部 4 项 `#check`/`#print axioms` 完整。Lean 4.35.0、编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；实际 mathlib checkout 无修改，与固定 lock 一致为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿与 base 相同，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；AGENTS/operations/state 协议保持已读取版本。

无修复项。接受本批 **AUXILIARY 实际上下图域的原弱 Dirichlet 解 H² 正则性**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、审计或其他报告，不 push。
