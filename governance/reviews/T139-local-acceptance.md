# T139 / C155 独立本机验收

- checked_sha: `b60153e14ed7085f5828aea582fbc74ade8286aa`
- base_commit: `d1dca8884990c684f923a4938e40a6cc88e1645f`
- reviewed_at: `2026-10-19T08:29:53+00:00`
- reviewer: `/root/accept_section3`，独立于实现者。
- result: **PASS**；axiom_check: **PASS**。
- scope: **AUXILIARY**。四模块 31 项声明均通过，C155 可登记 REVIEWED；P023、P024/连续 CE 及其他 PAPER 项不提升，原文完成数保持 **16/26**。

## 固定范围与原文定位

依固定版本的 AGENTS.md、PROJECT_OPERATIONS、state/README、MATH_SPEC、MILESTONES、PAPER_COVERAGE 及 `governance/analysis/T139-coordinate-reflection.md`，直接读取四模块完整源码、31 项实际展开类型和关键证明依赖，并独立读取远端 CI。未用执行者说明、旧 PASS 标签或 CI 代替数学审查；动态工作树、后续跨面实现与变化中的 `.ci/axioms.txt` 均不作为本批证据。

原文对应 `paper/main.tex:2657–2665` 的 Corollary A.2（`prop:analytic-realizations`）：凸多面体/盒上的 Dirichlet Laplacian 需有 `D(A)=H²∩H¹₀` 及椭圆正则估计；Section 6 的真实形式见 1469–1470、1634 行。原文在此引用 Grisvard，未独立陈述本批坐标反射引理。本批是通向盒上正则性的证明工具：构造全空间任意弱 H¹ 状态的坐标反射，并严格识别其梯度和能量。它尚未证明反射后跨面 Poisson 方程、盒面拼接或全局 H²，因而不能据此声称已覆盖 Corollary A.2。原 `prop:continuousCE`（2672 行起）同样不由本批完成。

## 全部 31 项声明

名称省略公共前缀 `Carleman.`；行号与路径对应固定 Git 对象。顺序与交付 declarations JSON、固定 C155/T139 清单完全一致，四模块均由固定 `Carleman.lean` 导入。

| # | 声明 | 固定位置 | 数学核验 |
|---|---|---|---|
| 1 | `coordinateSignFlip` | Geometry/CoordinateReflection:14 | PASS。逐坐标选取负号或恒等，构造真实欧氏线性等距同构。 |
| 2 | `coordinateSignFlip_apply` | Geometry/CoordinateReflection:18 | PASS。仅 r 分量变号，其余分量保持。 |
| 3 | `coordinateReflection` | Geometry/CoordinateReflection:23 | PASS。上述线性图后平移 `2c e_r`，得到实际仿射同胚。 |
| 4 | `coordinateReflection_apply` | Geometry/CoordinateReflection:27 | PASS。逐点严格为 `R(x)_r=2c-x_r`，其余坐标为 `x_j`。 |
| 5 | `coordinateReflection_involutive` | Geometry/CoordinateReflection:36 | PASS。逐坐标证明 `R(R x)=x`，不假设反射图自逆。 |
| 6 | `coordinateReflection_symm` | Geometry/CoordinateReflection:43 | PASS。同胚逆图由实际单射与自逆身份识别为 R。 |
| 7 | `coordinateReflection_measurePreserving` | Geometry/CoordinateReflection:50 | PASS。欧氏线性等距保体积与平移保体积复合；没有 Jacobian 缩放损失。 |
| 8 | `coordinateReflectionSign` | Geometry/CoordinateReflection:55 | PASS。实际 `s_i=-1` 当且仅当 `i=r`，否则为 1。 |
| 9 | `coordinateReflectionSign_sq` | Geometry/CoordinateReflection:57 | PASS。两种情形均有 `s_i²=1`。 |
| 10 | `coordinateSignFlip_basis` | Geometry/CoordinateReflection:61 | PASS。真实基向量作用为 `A e_i=s_i e_i`。 |
| 11 | `firstComponentFields` | Spatial/FirstComponentJet:13 | PASS。零阶用真实标量嵌入，一阶用全部坐标字段的 Euclidean 装配。 |
| 12 | `firstComponentJet` | Spatial/FirstComponentJet:19 | PASS。每个实际坐标弱导数作为输入，内部逐一清偿原 weakJetSubmodule 的全部一阶条件。 |
| 13 | `firstComponentJet_value` | Spatial/FirstComponentJet:34 | PASS。零阶真实 L² 值严格为给定 u。 |
| 14 | `firstComponentJet_gradient` | Spatial/FirstComponentJet:38 | PASS。每个实际 `Sym.cons i nil` 一阶分量严格为给定 `g i`。 |
| 15 | `firstGradientAssembly_norm_sq` | Spatial/FirstComponentJet:44 | PASS。全梯度 L² 范数平方等于各坐标 L² 范数平方之和，无维数或重复计数常数。 |
| 16 | `coordinateReflectionLp` | Spatial/CoordinateReflectionLp:13 | PASS。真实保测逆图复合产生 L² 等价类上的加法映射。 |
| 17 | `coordinateReflectionLp_ae` | Spatial/CoordinateReflectionLp:18 | PASS。借逆图等于 R，将代表严格识别为 `u∘R`，身份在 volume-a.e. 意义下成立。 |
| 18 | `coordinateReflectionLp_norm` | Spatial/CoordinateReflectionLp:26 | PASS。实际 L² 范数精确保持，常数为 1。 |
| 19 | `integral_mul_coordinateReflectionLp` | Spatial/CoordinateReflectionLp:30 | PASS。真实积分换元将左边 `a·Ru` 变成右边 `(a∘R)·u`，图方向准确。 |
| 20 | `coordinateReflectionLp_inner` | Spatial/CoordinateReflectionLp:35 | PASS。真实 L² 内积的单侧反射自伴身份，使用上述换元及代表身份。 |
| 21 | `coordinateReflectionLp_involutive` | Spatial/CoordinateReflectionLp:46 | PASS。第二个 a.e. 身份通过保测映射拉回，再用点态自逆得到 Lp 类相等。 |
| 22 | `coordinateReflectionLp_inner_both` | Spatial/CoordinateReflectionLp:59 | PASS。自伴加自逆得到两个输入同时反射时内积保持。 |
| 23 | `IsWeakSpatialDerivative.coordinate_reflection` | Spatial/CoordinateReflectionLp:64 | PASS。完整弱测试仿射换元先得到方向 `s_i e_i`，再乘 `s_i` 恢复方向 `e_i`，导数为 `s_i Rg`。 |
| 24 | `WeakSobolevJet.reflectCoordinate` | Spatial/CoordinateReflectionH1:15 | PASS。对任意原全空间 H¹ jet，实际反射值与所有带符号反射梯度组装成同一原空间中的 jet。 |
| 25 | `WeakSobolevJet.reflectCoordinate_value` | Spatial/CoordinateReflectionH1:22 | PASS。反射 jet 的真实值等于值的 L² 反射。 |
| 26 | `WeakSobolevJet.reflectCoordinate_gradient` | Spatial/CoordinateReflectionH1:25 | PASS。法向导数变号、切向导数保持，全部坐标均明确识别。 |
| 27 | `WeakSobolevJet.reflectCoordinate_involutive` | Spatial/CoordinateReflectionH1:30 | PASS。L² 值自逆配合原弱导数唯一性，得到整个 jet 相等。 |
| 28 | `WeakSobolevJet.reflectCoordinate_value_norm` | Spatial/CoordinateReflectionH1:35 | PASS。原标量 L² 值范数精确保持。 |
| 29 | `WeakSobolevJet.reflectCoordinate_gradient_pairing` | Spatial/CoordinateReflectionH1:39 | PASS。全梯度真实配对逐坐标展开，反射内积保持且 `s_i²=1`，双侧配对精确保持。 |
| 30 | `WeakSobolevJet.reflectCoordinate_gradient_norm` | Spatial/CoordinateReflectionH1:49 | PASS。取同一状态的配对平方身份，再用范数非负取根，得到真实全梯度范数相等。 |
| 31 | `WeakSobolevJet.reflectCoordinate_gradient_adjoint` | Spatial/CoordinateReflectionH1:56 | PASS。双侧配对保持与整个 jet 自逆推出单侧配对自伴。 |

## 关键数学核对

**真实几何与测度。** `SpatialCoordinates d` 是欧氏空间，线性部分为真实 `LinearIsometryEquiv.piLpCongrRight`，仿射部分为 `A x+2c e_r`。已直接核对 mathlib 的线性等距保体积证明以及 `Lp.compMeasurePreserving` 的构造、a.e. 代表与范数定理。反射可能改变取向，但其 Lebesgue 体积保持性由等距证明内部供应，不需外加行列式假设。图与逆图在定义中没有混用：一般 affineTransportLp 用逆图，本批明确证明逆图等于 R 后才改写为 `u∘R`。

**完整弱测试。** `IsWeakSpatialDerivative` 的原定义量化所有真实 `SpatialTest S`：全空间 C∞、紧支、支撑包含于 S 的函数，测试及其实际 Fréchet 方向导数的 L² 资格由紧支连续性给出。被调用的 `SpatialTest.pullbackAffine` 实际构造 `φ∘R`，证明光滑、紧支和支撑包含，链式法则使用真实导数 A。`affine_transport` 对每个目标测试调用原弱身份，再用保测换元；不是仅验证有限测试族，也没有要求 u 或 g 具有光滑代表。

在本批 S=T=univ，域前提内部成立。方向计算先给 `D_(s_i e_i)(Ru)=Rg`，再对方向乘 `s_i`，利用 `s_i²=1` 得 `D_i(Ru)=s_i Rg`。因此法向负号正确；没有把所有方向一律变号。反射 L² 的自逆证明专门使用 quasiMeasurePreserving 将 a.e. 身份复合拉回，未非法把 a.e. 身份当作全点身份。

`integral_mul_coordinateReflectionLp` 对任意函数 a 是 Bochner 积分换元身份，本身不声称任意乘积可积；其内积与弱测试用途均是 L²×L²，真实可积性已由相关 L² 资格保证。此宽类型不会造成弱导数证明退化成不可积函数的零积分。

**完整 H¹ 与梯度。** 原 jet 用零阶和所有一阶 Euclidean L² 字段组成，并由真实分布导数联系。firstComponentJet 证明全部约束，未增设替代弱测试。零阶只有 `Sym.nil`，一阶由 `Sym.oneEquiv` 与 Fin d 双射；装配范数平方与全部梯度配对恰好逐坐标求和，每个分量计一次。反射后的 whole-jet 自逆借 `value_injective`；已核对该旧证明依赖全测试决定 L² 类以及弱导数唯一性，univ 的开性、a.e. 支撑条件由本批内部提供。没有 H² 正则性或算子域识别的循环。

量词覆盖任意 d、任意现有坐标 `r : Fin d`、任意实数 c、任意全空间原弱 H¹ jet，以及配对中独立的 u、v。精确等式没有位置、状态或维数相关常数。d=0 时不存在可选坐标，反射声明不虚构坐标；独立的字段装配与平方和声明仍覆盖 d=0。全空间 volume/univ 范围在类型中明确，本批未把任意域的 H¹ 状态直接当作全空间状态，也未假设其 H² 零延拓。

## 固定依赖、公理与构建

四模块 Carleman 导入闭包共 **77** 模块，其中 **73** 个旧模块与 base 逐字节一致。另对关键已验收版本递归核对：

- `AffineWeakTransport` 的 18 模块闭包与 C093 / `8c4571e511be4cb48a8fd9b76c11ddba9a16e975` 一致。
- `WeakProductComponents` 的 71 模块闭包与 C084 / `3eeba97f7b274bd8ffd473d2f57aad2b4e722845` 一致。
- `FirstGradientAssembly` 的 41 模块闭包与 `604328efce1cc28e4d6fe6cadcdaa039ee0e76a3` 一致。
- `SobolevRealization` 的 25 模块闭包与 C022 / `a6c199412758d406be8c3f8d1e76587b9f820bc1` 一致。

除版本比较外，实际读取 AffineWeakTransport、WeakDerivative、WeakDirections、SobolevJet、SobolevRealization、WeakDerivativeUnique、FirstOrderSobolevJet、FirstGradientAssembly、GradientPairing、WeakProductComponents 的相关定义与证明。没有仅凭旧报告放行。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与 base 不变。

四新模块无 `sorry`、`admit`、新增 `axiom` 或 `native_decide`。31 项递归公理均仅为正常基础公理 `propext`、`Classical.choice`、`Quot.sound`；完整原始文本中 2533 个非空打印公理记录和 9 个无公理记录无越界项。全库递归遍历 **7156** 个声明，包含自动生成声明；该总数不等于显式打印记录数。已核对 CheckAxioms 的 `privateToUserName` / `collectAxioms` 检查体与基线不变，没有隐藏未批准公理。

实际定向日志 `/tmp/carleman-t139-h1-target.log` 为 **3217 jobs** 成功；全库 `/tmp/carleman-t139-reflection-full.log` 为 **3948 jobs** 成功及 7156 项审计通过。Lean 固定 4.35.0，CI 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，锁定版本与实际干净依赖 HEAD 一致。

## 独立 CI 与原始产物

独立查询 [正式 main CI 39222503707 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39222503707/attempts/1)：push/main，`head_sha=b60153e14ed7085f5828aea582fbc74ade8286aa`，run 最终 `completed/success`，`updated_at=2026-10-19T08:29:11Z`。同 SHA 的另一次 run 39222503279 为 cancelled，不作为通过证据。

| job | ID | 最终状态 |
|---|---|---|
| lean | 117960888663 | completed/success |
| state-check | 117960888867 | completed/success |
| dashboard / snapshot | 117962702023 | completed/success |

本验收者独立查询并通过 `gh run download` 自行下载同次正式 run 的两项原始产物：

- `lean-ci-result`，artifact ID **12172168531**，归档 **491 bytes**，archive digest `sha256:52a696866b0dffd1b58a0aeac328e3b9548ccc9aafedad71fe1159108ac55a15`。
- `lean-declaration-evidence`，artifact ID **12172970189**，归档 **201962 bytes**，archive digest `sha256:9fd7ab1d77ceb88ccccb8af0679add15b3ddb63af3e0d151020b8056e2441495`。

实际读取 [result.json](/tmp/carleman-t139-reflection-main-ci/result.json)：`status=PASS`，`checked_sha`、`source_head_sha` 均为本报告固定 SHA，目标为 `Carleman`，`finished_at=2026-10-19T08:27:25.130613+00:00`。此为证明结果时间；三项任务最终成功另经上述独立查询确认。

下载的 [原始公理/类型产物](/tmp/carleman-t139-reflection-main-axioms/axioms.txt) 与 [固定本机副本](/tmp/carleman-t139-reflection-local-axioms.txt) 经本验收者直接逐字节比较完全相同：均 **2181733 bytes**，SHA256 均为 `c4de73c8d65822a49f5c09c26b96fd95129e45b4c45f41cf8cdedd4e13278a8e`。31/31 声明均有完整类型及对应公理记录；末行为 `Axiom audit passed for all 7156 Carleman declarations.`。

未发现需修复的数学或证据缺陷。本次正式 PASS 仅覆盖明示全空间弱 H¹ 反射辅助范围；报告签发通知后冻结内容及 reviewed_at。
