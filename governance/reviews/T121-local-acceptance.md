# T121 / C137 独立本机验收

- `checked_sha`: `4689b4942585bde7e96bc0ecfa1a360de012db2b`
- `base_commit`: `a26158d00376e85866c536aa366239af41c83f97`
- `reviewed_at`: `2026-10-19T05:40:28+00:00`
- `reviewer`: `/root/accept_section3`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：任意全空间真实 L² 弱导数对 u、v、任意方向 e，对 C¹、全局 Lipschitz 且 η(0)=0 的实标量函数，证明 η(u) 的原分布导数为 η′(u)v。**本批不声称 H¹₀ 连续代表的边界零值已完成；P011 不提升，原文保持 14/26。**

本 Agent 独立读取固定 git 对象中的三个完整模块、9 项完整展开类型及关键依赖，并对照原稿 Section 6 的 P1 空间设置（`paper/main.tex:1465–1495`）及 Step 2（1523–1548）。已读固定 T121 分析、MATH_SPEC；AGENTS、运行/状态协议和原稿与前次实际读取版本逐字节不变。执行者说明及 CI 未替代本次数学核查。后续 SmoothGapCutoff、WeakZeroGradientConstant、WeakScalarGap 和变化中的 `.ci` 均未作为本批依据。

## 全部 9 项声明

以下名称省略公共前缀 `Carleman.`，模块位于 `Carleman/Spatial/`。清单与固定 C137、T121 及 `/tmp/carleman-weak-chain-declarations.json` 一致。展开类型行号为固定本地和相同远端 `axioms.txt` 中的行。

| # | 声明 | 固定源码 | 展开类型行 | 独立结论 |
|---|---|---|---|---|
| 1 | `memLp_mul_of_ae_bound` | L2BoundedMultiplierLimit:14 | 26394 | PASS；实际 a.e. 可测有界乘子与原 L² 函数的乘积确实 MemLp。 |
| 2 | `bochnerL2Norm_mul_le_of_ae_bound` | L2BoundedMultiplierLimit:23 | 26400 | PASS；真实 L² 乘子范数界为 M，未引入测度或维数损失。 |
| 3 | `l2_bounded_multiplier_zero_tendsto` | L2BoundedMultiplierLimit:33 | 26408 | PASS；固定可积控制 M²g² 与实际 DCT 给 aₙg 强趋零。 |
| 4 | `l2_bounded_multiplier_strong_tendsto` | L2BoundedMultiplierLimit:51 | 26418 | PASS；aₙ→b a.e.、Gₙ→g 强 L²，真实误差分解给 aₙGₙ→bg 强 L²。 |
| 5 | `memLp_toLp_tendsto_of_L2_error` | WeakDerivativeStrongLimit:14 | 26433 | PASS；实际函数误差范数转换为其 toLp 类的原范数拓扑收敛。 |
| 6 | `IsWeakSpatialDerivative.of_strong_function_limits` | WeakDerivativeStrongLimit:25 | 26438 | PASS；对全部原 SpatialTest，连续 L² 配对的闭集身份传到强极限。 |
| 7 | `weakSpatialDerivative_of_contDiff` | WeakDerivativeStrongLimit:43 | 26450 | PASS；全空间 C¹ 函数与其真实方向导数的合法 L² 类满足全部测试的分部积分身份。 |
| 8 | `l2_lipschitz_comp_error_tendsto` | WeakScalarChainRule:15 | 26457 | PASS；真实 Lipschitz 复合保持强 L² 误差趋零，复合资格由 η(0)=0 供应。 |
| 9 | `IsWeakSpatialDerivative.scalar_chain_rule` | WeakScalarChainRule:33 | 26467 | PASS；同一组实际卷积、经典链式法则及强极限给任意原弱状态的标量链式法则。 |

## 实际有界乘子与强 L² 乘积极限

第 1–4 项在任意可测空间和任意测度 ν 上处理实标量函数，不假设有限测度或有限体积。第 1 项先用 |ag|≤M|g| 和 a.e. 可测性建立乘积的真实 MemLp；第 2 项将真实 toLp 代表的 a.e. 身份代回范数单调性，得到 ‖ag‖₂≤M‖g‖₂。M≥0 是显式条件，M=0 也包括，未除以 M。

第 3 项中，被积函数是实际 (aₙg)²，控制函数恰为 **M²g²**。g∈L² 保证该控制函数可积，乘积可测性由第 1 项给出。每个 n 的 a.e. 上界和 aₙ→0 的 a.e. 极限满足固定 mathlib 支配收敛定理的真实条件，得到平方积分趋零，再通过平方积分与真实 L² 范数平方的身份及连续平方根得到强收敛。全程没有借用不可积积分的默认值或无穷 eLpNorm 的 toReal=0。

第 4 项精确使用

\[
a_nG_n-bg=a_n(G_n-g)+(a_n-b)g.
\]

首项由同一个 M 的乘子界和 Gₙ−g 强趋零控制；次项满足 |aₙ−b|≤2M，并对固定 g 应用第 3 项。原假设只需要 Gₙ 的真实 MemLp 与强 L² 收敛，不需要 Gₙ 逐点收敛或一族共同支配函数。DCT 的控制只用于固定 g 的那一项，未误用到变动 Gₙ。b 的 a.e. 可测性和同界明确列出；它们在最终链式法则中由 η′ 连续及内部导数界实际供应。

## 全测试函数的弱身份闭合与经典分部积分

第 5 项将 `(hF n).toLp (F n) − hf.toLp f` 通过真实 `MemLp.toLp_sub` 识别为差函数的 toLp，再用 `bochnerL2Norm_eq` 得到原 Lp 空间的强收敛。不是只把代表函数的 a.e. 极限命名为强极限。

第 6 项完整类型允许任意局部紧集有限测度 ν、任意测试域 S 与任意方向 e。`IsWeakSpatialDerivative` 已展开为对 **每一个 SpatialTest S** 的 L² 配对身份。对固定但任意 φ，集合

\[
\{(u,v):\langle u,D_e\varphi\rangle=-\langle v,\varphi\rangle\}
\]

因内积连续而闭；两个分量的真实 Lp 强极限落在此闭集。证明先 `intro φ`，故结论覆盖全部原测试函数，没有改成有限测试族、光滑状态子类或某稠密子集上的未清偿条件。局部有限性用于保证真实紧支测试及其导数的 L² 资格，与原弱导数定义一致。

第 7 项接受实际 C¹ 函数 f、任意方向 e 及与 f、Dₑf a.e. 相等的 L² 类 u、v。它对任意全空间 SpatialTest φ 使用真实 Fréchet 导数分部积分。Df·e、f、φ 和 Dφ·e 均连续，φ 及其导数紧支，因此三项 `(Dₑf)φ`、`f(Dₑφ)`、`fφ` 的可积性逐项证明后才调用积分身份。已核对固定 mathlib 定理的方向及负号，准确得到 ∫fDₑφ=−∫(Dₑf)φ。此辅助定理没有另加 f 全局 Lipschitz、紧支撑或有界导数假设。

## 原全部弱状态的真实标量链式法则

第 8 项先从全局 Lipschitz 性和 η(0)=0 得出 η∘Fₙ、η∘f 的真实 MemLp，再由逐点差界 |η(Fₙ)−η(f)|≤M|Fₙ−f| 得到真实 L² 误差界。已读取 mathlib `LipschitzWith.comp_memLp` 的实际证明：零点条件保证 |η(f)|≤M|f|，故即使全空间体积无限也保持 L²。此条件不是未证明的正则性结论。

第 9 项只对原 u、v 假设 `IsWeakSpatialDerivative volume univ e u v`，方向 e 任意、维数不限。使用同一实际归一化缩小核 κₙ 定义 Fₙ=u⋆κₙ、Gₙ=v⋆κₙ。已复查 `WeakConvolution` 中的全测试反射核分部积分和实际卷积求导，得到 **DₑFₙ=Gₙ**，不是两个不相关近似序列。实际光滑性、两者 MemLp、强 L² 极限和 Fₙ 的 a.e. 极限均来自固定已验收卷积证明。

η 的 C¹ 性给真实导数及 η′ 连续。`norm_deriv_le_of_lipschitz` 从 hL 内部推出所有 t 的 |η′(t)|≤M，已读取该 mathlib 定理；没有把未知导数界、链式法则或目标误差估计作为新假设。经典 `HasDerivAt.comp_hasFDerivAt` 给每个 n、每个 x 的实际恒等式

\[
D_e(\eta\circ F_n)(x)=\eta'(F_n(x))G_n(x).
\]

随后第 7 项将这个实际 C¹ 函数的身份转为原弱身份。值分量由第 8 项强收敛到 η(u)；导数分量中 aₙ=η′(Fₙ)、b=η′(u)，连续 η′ 与 Fₙ 的原 a.e. 极限给 aₙ→b a.e.，同一 M 供应两侧上界，而 Gₙ→v 是实际强 L² 极限。第 4 项因此给 η′(Fₙ)Gₙ→η′(u)v 强 L²。第 6 项把这两个强极限传回全部 SpatialTest，得到所需原分布导数。

主定理显式接收任意 U、V:Lp，并要求它们分别 a.e. 等于 η(u)、η′(u)v。这是代表无关的识别接口，不是隐藏的存在性障碍：证明内部 `hUf`、`hVf` 已从 hL、h0、η′ 连续/有界及原 u、v 的 MemLp 构造这两函数的真实 MemLp，故可取对应 toLp 类；末尾使用 Lp.ext 证明该实际类等于任意给定合法 U、V。没有预设 U/V 的目标弱身份。

因此本批不要求原状态连续、点态可微、光滑、紧支撑、H²，亦不要求 η 为 C² 或 C∞。M=0、e=0、d=0 都没有额外排除；方向长度不被错误省略，因为原 v 本来就是 Dₑu，公式中的全部方向依赖保留在 v 中。

## 原文对应与辅助范围

原 P1 空间为 H¹₀(Ω) 内的分片仿射函数，Step 2 使用 H² 的闭包连续代表定义节点插值。把连续的 H¹₀ 状态连接到边界节点零值，需要真实分析论证。本批提供后续截断论证所需的 **全空间弱 L² 标量链式法则**，并未直接输出边界迹、frontier 上点值或 conforming 插值资格。

本批主定理要求全空间弱导数，不能把任意域内弱状态的零延拓自动认作满足该条件；将其用于原 H¹₀ 状态须调用已有真实全空间零延拓结果。这里没有进行或声称完成该后续边界组合。η 的 C¹、全局 Lipschitz 和 η(0)=0 是本辅助命题的明确前提，不是原完整 P1 已被额外限制后的替代结论。

原 H¹₀ 连续代表的边界零值、后续 gap/截断组合、conforming 插值和全域允许权组装仍不属于本批结论；已有前批局部节点值/梯度成果也不由本批重新提升为完整 P011。本阶段没有时间或网格估计量词，不能据此宣称原允许权、T 统一或完整 P1 数值假设已经完成。范围保持 AUXILIARY，原文 14/26 不变。

## 固定版本、构建与公理依赖

三个新模块的 Carleman 导入闭包共 **89** 模块，除本批三模块外的 **86** 模块与 base 逐字节不变。关键已验收版本进一步核对：`StrongL2NormLimit` 的 61 模块闭包与 T119 的 `6f051d6775dc64fbf1ccf1e93df232c43dee616f` 一致；`StrongMollifierLimit` 的 72 模块闭包与 T115 的 `f134750df6b8ef03c639f50dd5084d4c42d49272` 一致；`WeakConvolution` 的 24 模块闭包与已验收 `c99262c4a0d65a4d23f2efb57748bda490e971d7` 一致。记录见 [T119](T119-local-acceptance.md)、[T115](T115-local-acceptance.md)、[T073](T073-local-acceptance.md)；实际使用另经本次独立检查。

AGENTS、治理协议、原稿及 toolchain pins 与 base 和前次实际读取版本不变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定 4.35.0；mathlib pin 与本机实际 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，mathlib 工作树干净。本次实际读取该版本 DCT、Lipschitz 复合、导数界和方向分部积分声明/证明。三个模块都在固定 root 导入，新源码无 sorry、admit、额外 axiom 或 native_decide。

固定审计器与 base 不变，collectAxioms 覆盖全部 Carleman 常量，包括私有/生成辅助声明，仅允许 propext、Classical.choice、Quot.sound。逐项检查 9 项新声明的完整类型及公理；固定文件全部 **2326** 条非空公理打印记录、**8** 条无公理记录均无不允许的公理。显式打印记录含重复，和环境总量不同；真实末行为 **6697** 项全声明递归审计 PASS。

独立读取 `/tmp/carleman-weak-chain-target.log` 的 **3255 jobs** 成功和 `-full.log` 的 **3872 jobs** 成功及上述审计。固定 `/tmp/carleman-weak-chain-local-axioms.txt` 为 **2,034,190 bytes**，SHA256 **`0712f1a9ed1a74436b903b356fcf3f4865f0e2411c31ef6ccdd95db61d65ebc8`**。

## 实际同 SHA CI 与原始产物

本 Agent 自行查询 [main CI 39205342801 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39205342801/attempts/1)。实际 main/push，head SHA 精确等于本报告 checked_sha；最终 **completed/success**，run 更新时间 `2026-10-19T05:39:20Z`。以下三项均实际查询为 completed/success：

| Job | ID | 最终结果 |
|---|---|---|
| state-check | 117906841750 | success |
| lean | 117906841944 | success |
| dashboard / snapshot | 117907803719 | success |

同 run 原始 `lean-ci-result` artifact **12165132810**（归档 492 bytes）与 `lean-declaration-evidence` artifact **12165132814**（归档 186,723 bytes）元数据均绑定本报告 SHA，且未过期。本 Agent 自行执行两次 `gh run download 39205342801`，均实际 exit 0，分别下载到 `/tmp/carleman-weak-chain-main-ci`、`/tmp/carleman-weak-chain-main-axioms`。

实际 `result.json` 为 **537 bytes**，SHA256 `1f1c4a9c337994432e396b993ebaec2d1db9cd1e4cbed08af9c4b20595471d1e`。内容 PASS，`checked_sha=source_head_sha=4689b4942585bde7e96bc0ecfa1a360de012db2b`，target 为 Carleman，`finished_at=2026-10-19T05:38:02.406671+00:00`，ci_url 为同 run/attempt。远端 Lean 4.35.0 提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 提交与固定 pin 一致。

独立逐字节比较远端 `/tmp/carleman-weak-chain-main-axioms/axioms.txt` 与固定本地副本：**完全相同，2,034,190 bytes，SHA256 `0712f1a9ed1a74436b903b356fcf3f4865f0e2411c31ef6ccdd95db61d65ebc8`**。远端末行同样是 6697 项递归审计 PASS。原始 result、同版本完整类型/公理产物、三 jobs 最终成功均分别核验，没有用另一运行或后续 `.ci` 替代。

## 验收决定

**C137：PASS，可升级 REVIEWED，scope 保持 AUXILIARY。** 9 项声明的真实乘子资格、DCT、强极限、全测试闭合、经典 IBP、同一卷积链式法则和全部原弱状态范围均通过独立核查；未发现需要修复的数学缺陷。同 SHA 三项 CI 及独立下载原始证据通过。

**P011 不提升，原文仍为 14/26。** 本批不提前宣布边界零值完成。本次仅新增本报告，未修改实现、root、台账或原稿，未 commit/push。以上 UTC 签发时间固定；定稿通知主 Agent 后冻结报告及 reviewed_at，不再修改。
