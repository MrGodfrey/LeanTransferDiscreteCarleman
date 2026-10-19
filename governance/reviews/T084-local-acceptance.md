# T084 / C100 独立本机验收

- `checked_sha`: `d8ccc85628961e226550d9fea095eac9710ed969`
- `base_commit`: `4e697929d6afc9043f0a20caf093a0d62a33963d`
- `reviewed_at`: `2026-10-19T00:25:46+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**，固定本机与同SHA远端原始产物已逐字节核对。
- `scope`: **AUXILIARY**
- 范围：真实局部平方积分、各向异性笛卡尔块的有限重数、局部加权估计到全域估计的明确√(2M)损失。原Qh局部再现／稳定性和实际Kuhn实例索引、支撑及覆盖仍需接入；原文保持 **13/26**。

独立从固定提交导出源码，读取三模块全部证明、16项完整展开类型和关键依赖，对照固定 `paper/main.tex` Appendix B的Lemma B.2（`lem:fd-weighted-approximation`，TeX 2841–2874）的最后平方求和步骤。执行者规格与CI没有代替数学核对，后续工作区修改不属于本报告。

## 全部16项声明

名称均省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付JSON一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `finiteCoverMultiplicity` | `Spatial/L2FiniteOverlap.lean:17` | PASS；重数是实际包含该点的指标集合之有限基数。 |
| 2 | `sum_indicator_eq_multiplicity` | `Spatial/L2FiniteOverlap.lean:22` | PASS；有限指标函数和逐点等于真实重数乘原函数。 |
| 3 | `bochnerL2Norm_sq_finite_overlap` | `Spatial/L2FiniteOverlap.lean:30` | PASS；原MemLp给可积平方密度，有限重数上界给局部平方和≤M乘全局平方。 |
| 4 | `bochnerL2Norm_sq_finite_cover` | `Spatial/L2FiniteOverlap.lean:46` | PASS；a.e.覆盖及非负密度给全局平方≤局部平方和。 |
| 5 | `subdomainLp_norm_eq_bochner` | `Spatial/L2FiniteOverlap.lean:72` | PASS；真实限制L²类的范数等于原代表在子域的Bochner范数。 |
| 6 | `subdomainLp_sq_finite_overlap` | `Spatial/L2FiniteOverlap.lean:77` | PASS；子域包含与可测性消去双重限制，得到实际Lp限制版本的重叠上界。 |
| 7 | `subdomainLp_sq_finite_cover` | `Spatial/L2FiniteOverlap.lean:87` | PASS；同一真实限制桥保留覆盖下界及全部全局Lp状态。 |
| 8 | `cartesianPatch` | `Geometry/CartesianPatchOverlap.lean:17` | PASS；逐坐标实际开盒端点为o+(z−r)δ与o+(z+r+1)δ。 |
| 9 | `cartesianPatch_isOpen` | `Geometry/CartesianPatchOverlap.lean:22` | PASS；真实坐标开盒的开性，不依赖假定的可测块标签。 |
| 10 | `cartesianPatch_index_bound` | `Geometry/CartesianPatchOverlap.lean:25` | PASS；正步长除法、floor双侧界及整数性给k−r≤z≤k+r。 |
| 11 | `cartesianPatch_window_card` | `Geometry/CartesianPatchOverlap.lean:45` | PASS；实际整数闭区间基数2r+1及函数笛卡尔积基数给(2r+1)^d。 |
| 12 | `cartesianPatch_multiplicity_le` | `Geometry/CartesianPatchOverlap.lean:54` | PASS；真实成员指标集注入窗口×有限标签，重数上界不含总指标数。 |
| 13 | `cartesianPatch_permutation_multiplicity_le` | `Geometry/CartesianPatchOverlap.lean:76` | PASS；标签确为Fin d的全部排列，实际基数d!。 |
| 14 | `finite_patch_h2_assembly` | `Spatial/FinitePatchAssembly.lean:19` | PASS；局部非负平方比较、覆盖和块重叠共同给√(2M)全域损失。 |
| 15 | `weighted_finite_patch_h2_assembly` | `Spatial/FinitePatchAssembly.lean:56` | PASS；真实乘权与Lp限制交换，将相同证明用于三个实际乘权字段。 |
| 16 | `weighted_cartesian_patch_h2_assembly` | `Spatial/FinitePatchAssembly.lean:74` | PASS；内部供应真实排列块重数，最终因子√(2(2r+1)^d d!)。 |

## 实际积分、有限覆盖和Lp限制

重数定义为 `Finset.univ.filter (fun i => x ∈ A i)` 的card，同一块若由不同指标出现就按指标分别计数。指标函数有限和先改写为成员指标集上的常值和，因此逐点等于m_A(x)g(x)。没有以任意给定函数替代几何重数，也没有预先假定所需积分结论。

`bochnerL2Norm`虽然由eLpNorm的toReal定义，但两项新积分比较都明确要求原f属于MemLp 2。该前提给‖f‖²的真实可积性；限制测度不增，所有局部范数也有限。每个可测块的指标密度可积，故有限和与积分交换合法。实际证明所得为

\[
\sum_i\|f\|_{L^2(A_i,\mu)}^2
=\int m_A(x)\|f(x)\|^2\,d\mu(x)
\le M\|f\|_{L^2(\mu)}^2.
\]

覆盖下界只要求a.e.每点属于至少一块，取一个实际成员的非负密度项即可；不要求各块不交，也没有把局部范数之和当成局部平方和。a.e.假设足以容许单元边界的零测例外。通用结果对任意测度及实内积空间值场成立，不额外要求有限全局测度或有限维值域。

`subdomainLp`实际用全局Lp代表在较小限制测度上的MemLp形成新Lp类，其a.e.身份由toLp证明。范数身份使用eLpNorm的a.e.不变性；当A_i⊆S且A_i可测时，(volume|S)|A_i=volume|A_i，于是得到原全局Lp类的两项真实局部平方估计。S本身无需额外开性或可测性，因为实际限制测度和包含关系已经足够。空指标集或零测域也包含在量词内，覆盖前提会恰当地约束非零全局范数。

## 正步长窗口、注入标签与维数因子

设y_j=(x_j−o_j)/δ_j，δ_j>0且x属于格点z的块，则z_j−r<y_j<z_j+r+1。令k_j=⌊y_j⌋，真实floor界k_j≤y_j<k_j+1先给k_j<z_j+r+1及z_j−r<k_j+1；再由整数性得到k_j−r≤z_j≤k_j+r。负坐标、任意平移和非整数步长均被覆盖，除法方向由逐坐标严格正的δ保障。开端点在整数格线上只会减少实际成员数，不会破坏该上界。

每个整数闭区间[k_j−r,k_j+r]恰有2r+1项；真正的有限函数笛卡尔积基数是这些基数的乘积，即(2r+1)^d。r允许为0，d允许为0：空坐标函数空间有一个元素，空积为1，零维排列基数0!=1。代码没有选择不存在的坐标或要求d正。

对每个点x，实际包含x的指标集经给定的全局注入index进入窗口×标签全集。成员落入窗口由实际块包含前提证明，注入性给基数不增加；因此上界为(2r+1)^d card(L)，排列标签时为(2r+1)^d d!。该d!来自实际 `Equiv.Perm (Fin d)` 的基数，而非未证明的“每格有限个单元”断言。任意子块或边界裁剪可以用包含关系接入，计数本身不要求子块可测；后面的积分组合另明确要求可测。

这个几何系数只依赖固定维数d和整数半径r，与o、逐坐标正步长δ、有限网格范围和总单元数无关。它并未构造Kuhn剖分到上述标签空间的注入，也未证明实际节点星或重构支撑落在给定半径块内；这些均仍为最终组合定理的显式前提。

## 平方求和、全域常数及真正乘权

组合定理的A族是覆盖原域的实际局部误差域，B族是右端字段的实际局部块。二者均明确可测并包含于S；A只需a.e.覆盖，B只需a.e.重数≤M。代码没有误对A使用B的重数，也不需要二者相等。

对任意三个真实全局Lp字段u、v、H，给定同一个非负C、h及每个i的局部界V_i+hG_i≤Ch²H_i。利用h≥0及范数非负可合法平方，且V_i²+h²G_i²≤(V_i+hG_i)²。A族覆盖给两个左端全局平方下界，B族重叠给右端平方和上界，故

\[
\|u\|^2+h^2\|v\|^2\le C^2h^4M\|H\|^2.
\]

最后由(‖u‖−h‖v‖)²≥0得到(‖u‖+h‖v‖)²≤2(‖u‖²+h²‖v‖²)，在M≥0、C≥0、h≥0下取非负平方根，精确得到√(2M)Ch²‖H‖。没有总块数、总单元数、额外维数或时间长度因子。M=0、C=0、h=0和空族均合法，没有除以这些量。

加权版本的w是实际a.e.可测有界标量乘子，其map u由真实函数w(x)•u(x)形成Lp类；seminorm就是该类的L²范数。已直接读 `onSubdomain_map`：它以四个真实a.e.身份及限制测度单调性证明先乘权后限制与先限制后乘权相等。`onSubdomain_seminorm`据此将局部假设准确改写为限制(w.map u)的范数，随后使用原未加权定理。乘子原有的有界性只保障真正Lp成员，没有把w.bound额外乘入最终常数。

该步骤不求导w，也不要求w有点态下界或处处非零；允许零乘子时得到合法半范数结论。原正允许权是它的应用情形。尤其左端第二项是w乘实际输入v，而非∇(wu)，没有错误引入或省略乘积法则项。

最后定理对所有位置、正步长、有限注入索引、可测域、乘子和三个Lp字段成立，几何损失内部固定为√(2(2r+1)^d d!)。C仍是局部估计的给定常数：本定理证明局部统一常数如何传递，不独立供应原Qh的统一局部常数。三个字段的数学含义也未被偷换；定理是任意Lp三字段的有效组合原则，并未据此声称v已经是u的弱梯度或H已经是某状态的Hessian。

## 原B.2对应与剩余范围

原B.2先通过原矩重构Qh的仿射再现、局部作用域、稳定性和逆估计取得实际误差局部界，再由hq≤1的允许权比较把它变为加权局部界，最后平方求和并使用有界重叠。本批精确完成最后一步所需的真实积分组合，以及在显式整数格点／排列索引和块包含条件下的实际重叠计数。

原Qh的局部仿射再现与稳定性、完整全局误差／弱梯度身份、实际Kuhn单元的覆盖、标签注入、支撑进入这些块及固定r的实例尚未在本批证明。加权定理的hlocal不能被当作已经构造的Qh误差定理。旧允许权局部逼近接口可以在未来提供部分输入，但新声明没有调用它来消去这些缺口。因此B.2/P026、FD/P012或其他原文命题不由本批提升，scope保持AUXILIARY，原文仍13/26。

## 固定依赖、构建与公理

三模块Carleman导入闭包共89模块，86旧模块相对base完全不变，新增恰为本批三模块。关键旧验收版本亦已比较：C098 SubdomainContinuity的66模块闭包相对 `59452751f05398e3446ed5305638a1e20dc89061` 不变，C099 LocalWeightedNorm的67模块闭包相对base不变。真实Lp限制、Bochner范数与积分平方身份、BoundedMultiplier实际乘法及其限制交换证明已直接读取。

原稿、已读治理协议、工具链pin和CI工作流没有被本批改变。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入三模块，CheckAxioms包含全部16项完整类型及公理输出。

固定本机16项完整展开类型均已核对，1773条显式公理记录仅含 `propext`、`Classical.choice`、`Quot.sound`，无sorryAx。检查器通过privateToUserName遍历所有Carleman声明并递归collectAxioms。实际定向日志为3236 jobs；`/tmp/carleman-patch-assembly-full.log` 包含 `Build completed successfully (3737 jobs).` 与 `Axiom audit passed for all 5810 Carleman declarations.`。固定 `/tmp/carleman-patch-assembly-local-axioms.txt` 为 **1,688,045 bytes**，SHA256 **`d3ccc761cebaaf3ba6b2292484f8c4f9a2a21d3349fc21f2eaa5a76d6ec366a3`**。

已实际读取 `/tmp/carleman-patch-assembly-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=d8ccc85628961e226550d9fea095eac9710ed969`，targets为Carleman，`finished_at=2026-10-19T00:22:27.621391+00:00`，ci_url为run 39180237642 / attempt 1。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-patch-assembly-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,688,045 bytes**，SHA256 **`d3ccc761cebaaf3ba6b2292484f8c4f9a2a21d3349fc21f2eaa5a76d6ec366a3`**。另逐名核对远端16/16完整展开类型及基础公理，1773条显式记录无其他公理、无sorryAx，实际末行为 **`Axiom audit passed for all 5810 Carleman declarations.`**。同run的lean-ci-result（12155933258）和lean-declaration-evidence（12155898216）实际artifact元数据均绑定固定SHA，未混用其他版本或后续工作区产物。

已独立通过GitHub connector读取 [main CI 39180237642 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39180237642/attempts/1)：main/push、head SHA精确匹配固定版本，run为completed/success。state-check（117831238074）、lean（117831238177）、dashboard / snapshot（117832480890）三项jobs全部completed/success；工具链准备、完整构建、checked source记录、原始证据上传及同次快照步骤均success。

## 验收决定

**C100：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定16项未发现实际积分、重数、整数窗口、标签基数、限制与乘权交换、平方求和常数或量词方面需要修复的缺陷；同SHA正式三项CI及原始远端公理证据已独立核实。原Qh与Kuhn实例的剩余义务如上，本批不提升B.2/P026、FD/P012或其他原文命题，原文仍 **13/26**。

本次仅写本报告，没有修改数学实现、台账、原稿或root导入，没有commit/push。
