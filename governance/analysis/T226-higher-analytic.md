# T226 — 一般阶系数 Proposition A.1 原接口装配

基线 `f616d5d02bde9bd06cc719a33a727b40c5d44675`；原稿 `paper/main.tex:2615–2654` 与 `333–376` 的 A1–A3。三模块7定理，目标完整 P022；在独立论文级验收前覆盖仍为17/26。

先通过原零阶嵌入的单射性，识别真实 H₀ᵐ Hilbert 能量成员与其规范 weak jet；由此 scalarForm 恰是原全系数 coefficientJetForm，而非另造同名形式。T221 对实际能量成员给的统一加权下界通过该身份移至全 H₀ᵐ 原接口，权平方作用是两次真实 conformingWeight，所有中间成员由已证光滑乘法保持性供应。

higherCoefficient_allowed_data_uniform 选定 c,C,Ccomm 后，才量化原域资格 hD、任意 TimeWeight、全部 τ 和 |η|=1。原正/逆权保留同一 D(A)，hD 仅为 Proposition A.1 原域等式所含的一向 H²ᵐ 资格。交换子用实际 inverse-map 身份消去权与逆权，T224 将两次原算子值识别为实际系数微分表达式，再直接使用 T225 统一界。常数不依赖hD见证、T、qmax、τ或状态。完整 Fin(2m) 下阶和恰是原 q^(2m−j)‖D^jv‖，没有最高阶余项。

higherCoefficient_allowed_family_uniform 将 C 取为 max(C_lower,Σαβ‖aαβ‖∞上界)，保持原下界且同时覆盖T218实际全系数Cauchy–Schwarz上界。使用同一原profile的两个符号以及−τ，给 AllowedFamily 的全部字段。常数先于全部TimeWeight及τStar，实际上对全部实τ成立；因此原有限τStar及T统一性保留。逆权对V的保持性由全符号全τ的同一data直接覆盖，无单独假设。

FormSelfAdjoint 的 operator_adjoint_graph_iff 对任意真实CoerciveForm证明：所有域测试满足 ⟨Av,y⟩=⟨v,g⟩ 当且仅当 y 属于同一原域且Ay=g。这是实际无界算子及其Hilbert伴随的图完全相等，并非仅对称性。使用原已构造 (A+1) resolvent，先解 z=(A+1)⁻¹(g+y)，再测试 v=(A+1)⁻¹(y−z)，得到‖y−z‖²=0；反向由实际域对称性。无有限维、谱截断、或额外自伴前提。

最终 higherCoefficient_analytic_realization 接受原有界Lipschitz域、实际有限W²ᵐ∞全部系数、原对称/coercivity、原一向域资格和原完整Sobolev Hilbert图估计。有限受限体积内部由原域有界性生成。返回同一原D(A)=H₀ᵐ∩H²ᵐ、稠密域、闭图、非负性和上述完整自伴图身份，以及对应原graph估计与任意固定SmoothOnClosure profile的全族A2/A3。profile本身从原光滑函数构造，不要求额外有界可测profile输入；完整Hilbert图估计蕴含项目既有jet范数图估计是已证范数比较。

A1的闭稠密H₀ᵐ、实际有界对称coercive形式和完整关联图由T216/T218及OriginalForm直接构造；本批没有证明一般椭圆正则性，也未声称去除了原graph假设。原A1末句“In particular, D(A^(1/2))=V ...”中的谱平方根尚未单独构造；当前结论使用原闭形式及其完整正自伴关联图。独立验收应明确判断这是否足以作为原A1的等价形式接口；若要求字面平方根结论，须将该缺项保留，不能以主接口编译成功自行升P022。原文无修改。
