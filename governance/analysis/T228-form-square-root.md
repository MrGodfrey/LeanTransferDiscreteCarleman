# T228 — 原闭形式的正自伴平方根及完整定义域/能量身份

基线 `4573638d5529914e0140c25f4dfe3689be92afaa`；原稿 `paper/main.tex:353` 的 A1 末句。三模块30声明（26定理、4定义），AUXILIARY；待把原H₀ᵐ值域身份和总接口接入后再重新审核完整P022。

对同一原CoerciveForm b，以已构造的零移位resolvent定义真实 R=A⁻¹=b.embed∘resolventEnergy(0)。原所有V测试身份给实际双线性配对，证明R正、自伴、单射，rangeR恰为原D(A)且稠密。resolventEnergy(0)在原Hilbert能量V中也稠密：对其范围的任意正交向量y，用原coercive形式的连续同构逆取w，再以所有H载荷配对推出embed(w)=0，真实嵌入单射推出w=y=0。没有输入原域或解的额外稠密性。

对任意正有界B满足B²=R，内部证明B单射及稠密，并从原形式测试精确得到 a(R_E f,R_E g)=⟨Bf,Bg⟩。coercivity给‖R_E f‖V≤c⁻¹/²‖Bf‖H。通过mathlib的真实有界线性延拓，将Bf↦R_E f延拓为L:H→V，且L(Bf)=R_E f。由B的真实稠密范围与连续性，将配对身份扩展为a(Lx,Ly)=⟨x,y⟩，同时embed(Lx)=Bx。

原形式有界性进一步给‖x‖H≤(1+‖a‖)‖Lx‖V，故L下有界且范围闭；原R_E范围稠密又包含于rangeL，因而L满射。于是rangeB=range(embed)=原V的实际H值域。这一步实际证明平方根范围资格，并非把目标H₀ᵐ域作为输入，也未只在原D(A)或光滑稠密子集上证明身份。

定义formSqrtDomain为原embed的完整范围，并以B的真实线性单射范围等价逆定义S:Dhalf→H。证明完整图身份 (x,f)∈graphS 当且仅当Bf=x。原H上的正性由⟨Sv,v⟩=⟨Sv,B Sv⟩≥0给出。对任意y,g，所有Dhalf测试的伴随等式等价于y=Bg：测试全部v=Bf，使用B自伴和H内积分离性；因此S的完整伴随图就是自身图，Dhalf由原embed稠密而稠密，不是仅声称对称。

组合图逐点刻画：x∈Dhalf且Sx∈Dhalf及S(Sx)=f，当且仅当B²f=x，当且仅当Rf=x，当且仅当(x,f)∈原graphA。因而S²=A同时包含完整组合域等式及原算子作用身份，绝非仅给某稠密子集的平方公式。对每个原能量成员v，由embed(L(S(embedv)))=embedv及嵌入单射得到L(S(embedv))=v，实际全空间配对身份给‖S(embedv)‖²=a(v,v)。

最终 exists_positive_form_square_root 在内部调用T227已构造的任意实Hilbert正有界算子平方根，供应R的真实B，再输出上述S、正性、完整自伴图、完整平方组合图以及全部原V的能量身份。没有将B、目标sqrt域、能量恒等式或第二表示定理作为新增输入；没有有限维、谱截断、紧嵌入、复化、额外光滑或额外正则性假设。原始b的Hilbert完备、稠密注入、有界对称coercive形式是唯一原数据。该结论直接清偿T226报告F1所要求的数学桥；下一阶段需要将range(embed)与OriginalForm.V在原值域中识别并装配完整一般系数命题，再由独立Agent判定P022。
