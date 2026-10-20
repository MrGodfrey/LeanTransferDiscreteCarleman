# T225 — 一般弱系数原算子的允许权统一交换子界

基线 `03f8c203f00dc90f126a44f9200c5ac56f645752`；原稿 `paper/main.tex:2633–2635` 与 ass:localization。一模块11声明（9定理、2定义）；AUXILIARY、17/26；完整A.1的统一原接口整合仍待。

在T224已识别的真实原微分表达式上，将每个系数项的差精确写为 Σ(D^p1 a)[D^(p2++β)u−wD^(p2++β)v]。这里w与有界系数的真实L²乘法交换、线性映射与完整有限列表和交换，未去除原分裂重数。所有状态词阶数均≤2m。每项范数由实际系数界乘该词差界控制，累加所有原αβ和全部分裂项定义固定的 coefficientOperatorBound；原符号(−1)^|α|的绝对值为1。

取v=ξu、wξ=1，T220真实弱Leibniz余项使每个词差的无权导数主项严格相消，剩余≤2^(2m)J lowerParameterNorm(q,u)。该 lower 只含j=0,…,2m−1，精确保留 q^(2m−j)‖D^ju‖。系数原W^(2m,∞)仅通过真实有限导数的有界乘子及固定有限和进入；没有将其换为光滑系数、输入目标交换子界或保留最高2m阶状态项。

原固定profile给真实ξ=q^(−τ)exp(−qηρ)和全族统一相对导数J>0。取 C=(1+coefficientOperatorBound)2^(2m)J>0，先于全部q≥1、τ、|η|=1、允许乘子和状态选择。由u.value=w v.value内部得到v=ξu，因此最终差界适用于所有同值原弱状态。无T、网格或权绝对sup界进入C；全部τ成立，包含原任意固定有限τ_*。

用T224原域等式和T217真实光滑乘法保持H²ᵐ及H₀ᵐ，证明原关联算子的完整域保持性。最终 higherCoefficient_allowed_commutator 只需原SmoothOnClosure及有界开域、真实有限弱系数、原对称/coercivity和原一向H²ᵐ域资格；内部给允许权域保持，并以同一原域成员canonicaljet识别实际Az−wAv，得到上述lower范数界。以−τ、−η应用同一定理即涵盖逆权域保持，未加强ρ为域外光滑延拓。一般椭圆正则性仍作为原假设，不宣称已证明。接下来将这些结论与已验收A3上下界装配进原AllowedWeightData/AllowedFamily及A1接口，再对完整Proposition A.1验收。
