# T229 — Proposition A.1 完整原陈述，包括平方根形式域身份

基线 `a914d2ede5d27b37e30708efaff64fdf1b783d2d`；原稿 `paper/main.tex:2615–2654`，原A1–A3在333–376。两模块4显式声明（3定理、1结构）。目标完整P022；独立验收之前仍为17/26。

OriginalForm.formSqrtDomain_eq 将T228原CoerciveForm平方根域range(embed)严格识别为同一原值空间V，依据既有conformingEmbed_range，未丢失原能量成员或改变边界。SquareRootData 在原V上直接记录实际线性算子Ahalf的非负性、完整无界伴随图、完整平方组合图等于同一原A图，以及每个v∈V的‖Ahalf v‖²=scalarForm(v,v)。域就是原V，稠密性由原OriginalForm.dense；伴随图量化所有原V测试，平方图量化全部H的x,f及完整中间域成员，不只给原A域上的单向公式。

exists_squareRootData 内部调用T228的真实正自伴平方根存在定理，用两个实际Submodule inclusion在已经相等的域之间转换。所有H值不变，正性、全伴随图和双向平方图直接无损转移；能量身份通过valueEquiv的满射和原scalarForm_value识别。因此没有把Ahalf或目标身份重新列作输入，也没有把sqrt(a(v,v))标量命名为算子平方根。

最终 higherCoefficient_spatial_operators 对原任意有界Lipschitz域、任意一般阶m、全αβ真实W²ᵐ∞弱系数矩阵、原对称及coercivity，保留原D(A)的H²ᵐ资格与原完整Sobolev Hilbert图估计输入，输出上述同一原A的完整平方根数据，同时输出T226的原域等式、稠密域、闭图、非负/自伴、图界和全允许族A2/A3。原形式确为全部系数实际积分，原V是全部紧支光滑测试的Hᵐ闭包H₀ᵐ；空间/形式基础由T216/T218供应。有界形式和表示定理已经实际证明，不额外假设同名目标接口。

对任意原固定SmoothOnClosure空间函数r，内部构造profile且value=r。统一c,C,Ccomm先于全部TimeWeight、τStar、时刻、符号、τ和全状态，因而原任意T>0及固定有限τStar保留；实际强于有限τ范围。A2覆盖V和D(A)正/逆权保持及原严格2m−1阶q幂交换子；A3覆盖同一完整系数形式的双向权上界和σ²测试下界。原A1完整Hilbert图估计明示为原假设；输出旧jet图界仅为已证范数比较，不冒称证明一般椭圆正则性。

T226独立报告F1要求的同一H上正自伴平方根、D(Ahalf)=V、Ahalf²=A含组合域、全V能量身份现在均在最终定理返回的SquareRootData中。该项数学桥依赖T227真实实Hilbert有界正根和T228真实逆根范围/能量构造，均没有新增有限维、谱截断、紧性、复Hilbert、光滑状态或额外正则性限制。原稿没有修改。P022是否可提升由独立Agent针对固定版本、该新返回字段及全部旧依赖做完整论文级验收决定。
