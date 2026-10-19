# T141：原坐标盒 Dirichlet Laplacian 的全局 H² 正则与算子域

本阶段完成任意固定正边长坐标盒、任意正维数上的原弱 Dirichlet 解全局 H²，以及原形式算子域 D(A)=H²∩H¹₀；完整 H² 图范数由原 L² 右端控制，常数在所有状态和右端之前选择。本结果是原 Corollary A.2 的盒上正则部分，不是整个含凸多面体和全部解析假设的 P023。

`UpperReflectedBox` 和 `UpperBoxOddPoisson` 对上侧面给与下侧面同等的实际几何、完整反对称边界测试、弱 Poisson 方程、原解恢复、扩大盒 H¹₀。上侧扩大端点为2bᵣ−aᵣ，反射平面为bᵣ；法向符号和零边界不被替换成下侧面假设。

`SubdomainComposition` 从实际 L² 代表证明嵌套限制、自限制和全空间后子域限制的严格身份，并逐字段提升为整个原弱 jet 身份。`BoxPoissonExtension` 将每次实际奇延拓的 H¹₀、方程、整个 jet 恢复、值/梯度/右端2倍界一并登记为 IsPoissonExtension，随后用真实构造证明其存在；该谓词没有被当作新的数学前提。`PoissonExtensionComposition` 真实限制的复合及非负因子估计证明延拓复合，全部状态和右端保持原对象。

`ExpandedCoordinateBox` 为有限坐标集s固定端点：已处理坐标为a'=2a−b、b'=3b−2a，其余为a、b。几何完全独立于状态/右端。单个新坐标依次对当前盒的下侧和上侧作奇反射，精确产生这两个端点。`FiniteBoxPoissonExtension` 对实际有限集归纳，每个坐标乘4，得到统一4^|s|的值、梯度、右端范数界；实际限制恢复通过逐次复合保持。全坐标univ给4^d，原闭盒严格包含于固定扩大开盒。

`BoxPoissonRegularity` 在扩大盒上对实际延拓弱解调用已验收的完整原内部 H² 定理。原闭盒紧且严格在扩大盒内，由已有真实光滑cutoff构造选出M，M在输入u/f之前选择。得到的H² jet限制整个H¹ jet为原u，实际负Laplacian由完整弱测试的右端唯一性识别为原f。各梯度坐标范数≤完整梯度范数，结合4^d界得到C(‖f‖+‖∇u‖+‖u‖)²的Hessian平方界；没有把原H²或反射后的H²作为输入。

`BoxDirichletRegularity` 从实际形式算子图得到原H¹₀弱解，以上结果给同值H² jet，故原operator domain⊆实际H²。结合此前已验收的反向包含，证明精确D(A)=H²∩H¹₀。再选固定盒的实际有界slab，从原弱方程和已证Poincaré给梯度≤2R‖f‖、值≤(2R)²‖f‖。由Hessian平方界取非负根，再使用原完整jet图范数≤三个真实字段范数和，得K≥0、∀u/f的完整‖v‖≤K‖f‖，其中truncate v=u且−Δv=f。没有自由选择替代解、替代梯度或额外光滑输入。

最终正则类型明确要求所有盒边长正；完整算子和纯右端估计要求d>0以选Poincaré方向。Hessian中间定理还覆盖d=0。常数允许依赖固定盒、维数，不声称对任意形状盒或一般凸域有统一常数；时间、网格和输入状态不参与常数选择。

九模块34声明，最终定向3404 jobs、全库3965 jobs、7289声明递归公理审计通过。固定 `/tmp/carleman-t141-box-h2-local-axioms.txt` 为2216514bytes，SHA256 `5837236580601c8df8c51a65b8d67eb278def318dfd18a7bbaecae4511a5d06e`，仅正常基础公理。申请AUXILIARY验收；本阶段清偿实际盒域H²正则，尚未包装全部FD数值命题、一般凸多面体正则、完整P023解析假设或连续CE。原文覆盖暂保持16/26。
