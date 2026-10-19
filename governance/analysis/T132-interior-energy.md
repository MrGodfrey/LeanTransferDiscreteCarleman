# T132：紧支测试的内部 Hessian 能量与真实 Poisson 平滑化

本阶段为 H² 内部正则估计建立两个实际分析工具，不宣称 Dirichlet 边界上的 Miranda–Talenti 不等式已经成立。

`CompactTestHessianEnergy` 对原紧支光滑测试 φ 和任意方向 e,f，通过两次真实分部积分及三阶测试导数的交换，证明 ‖D_fD_eφ‖²=⟨D_e²φ,D_f²φ⟩。对坐标求和给精确的有序 Hessian 能量 Σᵢⱼ‖Dᵢⱼφ‖²=‖ΣᵢDᵢᵢφ‖²，并推出每个真实二阶分量范数≤Laplacian范数。紧支性质负责没有边界项；该结论未扩展到具有非零法向导数的一般 H²∩H¹₀ 函数。

`CompactTestH2Jet` 给原测试的实际 L² Laplacian，并从上述分量界和全部弱测试身份构造真实 H² jet。其一阶截断严格等于原测试 jet，negativeLaplacian 严格等于负的实际纯二阶导数和，Hessian平方≤card(Sym(Fin d),2)‖Δφ‖²。该维数因子显式保留，未混同有序 d² 与原无序字段范数。

`WeakPoissonConvolution` 首先证明仅有一个原弱导数时的二次卷积微分交换。对实际 H¹ 弱 Poisson 解，将原方程写成逐坐标真实积分，使用支持包含于域内的反射光滑核作为原测试；a.e. 零延拓积分公式保留原测度和负号，得到卷积梯度的散度等于卷积右端项。随后用原一阶弱导数链识别卷积函数的实际纯二阶导数，证明 −Δ(u*κ)=f*κ 在核完整位于域内的每一点成立。没有原 u 的 H² 前提，没有其全空间二阶零延拓或预设二阶弱导数。

三模块9声明，定向3252 jobs、全库3922 jobs通过；6951声明递归公理审计PASS。固定 `/tmp/carleman-t132-interior-energy-local-axioms.txt` 为2126767 bytes，SHA256 `c7719e6145e61f465ebcd7dd51a25c15bc41b6e3939df9733771f42dde4cf4b6`。

AUXILIARY，14/26，P023 不提升。下一步由紧支截断和卷积 L² 界得到内部 H² 估计；边界正则性、统一凸域 Hessian 界及光滑凸穷竭仍需证明。
