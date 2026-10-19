# T133：真实 Poisson 截断恒等式与统一 H² 界

本阶段把原 H¹ 弱 Poisson 解的内部卷积恒等式转成实际紧支局部化的统一二阶估计，尚未对原弱解直接宣称 H²，也不处理边界正则性。

`SmoothLaplacianProduct` 定义实际经典 Laplacian，证明一阶及纯二阶乘积法则，逐坐标求和得到 Δ(ηU)=ηΔU+2∑ᵢDᵢηDᵢU+UΔη。`mulSmooth` 是原 SpatialTest 的真实乘积构造，保留紧支持及原域支持；`laplacianLp_ae` 将实际 L² Laplacian 与经典表达式作 a.e. 识别。

`CutoffPoissonConvolution` 仅要求反射核在截断函数支持上的每一点完整留在原域。支持内使用 T132 的原弱 Poisson 卷积 PDE 和原一阶弱链识别真实梯度；支持外 η、其一阶导数及其 Laplacian 均为零。因此在全空间每一点都有精确身份 Δ(η(u*κ))=−η(f*κ)+2∑ᵢDᵢη(Gᵢ*κ)+(Δη)(u*κ)。此处每个卷积操作的是原对应 L² 类的实际零延拓，不假定它们组成全空间弱导数链。

`CutoffPoissonEstimate` 从真实紧支性及光滑性内部选出同一个 M≥0，控制 |η|、全部 |Dᵢη| 与 |Δη|。非负单位积分卷积的实际 L² 收缩性、限制收缩、有界乘法和有限 Minkowski 给出

‖Δ(η(u*κ))‖₂ ≤ M(‖f‖₂+2∑ᵢ‖Gᵢ‖₂+‖u‖₂)。

所有使用 Bochner L² 范数的函数均先证明 MemLp，有限值转换不掩盖无穷。最后 `exists_uniform_cutoff_H2` 先固定开域和截断选 M，再量化所有原 H¹ 弱解、右端项和合法非负单位核，内部构造截断平滑函数的真实 H² jet；一阶截断严格等于同一原测试 jet，真实负 Laplacian 身份保留，Hessian平方≤card(Sym(Fin d),2)乘上述界的平方。常数不依赖解、载荷或核；显式保留无序二阶字段的维数因子。

三模块12声明，定向3290 jobs、全库3925 jobs通过，6968声明递归公理审计PASS。固定 `/tmp/carleman-t133-cutoff-local-axioms.txt` 为2135281 bytes，SHA256 `d72677eb1bca4ecce1ea6ad2bcabf7f52210227baf564fd85adb46e1d9d0cd8b`。

AUXILIARY，14/26，P023不提升。下一步构造实际光滑截断，结合强 L² 卷积极限，从此统一界恢复原弱解的内部 H² jet；边界正则性、凸域统一 Hessian 界和光滑凸穷竭仍待。
