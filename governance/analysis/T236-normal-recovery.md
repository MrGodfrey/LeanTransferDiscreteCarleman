# T236 / C252: actual variable-coefficient normal recovery

The original target is Corollary A.2 (`paper/main.tex:2659–2665`): the full Dirichlet Laplacian realization on bounded convex polytopes, with the original H² graph regularity. This stage is an auxiliary ingredient for smooth boundary charts. It does not promote P023 or change the accepted paper coverage of 18/26.

`VariableCoefficientNormalRecovery.lean` constructs the missing normal derivative of the same H¹ weak solution. For arbitrary open S, the first recovery theorem starts from the actual distributional divergence-form equation and the other second derivatives. With G_i = D_i u and normal coordinate r, it constructs

    R = −f − Σ_(i,j)≠(r,r) [a_ij D_j G_i + (D_j a_ij) G_i].

The original test equation proves D_r(a_rr G_r) = R. Multiplication by the actual bounded reciprocal of a_rr then gives D_r G_r. The reciprocal derivative is proved by the classical chain rule and the existing distributional product rule; no H² regularity or normal derivative is assumed. The norm bound is conservative and explicit.

The all-components assembly obtains every non-normal second derivative from the actual tangential test estimates using the existing Riesz representation theorem and weak mixed-derivative commutation. It then constructs a symmetric H² jet whose order-one truncation equals the original u exactly.

The final theorems discharge the auxiliary coefficient-derivative and normal-positivity inputs. The actual derivative multiplier is obtained from smoothness on S and the given global Lipschitz constant; its bound is that same constant. Testing a.e. ellipticity on a coordinate vector gives a_rr ≥ κ almost everywhere, and continuity plus full support of Euclidean volume upgrades this to every point. No separate normal-coefficient positivity assumption is needed in the final theorem.

The half-space theorem internally proves openness and all tangential translation invariances. Its assumptions are an original H¹₀ solution, an L² load, actual globally bounded Lipschitz coefficients smooth on the half-space, and global a.e. uniform ellipticity. Its PDE premise is explicitly the finite sum of integrals of a_ij D_i u D_j φ over the half-space, on every compact smooth spatial test. It does not assume existence for all L² loads on an unbounded half-space, finite measure, a spectral cutoff, or a finite-dimensional solution space.

Writing M = ‖∇u‖₂ and K = κ⁻¹(‖f‖₂ + (Σ C_ij)M), the second derivative bound uses max(K,N), where

    N = κ⁻¹(‖f‖₂ + Σ (‖a_ij‖_bound K + C_ij M))
        + κ⁻² C_rr ‖a_rr‖_bound M.

The squared norm of the symmetric Hessian field is bounded by the number of unordered second-order multi-indices times max(K,N)². Every constant is independent of difference-quotient steps.

Remaining work includes actual nonlinear chart pullback, localization, a finite smooth-boundary cover, the uniform convex Miranda–Talenti estimate, and passage through the already constructed exhaustion. Global extensions of chart coefficients have not been constructed here. This is AUXILIARY, not a completed general-domain paper result.
