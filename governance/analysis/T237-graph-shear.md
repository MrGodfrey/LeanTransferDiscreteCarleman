# T237 / C253: actual nonlinear graph coordinates

This stage supplies actual geometric and measure-theoretic input for the smooth-boundary proof route toward Corollary A.2 (`paper/main.tex:2659–2665`). It remains AUXILIARY, with paper coverage 18/26. It does not assert general-polytope H² regularity or claim a boundary graph has already been obtained from the analytic level charts.

For a selected coordinate r, the input is a real smooth height ψ on the full Euclidean space satisfying ψ(x+t e_r)=ψ(x) for every x,t. The actual homeomorphism is F(x)=x+ψ(x)e_r, with inverse x−ψ(x)e_r. The invariance hypothesis proves both inverse identities and exactly F⁻¹{ψ(x)<x_r}={0<x_r}; hence the map is onto the full graph domain, without a local-image or domain mismatch.

The normal derivative D_rψ is proved zero by the actual one-variable chain rule along t↦x+t e_r. The full Jacobian is I+e_r⊗Dψ. Its matrix in the real Euclidean orthonormal basis is identified entry by entry, and the matrix determinant lemma gives det DF=1+D_rψ=1. Mathlib's actual differentiable injective change-of-variables theorem, with F's bijectivity, then proves F preserves Euclidean volume. Restriction to every actual target set and in particular the graph domain is proved using the measurable embedding map/restrict identity. No unit determinant or measure preservation is assumed as an extra premise, and no finite-volume condition is used.

The forward and inverse maps are genuinely smooth. The slope differential is invariant under every normal translation, obtained by differentiating the original identity with a fixed real translation. For a global Lipschitz height, each actual slope D_jψ is packaged as a bounded multiplier with the original Lipschitz bound; it is smooth, and its normal derivative is proved zero. These are inputs for the following weak-coordinate product rule, rather than an assumed weak chain rule.

Actual smooth tests pull back under any smooth homeomorphism with the stated preimage support containment. Compact support follows from the homeomorphism; all first derivatives are the actual Fréchet chain rule. The graph-shear versions explicitly give D_e(φ∘F)=D_eφ∘F+(D_eψ)(D_rφ∘F) and the inverse formula with the minus sign.

The real L² pullback is mathlib's measure-preserving composition linear isometry on a.e. quotient classes. Its AE representative, actual inverse, test-to-L² compatibility, and scalar integral change-of-variables identity are proved. The general helper keeps its actual measure-preserving premise explicit; the concrete graph shear internally supplies that premise by the Jacobian proof above.

Outstanding: the weak chain rule for nonsmooth Sobolev states, transformation of the original PDE to the actual elliptic coefficient matrix, H¹₀/H² transport, construction and localization of graphs for the original smooth domains, and the uniform convex-domain estimate. No such step is asserted here.
