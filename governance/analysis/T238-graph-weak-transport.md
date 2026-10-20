# T238 / C254: actual weak graph-coordinate transport

This is the nonsmooth Sobolev counterpart of T237, on the proof route toward the original Corollary A.2 (`paper/main.tex:2659–2665`). It remains AUXILIARY, with accepted paper coverage 18/26. The original weak state is not assumed smooth, H², or supported in finitely many modes.

For the actual graph shear F(y)=y+ψ(y)e_r and every open target domain T, the source is exactly S=F⁻¹T and both spaces use their actual restricted Euclidean volume. T237 supplies the measure-preserving map. Given original distributional derivatives D_i u=v_i and D_r u=v_r, the theorem proves

    D_i(u∘F) = v_i∘F + (D_iψ)(v_r∘F)

as an identity of actual L² equivalence classes tested against every compact smooth test on S. ψ is globally smooth and Lipschitz and independent of the normal coordinate. There is no extra weak chain-rule, transformed-gradient or Piola identity assumption.

First, the normal derivative is transported directly by testing the original identity with φ∘F⁻¹. The inverse classical chain rule has no normal correction because D_rψ=0. For the general direction, the same inverse test gives the actual correction involving the slope multiplier D_iψ. The already transported normal derivative, multiplied by this slope, removes the correction: its normal derivative is zero, as proved in T237. The bounded smooth product rule is applied to the true compact test, and the scalar identities are combined using the actual L² isometry. All signs and the normal slope invariance come from explicit pointwise identities. The proof merges only finitely many AE representative equalities per test, without assigning point values to an L² equivalence class.

`WeakSobolevJet.graphShearPullback` constructs the full H¹ jet from the transported value and all these actual gradient components. Its value is precisely the real L² composition and its gradient has the formula above. Complete graph-topology convergence follows componentwise from the L² isometry, the fixed bounded multiplication maps, and the true gradient-field assembly; it is not merely scalar L² convergence.

For a real compact smooth test, the constructed jet equals the classical smooth-test pullback. Equality is proved using actual scalar L² identity plus weak-jet uniqueness, whose hypotheses include the actual open preimage and its restricted volume. Consequently the full original H¹₀ test-span closure maps to the actual H¹₀ closure of S, by continuity and the same approximating tests. Zero boundary condition is thus proved, not separately postulated.

The scalar L² norm is exactly preserved. The complete gradient field obeys the explicit conservative estimate

    ‖∇(u∘F)‖₂² ≤ d (1+C)² ‖∇u‖₂²,

where C is the original global Lipschitz constant of ψ. No state-dependent derivative bound or limiting-step parameter enters this constant.

Still outstanding: H² transport, the actual transformed elliptic matrix and original PDE, construction/localization of graph heights for the analytic boundary charts, and the uniform convex-domain Hessian estimate. No general smooth-domain or polytope paper result is promoted here.
