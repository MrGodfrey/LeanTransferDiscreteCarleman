# T247 / C263: actual first and second boundary derivative identities

This stage proves the classical geometric identities needed for the convex-domain Hessian estimate toward Corollary A.2 (`paper/main.tex:2659–2665`). It remains AUXILIARY, coverage 18/26. The functions here are genuinely globally C∞; no boundary derivative is assigned to a merely H² state.

For the actual graph projection G(x)=x+(ψ(x)−x_r)e_r, local constancy of f∘G and the actual first chain rule give

    Df(c)v + (Dψ(c)v−v_r) D_rf(c) = 0.

Apply this to the original level function g and a function u with zero values on that level. Since the chosen original D_rg(c) is nonzero, the true full Fréchet derivative satisfies Du(c)=q Dg(c), with q=D_ru(c)/D_rg(c). This is proved for every direction, not assumed as a normal trace condition. If Dg(c)v=0, the same identity proves DG(c)v=v.

For h=u−qg, Dh(c)=0 and h∘G is locally constant. Differentiating the actual first chain rule once more gives D²(h∘G)(c)[v,v]=D²h(c)[DG(c)v,DG(c)v]+Dh(c)[D²G(c)[v,v]]. The second term vanishes by the already proved actual Dh(c)=0; the first becomes D²h(c)[v,v] for a true tangent v. Local constancy makes the left side zero, yielding the original tangential identity D²u(c)[v,v]=q D²g(c)[v,v]. The proof differentiates the actual continuous-linear-map-valued derivative and its evaluation; no unproved second chain rule or free Hessian is supplied.

The actual regular analytic g supplies its global smooth graph through T244. A general helper assumes u vanishes on the original whole level g=g(c) and internally constructs q and all derivative identities. For the concrete exponential sum, this is reduced to the original frontier condition: an actual interior point z and g(c)=1/2 imply the open segment from z to c lies strictly in the sublevel set by convexity, hence c belongs to its closure and, by strict-level exclusion, to its frontier. Thus every point on the level 1/2 is a true frontier point. The final concrete theorem consequently uses only actual zero values on the original frontier, not a stronger unstated zero-level assumption.

The actual second derivative of the original finite exponential sum is explicitly calculated:

    D²g_n(x)[v,v] = Σ_i exp((n+1)(b_i−ℓ_i x)) ((n+1)ℓ_i v)² ≥ 0.

Both minus signs from the first and second differentiation are accounted for. This is the actual Fréchet Hessian and holds for all x and v, with no geometry or PDE hypotheses. Together these facts supply the geometric inputs for the boundary flux sign.

The pointwise flux algebra, integrated Hessian identity, boundary-preserving strong approximation of H²∩H¹₀ states, uniform estimate and original-polytope exhaustion remain to be proved. Classical zero-value statements are not substituted for unproved Sobolev traces or density. No paper-level status is promoted.
