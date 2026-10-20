# T243 / C259: actual coordinate level charts and local height

This stage constructs geometry from the original analytic level function, for the boundary regularity route of Corollary A.2 (`paper/main.tex:2659–2665`). It remains AUXILIARY, coverage 18/26.

The coordinate level map is F(x)=x+(g(x)−x_r)e_r. Its r coordinate is exactly g(x); every other coordinate is exactly x_i. Its actual derivative is I+e_r⊗(Dg−e_r*), and a rank-one determinant calculation in the true orthonormal basis proves det DF=D_rg. Nonzero original Dg supplies an actual coordinate r with D_rg≠0 by the basis spanning identity. No invertible derivative or preexisting graph chart is assumed.

At a regular point c, the actual inverse function theorem applied to this derivative constructs an open partial homeomorphism e whose forward map is exactly F. The original globally analytic g supplies forward analytic regularity, and the inverse theorem supplies analytic inverse on an actual open target neighborhood after restriction. The inverse's level and tangential coordinates are proved from the true right inverse identity: g(e⁻¹y)=y_r and (e⁻¹y)_i=y_i for i≠r.

Resetting only the normal coordinate to a=g(c) gives Q(x)=x+(a−x_r)e_r. Q is globally invariant under normal translation. The actual height ψ(x)=(e⁻¹(Qx))_r is therefore globally normal-invariant as a function, even though its analytic regularity is presently local. The actual open set V=Q⁻¹(target e) contains c; ψ is analytic on V, ψ(c)=c_r, and the constructed graph point x+(ψ(x)−x_r)e_r is exactly e⁻¹(Qx) there. Thus g of that graph point equals a. On V intersect source e, g(x)=a if and only if x_r=ψ(x). All functions, open sets and identities are produced by the theorem.

Finally the original exponential-sum smooth inner domains supply their actual analytic g and boundary nonzero derivative through T230. Their boundary point satisfies g(c)=1/2; the concrete theorem therefore produces the coordinate and height with exact level 1/2 identities. It does not insert an abstract regular chart as an input.

This is an actual local level-graph construction. It does not yet prove which side of that graph represents the original sublevel set, nor construct a globally smooth bounded-slope height agreeing locally. The inverse function is globally defined but its regularity outside V is not claimed. Those geometric tasks, the cutoff neighborhoods and finite localization, and the uniform convex-domain Hessian inequality remain outstanding. No general-domain paper status is promoted.
