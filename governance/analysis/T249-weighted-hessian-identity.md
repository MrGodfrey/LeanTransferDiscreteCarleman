# T249 / C265: exact weighted Hessian and boundary-layer identities

This is an auxiliary classical integration stage toward original Corollary A.2 (`paper/main.tex:2659–2665`); coverage remains 18/26. Functions are globally C∞. Only the weight η must have compact support; u and g need not vanish near the boundary or have compact support. All integrations use actual Euclidean volume and actual derivatives.

A compact smooth factor times any smooth factor is genuinely integrable. The existing whole-space integration-by-parts theorem then gives ∫f D_e g=−∫D_e f g when f is smooth and compactly supported. Differentiated compact factors retain compact support. Applied twice, with all product-rule terms retained and actual mixed derivatives commuting, this yields

    ∫η(D_e f D_v g−D_v f D_e g)
      =∫(D_eη D_vf−D_vη D_ef)g.

Taking f=D_vu, g=D_eu and commuting the actual second derivatives gives the weighted Hessian pair identity, with its negative sign on the weight-derivative terms. Every integrand needed to separate and recombine integrals is proved integrable from actual compact support, including the derivatives of η. Finite summation gives the true ordered Hessian square sum H(u)=Σ_{i,j}(D_iD_ju)² and

    ∫η[(Δu)²−H(u)]
      =−∫Σ_{i,j}[(D_iη)(D_iu)(D_jD_ju)−(D_jη)(D_iu)(D_iD_ju)].

The source also expands the already defined genuine flux F=Δu inner(∇u,∇g)−D²u[∇u,∇g] into exactly the corresponding double coordinate sum. The two basis expansions preserve the original derivative order; the finite sum exchange is explicit. Hence, for a true derivative identity Dη=−κDg,

    ∫η[(Δu)²−H(u)] = ∫κ F(u,g).

This helper explicitly retains the derivative identity as an input. The actual smooth level cutoff and its chain rule will supply it in the next stage; no curvature or flux positivity is smuggled into this identity. κ is an arbitrary real function here: all rewritten integrands are equal to the proved compact-factor expressions, so the result does not silently assert integrability of an unrelated function.

A second actual integration-by-parts computation gives

    ∫η Δg=−∫Σ_i(D_iη)(D_ig),
    ∫κ‖∇g‖²=∫η Δg   when Dη=−κDg.

This supplies the exact boundary-layer mass identity without surface measure or an assumed coarea formula. It is not itself a uniform bound: the actual cutoff, support, positivity and limiting arguments are still to be supplied. No boundary term has been discarded by pretending u is compactly supported inside a domain. Strong approximation of the original H²∩H¹₀ solution, the convex uniform estimate, and exhaustion to the original polytope remain pending.
