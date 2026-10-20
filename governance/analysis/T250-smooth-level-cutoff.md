# T250 / C266: actual smooth interior level cutoffs

This auxiliary stage toward Corollary A.2 constructs the actual weight needed in T249; it does not assume a cutoff, its derivative identity or a layer support hypothesis. Coverage remains 18/26.

For ε>0, a real level a and the original smooth defining function g, define

    ηε(x)=smoothTransition((a−g(x)−ε)/ε),
    κε(x)=smoothTransition'((a−g(x)−ε)/ε)/ε.

Both are globally C∞ when g is. The actual transition is in [0,1] and monotone, hence 0≤ηε≤1 and κε≥0. Fermat's theorem applied to its true global minimum 0 and global maximum 1 proves that its derivative vanishes on both closed plateaus, including the transition endpoints. Thus ηε=0 for g≥a−ε and ηε=1 for g≤a−2ε; κε vanishes on both plateaus.

The actual Fréchet chain rule gives Dηε=−κεDg. The sign, division by ε and true derivative of the scalar transition are retained. The chain identity itself is algebraically valid even for ε=0 under Lean's total division; every support, positivity, compactness and limiting application explicitly requires ε>0.

Taking closures of genuine function supports gives the full topological support qualifications

    tsupport(ηε) ⊆ {g≤a−ε},
    tsupport(κε) ⊆ {a−2ε≤g≤a−ε}.

For ε>0 these closed sets place both supports strictly inside S={g<a}. If closure(S) is compact, each full support is a closed subset of that actual compact set and therefore compact. This is not merely an ordinary support inclusion or a claim of vanishing outside an unclosed shell.

For any positive sequence εn→0, ηεn(x) tends pointwise to the actual indicator of S. At each x∈S the positive margin a−g(x) makes 2εn smaller eventually, so ηεn(x)=1 eventually. Outside S all weights equal zero, including at its boundary. No assumption of negligible boundary measure is used.

Finally the concrete ηε and κε are substituted into the two T249 identities. Smoothness, compact support and the actual derivative identity are supplied internally from the original g and compact closure of its sublevel, giving

    ∫ηε[(Δu)²−Σij(DiDju)²]=∫κε F(u,g),
    ∫κε‖∇g‖²=∫ηεΔg.

The identities hold for arbitrary globally C∞ u; there is no artificial zero-near-boundary condition on u. Generic compact-closure input remains explicit and is supplied by the existing original bounded exponential-inner-domain theorem in the convex-domain application. Boundary-layer bounds and dominated convergence, the classical uniform Hessian estimate, and boundary-preserving strong H² approximation of the original weak solution remain pending. No paper result is promoted.
