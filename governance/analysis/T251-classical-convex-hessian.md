# T251 / C267: classical uniform Miranda–Talenti estimate on original inner domains

This stage completes the classical uniform Hessian estimate used toward original Corollary A.2 (`paper/main.tex:2659–2665`). It remains AUXILIARY, coverage 18/26: the original weak H²∩H¹₀ states still need boundary-preserving strong approximation.

For a continuous defining function g and S={g<a} with compact closure, a continuous F strictly positive on the true frontier is strictly positive on a sufficiently thin closed inner level layer. The proof forms the genuine compact bad set closure(S)∩{F≤0}. Any point in that set has g<a, because a closure point outside S is a true frontier point. If the bad set is nonempty, its actual maximum of g is attained at c with g(c)<a; choosing r=(a−g(c))/4 excludes every bad point with g≥a−2r. If it is empty the conclusion is immediate. No boundary distance or level-set identification is assumed.

Apply this to F=flux(u,g)+δ‖∇g‖², δ>0. True nonnegative boundary flux and nonzero boundary Dg give strict positivity there. The actual layer support from T250 and κ≥0 then give, uniformly for all sufficiently small positive ε,

    κε flux(u,g) ≥ −δ κε‖∇g‖²

at every point, including points where κ=0. The original flux is continuous by its actual C∞ construction.

The boundary-layer mass is uniformly bounded by the finite original domain integral

    ∫κε‖∇g‖² = ∫ηε Δg ≤ ∫_S |Δg| = M.

The comparison uses 0≤η≤1 and exact vanishing outside S; the right side is truly integrable because Δg is continuous on the compact closure. It does not require Δg≥0, a bound on κ itself, a surface measure or a coarea theorem. All products involving κ are integrable from its actual compact support and smoothness. Consequently the exact T249 identity gives the uniform weighted defect bound

    ∫ηε[(Δu)²−HessSq(u)] ≥ −δM.

For every continuous F, the actual cutoffs satisfy ∫ηεnF→∫_S F when εn>0 and εn→0. The proof uses pointwise indicator convergence and the genuine integrable dominating function 1_S|F|; it handles the boundary pointwise as zero and requires no boundary-null hypothesis. Apply this to the actual continuous Hessian defect, with εn=1/(n+1). For each δ>0 the layer bound holds eventually, so the integral limit is ≥−δM. Taking the same positive scalar sequence δn→0 gives a nonnegative limit. Separating the two genuinely integrable square terms yields

    ∫_S Σ_{i,j}(D_iD_ju)² ≤ ∫_S (Δu)².

The concrete final theorem applies to every original exponential inner domain of a bounded finite strict halfspace intersection and every globally C∞ u with actual zero values on its true frontier. Its actual compact closure, nonzero boundary derivative and boundary flux sign are all supplied internally from previous proven original geometry and the true zero data. No thin-layer bound, flux condition, chart, cutoff, candidate Hessian or uniform constant is an input to that final statement. The constant is exactly 1 and independent of n, the chosen charts, the level gradient and u. The dimension is arbitrary, including trivial zero-dimensional implications where the premises allow them.

This proves a classical estimate, not yet the same estimate for arbitrary weak H²∩H¹₀ states. The full ordered classical square sum has not yet been transferred through a boundary-preserving strong approximation to the original weak derivative components. That density/transfer and the original polytope exhaustion remain pending; P023 is not promoted.
