# T242 / C258: actual boundary localization and change of domain

This stage supplies boundary-crossing localization toward Corollary A.2 (`paper/main.tex:2659–2665`). It remains AUXILIARY, coverage 18/26. The original boundary graphs still have to be constructed.

A cutoff η is a genuine globally smooth compactly supported function. Its support may cross the original boundary; it is not required to be compactly supported inside the original domain S. The target T is another open domain. Two separate support qualifications are kept explicit: S∩tsupport η⊆T ensures the cut-off original test approximants belong to H¹₀(T), while T∩tsupport η⊆S ensures every target test multiplied by η is a valid original test. Agreement of S and T near the cutoff supplies both, without requiring a global inclusion in either direction.

The actual original H¹₀ state u is extended by zero as a proved full H¹ jet and restricted to T, giving v. The new state is the actual bounded smooth product ηv. Value and all weak gradient identities are explicit, as is continuity of the cutoff operator. The true original test-closure approximants of u, after zero extension/restriction and multiplication, converge in the full weak H¹ topology to this state. Their genuine smooth supports lie in T by the first qualification. Hence ηv is genuinely in H¹₀(T), rather than just labelled as zero on a boundary.

The source and target can differ globally. For a test supported in both domains, actual full-space test jets, restriction/zero-extension adjoint pairings and exact same-function relabelling prove equality of its source and target gradient/load pairings. Applying this to ηφ for every target test φ and using the original weak Poisson identity yields the full target equation with explicit true L² load

    η E(f) − Σ_i [2(D_iη)D_i v + (D_i²η)v].

Here E is actual zero extension from S followed by restriction to T. Every coefficient and derivative multiplier is built from η and its actual smooth compact derivative tests. The weak product identity is proved at H¹ level; no H² state, zero extension of H², or Laplacian equation across the uncut original boundary is assumed. In particular no boundary distribution of the uncut extension is silently discarded. Both first-derivative cross terms and the second-derivative cutoff terms are retained with the correct negative signs.

The precise AE value identity is η·1_S u on T. If η=1 on an open R⊆S∩T, a full H² solution of the resulting target equation restricts to an H² jet whose complete H¹ truncation is exactly the original u restricted to R. The general recovery helper explicitly takes a target Dirichlet H² regularity property. The two final actual graph-domain corollaries discharge that property internally using T241, for either epigraphs or hypographs with the stated global smoothness and height/slope Lipschitz bounds. They do not assume a target H² state or a transformed equation.

All domains, source/target restriction measures, original state, original load and complete test families are preserved. These local graph consequences still require the actual cutoff support/domain agreement and graph data. Their geometric construction, finite localization of the original smooth inner domains, and the uniform convex-domain Hessian bound remain outstanding. No paper result is promoted.
