# T265 / C281: genuine strong domain-exhaustion limits

This auxiliary stage supplies the spatial approximation needed to transfer the uniform inner-domain heat estimate to the original domain. It proves actual full-sequence H¹ convergence, not just weak subsequence compactness.

For nested open domains T⊆S and the same original L² load f, the inner weak Poisson solution v has load f restricted to T. Actual H¹₀ zero extension E gives the exact gradient pairing identity and adjoint load identity. The original and inner variational equations imply ∇(u−Ev) is orthogonal to every gradient of an extended inner H¹₀ test. Applying this to v and to a genuine compact smooth test φ supported in T yields the best-test bound

    ‖∇(u−Ev)‖ ≤ ‖∇(u−φ)‖.

The original outer-domain slab Poincare estimate then gives

    ‖u−Ev‖_{full H¹ jet} ≤ (2R+1) ‖u−φ‖_{full H¹ jet}.

On an increasing open exhaustion, every original compact test is eventually supported in an inner domain. The actual H¹₀ closure provides arbitrarily close tests. Thus the whole sequence of actual inner solutions, extended by zero in H¹, converges strongly to the same original solution. No assumed approximation, compact embedding or new regularity premise is used.

For any L² field f, the actual restricted field extended by zero equals 1_T f almost everywhere. The squared difference is bounded by ‖f‖², which is genuinely integrable. Actual eventual membership and dominated convergence yield full L² convergence on the original domain, including the operator loads. This vector-valued result requires only a normed additive group.

`InnerGraphLimit` constructs inner graph coefficients using the actual zero-shift coercive resolvent of the restricted original operator load. It proves the exact inner operator identity, and strong convergence of zero-extended values, genuine weak gradients and operator loads to those of the original graph coefficient. A concrete theorem supplies all increasing-cover geometry for any shifted exponential smooth inner exhaustion of a bounded finite half-space domain. No choice of center or extra nonempty-inner premise is needed for this spatial result; the later heat estimate will use a tail containing its fixed center.

Zero extension is used only for H¹ states and L² fields. In particular, the extended inner H² solution is never asserted to lie in the outer operator domain or H². This distinction preserves the genuine boundary distribution. P024 still requires the periodic/time-energy passage. Scope AUXILIARY, coverage 20/26.

Ten explicit declarations, root imports and fixed-source local build/recursive axiom audit are recorded in the canonical ledger, followed by independent acceptance.
