# T239 / C255: full weak Hessian transport in both directions

This stage proves actual H² invariance under the T237 graph shear, for the boundary regularity route toward Corollary A.2 (`paper/main.tex:2659–2665`). It remains AUXILIARY, with paper coverage 18/26. It does not assume that the original PDE has already been transformed or that the graph height has been constructed from the original domain.

Inputs are an arbitrary open original domain T, the same globally smooth height ψ independent of the normal coordinate, a global Lipschitz bound C for ψ, and global Lipschitz bounds B_i for its actual slopes D_iψ. The last bounds are explicit additional geometry qualifications, not inferred from boundedness of first derivatives alone.

For an original H² jet U, write G_i=D_iU and H_ij=D_jG_i, P for the actual restricted-volume L² pullback, w_i=D_iψ, and dw_ij=D_jw_i. T238 applies to the original weak chains of each G_i, giving Q_ij=P(H_ij)+w_j P(H_ir). The actual smooth bounded product rule then proves the derivative of the already constructed H¹ pullback gradient:

    D_j [P(G_i)+w_i P(G_r)]
      = Q_ij + w_i Q_rj + dw_ij P(G_r).

Every term is an actual L² class. The dw_ij multiplier is internally constructed from the actual slope's Fréchet derivative and its given Lipschitz bound B_i. No transformed second derivative, H² chain rule, or gradient smoothness is assumed. The finite family of weak derivative identities yields all original test bounds, and the existing symmetric H² assembly constructs V with exact truncation to the same H¹ pullback.

With H=‖field₂U‖ and M=‖field₁U‖, all second derivative components are bounded by L=(1+C)²H+(Σ_i B_i)M. Thus ‖field₂V‖²≤card(Sym(Fin d,2))L². The bound is conservative, explicit, and independent of approximation or difference-quotient parameters. The real L² representative of V is explicitly the original value composed with F, almost everywhere on the actual preimage domain.

The inverse map is proved to be exactly the graph shear for −ψ. Its actual slope is −D_iψ, so both original Lipschitz constants C and B_i remain valid. Applying the established H² transport to this genuine inverse yields a state on F⁻¹'s actual preimage of F⁻¹T, proved equal to the original T. Actual AE composition identities are transported through the measure-preserving inverse, and weak-jet uniqueness then proves that the resulting H² jet truncates to the same original u, not to a replacement representative or a distinct solution. An explicit reverse Hessian bound and a two-sided H²-membership equivalence are included.

Only the input which is being transported is assumed H². The reverse theorem starts with original u in H¹ and an H² realization of its actual pullback; it derives original H². This is the direction needed after the half-space regularity theorem. Zero boundary conditions, when needed, are supplied by the already proved T238 H¹₀ transport and the exact truncation identities.

Remaining work includes the actual transformed coefficient matrix and PDE, localized graph construction for the smooth inner domains, and uniform convex-domain Hessian control before the original exhaustion limit. No general-domain paper result is promoted here.
