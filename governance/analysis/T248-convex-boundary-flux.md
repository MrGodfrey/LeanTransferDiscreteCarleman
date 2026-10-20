# T248 / C264: the actual convex boundary flux

This auxiliary stage toward original Corollary A.2 (`paper/main.tex:2659–2665`) proves the classical pointwise Miranda–Talenti boundary sign on the actual exponential-sum inner domains. Coverage remains 18/26; no uniform Sobolev estimate or paper-level result is claimed yet.

The existing graphSlopeVector is connected to the actual derivative by the Euclidean orthonormal expansion: inner(∇f,v)=Df(v). Thus a nonzero actual derivative gives a nonzero gradient, and Du=qDg implies ∇u=q∇g. The original spatialLaplacian is proved to be the trace of the actual second Fréchet derivative.

For any vector N, put p=‖N‖² and w_i=p e_i−N_i N. These are actual tangent vectors: inner(N,w_i)=0. For every real continuous bilinear form H, with no symmetry assumption, direct bilinearity and the full orthonormal expansion give

    Σ_i H(w_i,w_i) = p (p Σ_i H(e_i,e_i)−H(N,N)).

Both mixed sums equal H(N,N); Σ_i N_i²=p. This identity uses neither a selected tangent frame nor division, and remains valid in dimension zero or at N=0.

Define the genuine flux against the unnormalized outward level gradient by

    F(u,g,c) = Δu(c) inner(∇u(c),∇g(c)) − D²u(c)[∇u(c),∇g(c)].

The actual Laplacian and flux are globally C∞ for globally C∞ inputs. Given the already proved actual first and tangential second boundary identities, with N=∇g(c), the algebra above yields exactly

    p F(u,g,c) = q² Σ_i D²g(c)[w_i,w_i].

No sign of q is imposed. If Dg(c) is nonzero and its actual Hessian is positive semidefinite, p>0 and the right side is nonnegative, so F≥0. The concrete final theorem supplies both boundary identities from T247, the nonzero original derivative from the original inner-domain regularity theorem, and the actual Hessian positivity from the computed exponential square sum. Its only function/geometry inputs are globally C∞ u, original zero values on the true frontier, a true inner point and a true frontier point; no gradient/Hessian identity, curvature, or flux sign is assumed there.

The pointwise statement is classical. Weighted integration by parts, passage from smooth zero boundary functions to the original H²∩H¹₀ weak solution, a uniform Hessian estimate and exhaustion to the original polytope are still pending. No boundary trace is assigned to a Sobolev function by this stage and no coercive estimate is inferred merely from pointwise positivity.
