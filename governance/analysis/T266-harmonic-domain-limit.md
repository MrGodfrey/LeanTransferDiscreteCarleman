# T266 / C282: actual weighted zero extension and periodic harmonic fields

This auxiliary stage links the T265 spatial coefficient limits with actual periodic Bochner fields on the original domain. It does not yet assert the full original-domain heat estimate.

`SubdomainWeightedExtension` constructs the genuine L² zero-extension CLM via the adjoint of actual restriction and proves its a.e. identity. Any pair of bounded spatial multipliers agreeing on the inner domain commutes with the actual extension; when the domain is contained in the outer domain the multiplier seminorm is preserved exactly. This applies to the same Gaussian spatial profile at every time and every exponent, and the genuine W cutoff. The time-square identity uses the actual compLp representative and actual time integral; no q/T-dependent loss is introduced.

`HarmonicLpMap` proves the actual two-coefficient harmonic Bochner map is continuous, with explicit sqrt(T) bound used only for fixed-T convergence. It also commutes with every actual spatial CLM. `DirichletHarmonicFields` identifies the original harmonic graph's actual value, time derivative, operator and weak gradient with the corresponding four harmonic L² fields. In particular, the weak spatial gradient is obtained from the same original domain jet, using genuine weak-jet value uniqueness and the original trajectory identity.

`DirichletHeatFields` packages these four genuine Bochner fields in their original L² product and defines their actual domain-zero-extension CLM. This does not declare an extended inner solution to be in the outer operator domain. `HarmonicDomainLimit` uses T265's actual resolvent coefficient approximations for both harmonic coefficients, the exact field identities and harmonic-map continuity to construct actual inner periodic graphs whose four zero-extended fields converge strongly to those of the same original harmonic graph.

All inner states solve their own genuine original domain/periodic-graph conditions; no H² extension or abstract replacement operator is used. No approximation premise is left in the final increasing-open-exhaustion theorem. The sqrt(T) bound is solely continuity at fixed T, not a multiplier of the CE constant. Finite sums and closure to the full original periodic graph, and application of T264's common estimate, are the next stage. AUXILIARY, P024 incomplete, 20/26 unchanged.

Validation and all 23 explicit declarations are recorded in the canonical ledger, with exact local source/build/axiom evidence and independent mathematical acceptance.
