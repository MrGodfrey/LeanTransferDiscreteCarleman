# T033 — Actual projected weighted test and uniform temporal bound

Scope CONDITIONAL. No concrete mesh superapproximation, approximation or
continuous Dirichlet heat CE is claimed. P011/P014/P015 remain incomplete.

For any complete real L2 subspace X, F(t)=sigma(t) composed with its inclusion.
`galerkinWeightedTest=F.adjoint*F` is proved equal to the actual orthogonal
projection of sigma(sigma z), the original Pi_h(sigma²z). Its pairing equals
the actual weighted L2 pairing, hence it is symmetric and nonnegative, and
its quadratic form equals the square of the multiplier seminorm. It is not
an unspecified test map chosen to satisfy the desired inequalities.

The actual derivative D(t) of the weight multiplier in operator norm is
already proved in TemporalMultiplier. Here the test derivative is
F'(t).adjoint*F(t)+F(t).adjoint*F'(t). The quadratic time derivative is proved
using the actual HasDerivWithinAt multiplier result and inner-product calculus
on the full closed interval. Endpoint equality follows from the actual
periodic q trace; q itself is never differentiated by a formal symbol.

The relative multiplier derivative bound gives
|<z,T'(t)z>| ≤ 2 beta (|tau|+rho.bound) (q(t)||sigma(t)z||)^2,
and therefore the uniform constant Ctime=2 beta(tauStar+rho.bound).
This constant is independent of T, X, dimension, h, dt, qmax and z. No weighted
projection stability estimate is used to prove this time bound: the projection
is removed using its exact pairing, and the logarithmic derivative acts on
the already weighted state. Both signs of rho have the same bound.

`GalerkinSuperapprox` is exactly the remaining spatial N4 inequality for this
specific test. `galerkinWeightedTestData` constructs every original N4 field
from that single spatial inequality: op, derivative, periodic endpoint,
HasDerivWithinAt, symmetry, nonnegativity and the uniform time bound are all
supplied internally. Superapproximation uses the original V-valued double
weight action and its original preservation witness, inverse weight, and
Csuper*h*qmax scale. It has not been proved for a mesh here.

`ProjectedHeatData` retains original AllowedFamily, N3 approximation, this
spatial N4 superapproximation and continuous A4. Its toGalerkin constructor
builds N4 for both signs/all |tau|≤tauStar, with the single explicit Ctime.
The data itself need not include beta: beta is carried by the actual
TimeWeightRegularity argument when constructing the test derivative.

`projected_heat_observation_control_uniform` sets this Ctime before choosing
all transfer and physical constants, then calls the actual Galerkin theorem.
It preserves the original heat scale and full physical observation/control
conclusions, with all common constants chosen before the same numerical data.
It assumes neither an arbitrary test operator nor its time derivative/bound.
It still requires uniform original analytic/spatial data for every full
PhysicalQClass weight, so no concrete finite-element result is promoted.
