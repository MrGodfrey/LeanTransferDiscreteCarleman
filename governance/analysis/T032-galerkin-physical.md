# T032 — Actual consistent-mass Galerkin physical system

Scope CONDITIONAL: concrete P1 meshes, their weighted approximation/test
estimates and the continuous Dirichlet heat inputs remain unproved instances.
This does not promote Proposition 6.1 or Theorems 7.2/7.3.

## Constructed stiffness

For any finite-dimensional actual L2 submodule X≤a.V, conformingEnergyLift is
the inverse canonical energy/value equivalence after inclusion X→a.V. Finite
dimensionality provides continuity; no uniform bound on this lift is asserted
or used. The actual Galerkin stiffness is the Riesz inverse of the pullback
of the original symmetric coercive form to X, using X's actual L2 inner product.

Its pairing is exactly a(Rx,Ry). Symmetry, nonnegativity, uniqueness of the
operator with this pairing, and zero stiffness defect are proved. No A, no
A-symmetry/positivity hypotheses, and no defect witness enter the final physical
control theorem. The generic OriginalForm is not falsely called the concrete
Dirichlet Laplacian; specializing it remains a separate obligation.

## Constructed original numerical fields

The actual reconstruction is injective, its G=Id, and its ambient Q is the L2
orthogonal projection (followed by inclusion). Weighted ambient observation
is exactly the multiplier seminorm of the actual ambient control adjoint.
`galerkinNumericalData` supplies the original NumericalData with Cnum=1:
stiffness and defect, two reconstruction comparisons, ordinary lift and
observation compatibility are proved internally. Only original weighted N3
approximation and N4 test data are inputs. The zero defect satisfies any
nonnegative registered ηA, in particular ηA=0; no positive defect is invented.

`GalerkinHeatData` contains AllowedFamily A2/A3, N3, N4 and continuous A4.
Its toConforming constructor supplies all remaining N fields for the actual
Galerkin stiffness and defect 0. Neither a discrete CE nor observability is
hidden in its fields.

## Physical conclusion

`galerkin_heat_observation_control_uniform` calls the accepted original-data
physical theorem with Cnum=1 and the constructed stiffness. It preserves
κ,h0,Δ0,Cb,d0 before T/M and Cphys(T,M) before X, h/grid, approximation data,
potential sequence, trajectories and initial datum. Original heat Smax,
qb, mesh/dt conditions, all N+1 adjoint nodes, real region B.adjoint, L2(omega)
control, and exact forward equation remain unchanged. No estimate involving
the finite-dimensional lift norm enters the uniform constants.

The statement is still conditional on actual uniform analytic data for each
allowed full PhysicalQClass. It does not assert that every finite subspace
satisfies N3/N4, nor that every OriginalForm has continuous heat CE. Those
substantive realization obligations remain explicit.
