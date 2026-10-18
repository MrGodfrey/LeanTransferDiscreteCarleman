# T031 — Original heat transfer to physical observation and HUM

Scope: CONDITIONAL. This stage does not certify concrete P1/FD estimates or
continuous heat Carleman, and does not promote P014/P015.

`physical_cube_le_nodeEnergy` discards only the nonnegative derivative part of
the full heat energy. Heat c0=o=3; real powers are identified with natural
cubes. Actual load/observation dt-weighted sums are identified exactly.
`physical_load_carleman_of_transfer` uses the original minus orientation and
load equation on every periodic state/load; physical observation is not an input.

For X an actual complete L2 submodule contained in V, `conformingReconstruction`
has R the inclusion into V and J the actual orthogonal projection onto X.
The mass-adjoint identity is proved. `conformingLoad` has Γ=J and ordinary
lift=identity. State seminorms compose the actual spatial multiplier with the
inclusion; load/control seminorms are actual multiplication norms. Definiteness
follows from the existing nonvanishing exponential weight. The intermediate
ambient observation uses the already calculated actual control adjoint.

`ConformingHeatData` packages original AllowedFamily (A2/A3), NumericalData
(N1–N5), and continuous A4 on genuine weak periodic trajectories and Sobolev
geometry. It is data, not a proof that those assumptions have concrete
instances. It contains neither periodic discrete CE nor physical observability.
Concrete P1 meshes must still supply these objects; FD's different mass and
reconstruction are not supplied by this conforming specialization.

`conforming_heat_load_uniform` invokes accepted `OriginalForm.heat_scale_uniform`.
Fixed analytic/numerical constants, original graph regularity and profile
smoothness precede κ,h0,Δ0,CCE. Those precede X, its inclusion in V, A/defect,
T/grid, weight, h/errors and data. The orders are aE≤Cap*h, a0+ηA≤Cap*h²;
the scale is qmax≤κ min(h^(-4/5),dt^(-2/5)). Full original transfer supplies the
periodic CE, from which actual PhysicalLoadCarleman follows. No error bridge
or discrete CE is assumed.

`conforming_heat_observation_control_uniform` chooses κ,h0,Δ0 from transfer,
then Cb,d0 from the accepted physical construction, all before T/M. For
T>0,M≥0 it chooses Cphys(T,M), before finite-dimensional X, g/h, A, defect,
errors, potentials, trajectories and initial data. Smax is exactly
κ min(h^(-4/5),dt^(-2/5)); original h≤h0, dt≤Δ0,T/12, dt*M≤1/2 and
16qb≤Smax≤qb*T/(4dt) remain. The caller supplies ConformingHeatData uniformly
over full PhysicalQClass and qmax≤Smax, with the same constants. The proof
invokes original transfer for each such weight and feeds the resulting CE to
the accepted actual L2(omega) observation/HUM result.

The output is the full N+1-node adjoint estimate using true B.adjoint, and an
actual L2(omega) control with a full forward solution for each y0. Its cost is
sqrt(Cphys), terminal factor exp(-d0*Smax), and squared observation remainder
exp(-2*d0*Smax). Remaining substantive obligations are concrete P1 weighted
approximations/tests and mesh bounds, the concrete Dirichlet realization and
continuous heat CE; FD requires its own physical interfaces. Conditional
acceptance cannot claim those concrete instances have been proved.
