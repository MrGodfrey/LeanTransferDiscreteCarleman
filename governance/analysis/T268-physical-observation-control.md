# T268 / C284: original Theorems 7.2 and 7.3

The original targets are physical observability (`paper/main.tex:1827`, P014) and approximate null control (`paper/main.tex:2032`, P015). This stage supplies the general bounded convex-polytope P1 branch. The unchanged `box_cartesian_physical_observability` and `box_cartesian_physical_control` supply the original Cartesian branch on boxes in arbitrary positive dimension. The result is on the full discrete spaces and actual regional control spaces.

## Actual P1 load estimate

`finite_halfspace_p1_physical_load_carleman` takes a bounded finite intersection of strict affine halfspaces in dimension d+1 ≤ 3, a nonempty open observation region, and the original fixed shape and local-grading bounds. The continuous estimate is T267's full original-domain result, with one Gaussian profile and constants before all meshes, periods and weights. Original H² graph regularity comes from `finite_halfspace_dirichlet_graph_estimate` and `finite_halfspace_dirichlet_domain_le_h2`; the common allowed-weight family is provided by `dirichlet_allowed_family_uniform` for that same profile and actual operator. The finite-halfspace boundary-chart theorem supplies the actual bounded Lipschitz domain internally.

The numerical data use the genuine conforming P1 space, actual consistent-mass Hilbert structure, true Galerkin stiffness, original L² load projection and actual regional observation. `full_p1_numericalData` supplies N1–N5, including its proved weighted projection test; no numerical assumption is left as an input. The operator symmetry gives zero stiffness defect. The existing complete transfer theorem yields the physical load estimate for every state with

qmax ≤ κ min(h^(-4/5), dt^(-2/5)).

The choice κ = min(κtransfer, δnum), together with h ≤ 1, internally ensures h qmax ≤ δnum. All constants precede the mesh, time grid, q and discrete state. The spatial finite-index universe does not restrict the state space.

## Actual observability and controls

`finite_halfspace_p1_physical_observation_control` applies the proved uniform physical cutoff/absorption theorem to this full load estimate. It retains the original conditions h ≤ h0, dt ≤ min(Δ0,T/12), dt M ≤ 1/2, and 16 qb ≤ Smax ≤ qb T/(4 dt), with the original `physicalBaseAmplitude` and `physicalMeshScale`. Arbitrary bounded real potential multipliers are projected to the same conforming space; their actual symmetric operators and operator-norm bounds are used. The constants qc, κ, h0, Δ0, Cb and d0 are chosen before T and M; the physical constant is chosen before all meshes, potentials and initial states.

The first conjunct of `PhysicalObservationControl` is precisely the actual adjoint estimate at p0 with the dt sum of actual B* observations at previous time nodes and exp(-2 d0 Smax) times the terminal norm squared. The second conjunct gives, for every original y0, an actual regional control and a forward trajectory solving the actual discrete equation, with control norm at most sqrt(Cphys) times the initial norm and terminal norm at most sqrt(Cphys) exp(-d0 Smax) times that norm. The square root is simply the paper's renamed positive control constant, with the same uniformity. No solution or terminal-value controllability is assumed as an input.

The existing Cartesian declarations use the actual mass-weighted grid state space, the genuine Cartesian Laplacian and regional control extension. They are included explicitly in the fixed-version paper coverage and independent review. P1 dimension d+1 ≤ 3 with d+1 positive includes both original d=2 and d=3; the theorem also permits dimension one. The original compactly contained nonempty open control region satisfies the weaker inclusion used here. Mesh face matching, boundary fitting, shape regularity and allowed local grading are the encoded original mesh assumptions, not additional analytic premises.

Actual build and recursive axiom evidence are attached only after successful execution. P014/P015 require independent exact-version paper acceptance; these descriptions do not themselves promote coverage.
