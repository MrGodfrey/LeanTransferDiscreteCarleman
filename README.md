# Lean Transfer Discrete Carleman

[![Lean CI](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/workflows/lean-ci.yml/badge.svg)](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/workflows/lean-ci.yml)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0-blue)](lean-toolchain)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 / mathlib formalization of **continuous-to-fully-discrete Carleman
estimates for parabolic equations**, together with their finite element,
finite difference, observability, and control applications.

The mathematical source is **Qi Lü and Yu Wang, _From Continuous to Fully
Discrete Carleman Estimates: A Transfer Principle for Parabolic Schemes_**
([arXiv:2610.02983](https://arxiv.org/abs/2610.02983)).
The precise reference for this formalization is the manuscript snapshot in
[`paper/paper.pdf`](paper/paper.pdf) and [`paper/main.tex`](paper/main.tex);
its provenance and checksums are recorded in the
[source manifest](paper/SOURCE_MANIFEST.md).

**Status:** all **26 named results** in that snapshot have Lean proofs and
recorded independent mathematical reviews. The
[result-by-result coverage table](governance/PAPER_COVERAGE.md) links paper
statements to Lean declarations, and the
[final acceptance record](governance/FINAL_ACCEPTANCE.md) identifies the checked
commits and evidence. Section 8 numerical experiments are outside this
formalization deliverable.

[Mathematics](#what-is-formalized) · [Reusable components](#reusable-components) ·
[Build](#building-and-checking-the-proofs) · [Citation](#citation) ·
[License](#license)

## What is formalized?

The central result transfers a continuous Carleman inequality to a fully
discrete backward Euler scheme with a conforming spatial reconstruction.
The proof assigns a continuous auxiliary problem to each discrete state,
estimates the weighted reconstruction error, and absorbs that error under
explicit mesh and weight conditions.

For either time orientation, the resulting estimate has the form

$$
\mathcal E_{q,h,\delta t}(z)
\le C\left(
\|D_\pm z+A_hz\|_{\ell^2_{\delta t}(X_h),\theta}^{\,2}
+
\|q^{o/2}B_h^*z\|_{\ell^2_{\delta t}(U_h),\theta}^{\,2}
\right).
$$

The development includes both this residual formulation and the formulation
with a prescribed load. The abstract theorem applies to the full discrete
state space, with constants chosen uniformly over the admissible periods,
meshes, time steps, and weights after fixing the structural bounds. Its
continuous Carleman and numerical compatibility assumptions remain explicit;
the intermediate error and auxiliary-solution estimates are proved.

For the heat equation, the admissible weight scale is

$$
q_{\max}\le \kappa\min\{h^{-4/5},(\delta t)^{-2/5}\}.
$$

The concrete realizations cover consistent-mass $P_1$ finite elements on locally
graded simplicial meshes in dimensions two and three, and Cartesian finite
differences in any fixed positive dimension. The downstream results treat
bounded real space-time potentials, relaxed and filtered observability,
approximate null controls with uniformly bounded cost and exponentially small
terminal errors, and continuous null-control limits under independent spatial
and temporal refinement.

### Main proof entry points

All declarations below are in the `Carleman` namespace. See the
[coverage table](governance/PAPER_COVERAGE.md) for all 26 results and their
complete declaration lists.

| Paper result | Lean entry point |
| --- | --- |
| Theorem 2.1: uniform transfer, both time directions | [`Transfer/OriginalUniform.lean`](Carleman/Transfer/OriginalUniform.lean), `OriginalForm.transfer_uniform` |
| Corollaries 2.2–2.3: general and heat-specific mesh scales | [`Transfer/ScaleUniform.lean`](Carleman/Transfer/ScaleUniform.lean), `OriginalForm.scale_uniform`; [`Transfer/HeatScaleUniform.lean`](Carleman/Transfer/HeatScaleUniform.lean), `OriginalForm.heat_scale_uniform` |
| Sections 3–4: weighted temporal, spatial, and combined errors | [`governance/PAPER_COVERAGE.md`](governance/PAPER_COVERAGE.md), entries P004–P010 |
| Proposition 6.1: full $P_1$ realization on bounded convex polytopes | [`Control/FullP1Realization.lean`](Carleman/Control/FullP1Realization.lean), `finite_halfspace_p1_realization` |
| Proposition 6.2: Cartesian finite differences | [`Spatial/CartesianBoxNumericalData.lean`](Carleman/Spatial/CartesianBoxNumericalData.lean), `cartesian_numericalData_of_box` |
| Theorems 7.2–7.3: physical observability and approximate control | [`Control/FiniteHalfspaceP1PhysicalControl.lean`](Carleman/Control/FiniteHalfspaceP1PhysicalControl.lean), `Physical.finite_halfspace_p1_physical_observation_control`; [`Control/BoxCartesianControl.lean`](Carleman/Control/BoxCartesianControl.lean) |
| Theorem 7.5 and Corollary 7.6: filtered observability and control | [`Control/FiniteHalfspaceP1FilteredControl.lean`](Carleman/Control/FiniteHalfspaceP1FilteredControl.lean); [`Control/BoxCartesianFilteredControl.lean`](Carleman/Control/BoxCartesianFilteredControl.lean) |
| Corollary 7.9: continuous null-control limits | [`Control/FiniteHalfspaceP1NullControlLimits.lean`](Carleman/Control/FiniteHalfspaceP1NullControlLimits.lean), `Physical.finite_halfspace_p1_controls_null_limits`; [`Control/CartesianNullControlLimits.lean`](Carleman/Control/CartesianNullControlLimits.lean), `Physical.box_cartesian_controls_null_limits` |
| Appendices A–B: analytic realizations, continuous heat estimates, and Cartesian approximation | [Coverage entries P022–P026](governance/PAPER_COVERAGE.md); [`Transfer/FiniteHalfspaceHeatContinuous.lean`](Carleman/Transfer/FiniteHalfspaceHeatContinuous.lean) |

## Reusable components

The library contains infrastructure that can also support other formalizations
of numerical PDEs and control theory. Each component carries its own explicit
hypotheses; importing a component does not require instantiating the full
Carleman transfer theorem.

| Component | What it provides | Starting modules |
| --- | --- | --- |
| Periodic time discretization | Positive time grids, cyclic shifts, both oriented differences, summation by parts, weighted sequence norms, and cell extensions | [`TimeGrid`](Carleman/Periodic/TimeGrid.lean), [`SummationByParts`](Carleman/Periodic/SummationByParts.lean), [`WeightedNorm`](Carleman/Periodic/WeightedNorm.lean), [`CellExtension`](Carleman/Periodic/CellExtension.lean) |
| Reconstruction and load interfaces | Reconstruction $R$, mass adjoint $J$, compositions $RJ$ and $JR$, compatible loads, and shifted discrete schemes | [`Reconstruction`](Carleman/Transfer/Reconstruction.lean), [`Load`](Carleman/Transfer/Load.lean), [`ShiftedScheme`](Carleman/Transfer/ShiftedScheme.lean) |
| Hilbert-space evolution and forms | Coercive forms, associated operators, positive square roots, and periodic weak evolution | [`CoerciveForm`](Carleman/Continuous/CoerciveForm.lean), [`FormSquareRoot`](Carleman/Continuous/FormSquareRoot.lean), [`PeriodicEvolution`](Carleman/Continuous/PeriodicEvolution.lean) |
| Weak derivatives and Dirichlet analysis | Weak Sobolev machinery, product rules, mollification, Poincaré bounds, and convex-polytope regularity | [`WeakDerivative`](Carleman/Spatial/WeakDerivative.lean), [`WeakLeibniz`](Carleman/Spatial/WeakLeibniz.lean), [`InwardMollification`](Carleman/Spatial/InwardMollification.lean), [`DirichletPoincare`](Carleman/Spatial/DirichletPoincare.lean), [`FiniteHalfspaceRegularity`](Carleman/Spatial/FiniteHalfspaceRegularity.lean) |
| Finite element and finite difference estimates | Simplex interpolation, weighted inverse bounds, Cartesian summation by parts, and coarse-to-fine prolongation | [`SimplexNodalInterpolation`](Carleman/Spatial/SimplexNodalInterpolation.lean), [`SimplexWeightedInverse`](Carleman/Spatial/SimplexWeightedInverse.lean), [`CartesianSummationByParts`](Carleman/Spatial/CartesianSummationByParts.lean), [`TensorLinearProlongation`](Carleman/Spatial/TensorLinearProlongation.lean) |
| Carleman weights and transfer | Cellwise weight comparisons, explicit error budgets, scale exponents, and the numerical interface for another scheme | [`CellLemma`](Carleman/Weights/CellLemma.lean), [`ScaleExponents`](Carleman/Transfer/ScaleExponents.lean), [`OriginalData`](Carleman/Transfer/OriginalData.lean), [`OriginalUniform`](Carleman/Transfer/OriginalUniform.lean) |
| Observability-to-control arguments | Penalized Hilbert uniqueness method (HUM), filtered control, regional reconstruction, and weak compactness | [`PenalizedHUM`](Carleman/Control/PenalizedHUM.lean), [`FilteredControl`](Carleman/Control/FilteredControl.lean), [`ReconstructedControlCompactness`](Carleman/Control/ReconstructedControlCompactness.lean) |

For example, periodic summation by parts works in any real inner product
space, without completeness or finite-dimensionality assumptions:

```lean
import Carleman.Periodic.SummationByParts

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : Carleman.TimeGrid) (u v : g.Sequence H) :
    g.pairing (g.dPlus u) v = g.pairing u (g.dMinus v) :=
  g.pairing_dPlus u v
```

Import individual modules for focused use, or `import Carleman` for the whole
development. To use this repository as a Lake dependency, keep your project's
Lean and mathlib versions compatible with the pins below and add this entry to
your `lakefile.toml`, replacing `FULL_COMMIT_SHA` with the exact revision you
intend to use:

```toml
[[require]]
name = "carleman"
git = "https://github.com/MrGodfrey/LeanTransferDiscreteCarleman.git"
rev = "FULL_COMMIT_SHA"
```

Resolve the dependency with `lake update carleman` in the **consuming project**
and commit its resulting manifest. Pin a commit for reproducibility: module
names and interfaces may evolve. For a new discretization, start with
`Section5.NumericalData` in `OriginalData.lean` and the explicit hypotheses of
`OriginalForm.transfer_uniform`.

## Building and checking the proofs

The project pins **Lean 4.35.0** and **mathlib v4.35.0**, commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
[`lake-manifest.json`](lake-manifest.json) fixes the transitive dependencies.
Avoid `lake update` when reproducing this repository's checked build.

With [Lean's Elan toolchain manager](https://github.com/leanprover/elan) and Git
installed, run:

```bash
git clone https://github.com/MrGodfrey/LeanTransferDiscreteCarleman.git
cd LeanTransferDiscreteCarleman
lake exe cache get
lake build Carleman
lake env lean tools/CheckAxioms.lean
```

Elan selects the pinned compiler from `lean-toolchain`. The cache command
downloads precompiled mathlib dependencies; the project proofs are built
locally. A first build can take substantially longer than an incremental build.

The repository also provides `bash tools/setup_lean.sh` to install Elan if
needed, restore the pinned dependencies, and fetch selected mathlib cache roots.
That script requires Bash, Git, `curl`, `tar`, `zstd`, `sha256sum`, a C toolchain,
and Python (CI uses 3.12). If Elan was newly installed, add
`${ELAN_HOME:-$HOME/.elan}/bin` to your shell's `PATH` before running Lake.
Node.js 22+ is needed only for the dashboard's JavaScript tests.

### Verification scope

The [final recorded proof audit](governance/FINAL_ACCEPTANCE.md), at mathematical
commit `99d519544e0eb8d42a955ca6bff3935c322d855f`, covers **1,080 mathematical
modules** and **10,681 declarations**. The aggregate target
[`Carleman.lean`](Carleman.lean) imports every registered mathematical module.
[`tools/CheckAxioms.lean`](tools/CheckAxioms.lean) recursively checks axiom
dependencies for every declaration in the `Carleman` namespace and rejects
anything outside `propext`, `Classical.choice`, and `Quot.sound`, including
`sorryAx`.

Lean checks the formal statements and their proofs. Correspondence with the
manuscript is documented separately through fixed-commit, independent
agent-based reviews in [`governance/reviews/`](governance/reviews/). Auxiliary
and conditional intermediate results remain identified as such and are not
counted as additional paper results. CI reproduces the build and audit;
the badge above reflects its current status, not a separate mathematical review.

## Repository guide

| Path | Contents |
| --- | --- |
| [`Carleman/`](Carleman/) | Lean library: `Periodic`, `Continuous`, `Spatial`, `Weights`, `Transfer`, and `Control` |
| [`Carleman.lean`](Carleman.lean) | Aggregate import and default build target |
| [`paper/`](paper/) | Reference manuscript, rendered PDF, and source checksums |
| [`governance/PAPER_COVERAGE.md`](governance/PAPER_COVERAGE.md) | Paper-to-Lean result map |
| [`governance/FINAL_ACCEPTANCE.md`](governance/FINAL_ACCEPTANCE.md) | Completion record and verification evidence |
| [`state/`](state/) | Machine-readable task, coverage, and verification records |
| [`tools/`](tools/) | Build, axiom-audit, validation, and dashboard scripts |
| [`docs/`](docs/) | Static progress viewer; open `docs/index.html` locally |

Historical development records are primarily in Chinese. The
[mathematical specification](governance/MATH_SPEC.md),
[project operations](governance/PROJECT_OPERATIONS.md), and
[state format](state/README.md) describe the detailed proof and evidence
workflow. The progress viewer is a snapshot generated from those records;
the repository does not currently deploy a GitHub Pages site.

## Citation

If you use the formalization, cite this repository and record the **full commit
SHA** you used (`git rev-parse HEAD`). If you use the mathematical results, also
cite the paper. [`CITATION.cff`](CITATION.cff) provides machine-readable software
metadata for GitHub's **Cite this repository** feature;
[`CITATION.bib`](CITATION.bib) contains both entries.

```bibtex
@misc{Wang2026LeanCarleman,
  author       = {Wang, Yu},
  title        = {{LeanTransferDiscreteCarleman}: A {Lean} 4 Formalization
                  of Continuous-to-Fully-Discrete {Carleman} Estimates},
  year         = {2026},
  howpublished = {GitHub repository},
  url          = {https://github.com/MrGodfrey/LeanTransferDiscreteCarleman},
  note         = {Record the full commit SHA of the version used}
}

@misc{LuWang2026Transfer,
  author        = {L{\"u}, Qi and Wang, Yu},
  title         = {From Continuous to Fully Discrete {Carleman} Estimates:
                   A Transfer Principle for Parabolic Schemes},
  year          = {2026},
  eprint        = {2610.02983},
  archivePrefix = {arXiv},
  primaryClass  = {math.NA},
  url           = {https://arxiv.org/abs/2610.02983}
}
```

Replace the software entry's `note` with `Commit <full SHA>` when citing a
specific checkout. The paper's arXiv identifier identifies the paper; the
repository URL and commit identify the formalization. The result numbering in
the coverage table refers to the bundled manuscript snapshot.

## Contributing and acknowledgments

Issues and focused pull requests are welcome. For mathematical changes, state
the relevant paper result or reusable interface, build the affected modules,
and check the axiom dependencies. Add new completed modules to `Carleman.lean`;
changes to theorem statements also require a fresh correspondence review under
the [project instructions](AGENTS.md).

The formalization is maintained by Yu Wang and was developed with AI-assisted
proof construction and separate agent-based reviews. It builds on
[Lean](https://lean-lang.org/) and
[mathlib](https://github.com/leanprover-community/mathlib4); the manuscript is
joint work of Qi Lü and Yu Wang.

## License

The original Lean code, scripts, configuration, and project documentation are
licensed under the **Apache License 2.0**; see [`LICENSE`](LICENSE) and
[`NOTICE`](NOTICE). You may reuse and adapt these components under its terms.

The bundled manuscript (`paper/main.tex` and `paper/paper.pdf`) is excluded
from this software license and retains its existing rights and licensing terms.
Third-party dependencies and any material carrying its own notice retain their
respective licenses.
