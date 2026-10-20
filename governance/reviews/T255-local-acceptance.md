# T255 / C271 independent local acceptance

- checked_sha: `2b7dfa5b8dc39445682940c02d91c5bec5a747a0`
- mathematical_base: `4a84f2b095e71ea776fa79ecf2d568f28270cbe1`
- reviewed_at: `2026-10-20T10:23:07+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 10/10 explicit declarations (9 theorems, 1 definition); no blocking or corrective finding.**
- scope: **AUXILIARY**, compactly supported original H²∩H¹₀ states on either coordinate half-space, plus the stated positive-dimensional full-space counterpart. Paper coverage stays **18/26**; P023 / Corollary A.2 is not promoted.
- evidence_source: `local`; no remote CI gate, remote artifact claim, or redundant full rebuild.

## Original meaning and exact scope

I read the fixed `CompactHalfspaceDensity.lean` in full, its complete audited declaration types, the T255 analysis and mathematical specification, and `paper/main.tex:2659–2665`. The original Corollary A.2 concerns the Dirichlet Laplacian and its full spatial assumptions on the specified convex polytope/box domains. This stage supplies a flat-boundary strong density step useful for that route; it does not itself prove the original general-domain H² regularity or the uniform convex-domain estimate.

Here `dirichletH2JetSpace S` is the actual H² weak-jet subspace whose H¹ truncation belongs to the original H¹₀ closure. It is not H²₀ and does not impose a vanishing normal derivative. A `SpatialTest univ` is a genuine globally compactly supported smooth function. The final half-space sequence has pointwise zero values on the entire actual frontier, each H¹ truncation lies in the original H¹₀ space, and its full H² jets converge to the same original `u.val`. This is stronger than convergence only of values or selected derivative coordinates.

The compact support assumption is the stated restricted-a.e. scalar-value identity outside K. It does not require a continuous representative of u, classical derivatives of u, or K to lie inside the open half-space. K can meet or cross the boundary plane and may be empty. The final half-space theorem takes r : Fin d, so its positive-dimensional qualification is intrinsic. The full-space theorem explicitly retains `0 < d` and `u : dirichletH2JetSpace univ`; it is not a theorem about dimension zero or arbitrary noncompactly supported H² states. Its explicit conclusion is the sequence and full H² convergence; it discards the helper’s additional boundary/membership conjuncts rather than restating them.

## Declaration-by-declaration review

All names below have prefix `Carleman.`. Source lines refer to the fixed new module; raw lines refer to the fixed local `axioms.txt` named below. Each full printed type was inspected together with its proof, not only its name or specification.

| Declaration | Source / raw line | Result and checked content |
| --- | --- | --- |
| `SpatialTest.cutoffH2Transfer_roundtrip` | 13 / 44370 | PASS. Both genuine support inclusions and ηu=u a.e. recover the same complete original H² jet after two actual cutoff transfers. The inner target-a.e. formula is legitimately transported between nonnested domains. |
| `exists_compact_localbox_strong_h2_approximation` | 34 / 44379 | PASS. The helper explicitly assumes its genuine box, cutoff, support agreements, and source regularity. The off-K value condition supplies ηu=u, and the actual box sequence and roundtrip give the stated full H² limit, frontier zero values, and H¹₀ membership. |
| `signedCoordinateHalfspace` | 60 / 44395 | PASS. Boolean true means `{x | 0 < x r}`; false means `{x | x r < 0}`. No boundary points are included. |
| `signedCoordinateHalfspace_isOpen` | 63 / 44397 | PASS. Actual continuous coordinate evaluation gives openness for both signs. |
| `dirichletH2Regular_signedHalfspace` | 69 / 44400 | PASS. Tangential translation leaves coordinate r unchanged. The prior weak-Poisson regularity theorem applies to all original H¹₀ weak solutions and produces their H² lifts internally. |
| `exists_signedHalfspace_box_cutoff` | 83 / 44403 | PASS. Any compact K yields R>0, an actual smooth cutoff equal to 1 on K, and a positive-sided box attached to the correct plane. Coordinate norm bounds prove both full-support inclusions. |
| `exists_compact_halfspace_strong_h2_approximation` | 122 / 44411 | PASS. All box/cutoff/regularity qualifications are internally discharged. One sequence has the three stated properties for all n, on either half-space, for the same original state. |
| `dirichletH2Regular_univ` | 134 / 44425 | PASS. Explicit d>0 provides a coordinate; full-space tangential invariance invokes the same actual weak regularity theorem without assuming the desired H² lift. |
| `exists_fullspace_box_cutoff` | 141 / 44427 | PASS. An actual compact-support cutoff fits in the symmetric coordinate box with bounds −R,R; each side is strictly positive. |
| `exists_compact_fullspace_strong_h2_approximation` | 152 / 44430 | PASS. The internally supplied box/cutoff and full-space regularity yield genuine global compact smooth approximants converging in the entire original H² topology. |

The fixed C271 and T255 declaration lists match these ten source declarations and the root imports/audit entries. No additional explicit declaration is omitted.

## Critical proof checks

**Roundtrip and null sets.** The first transfer supplies an identity a.e. on T, whereas the return must be checked on S. The proof uses `ae_restrict_iff'` with measurable T to obtain a whole-space a.e. conditional statement `x ∈ T → ...`, then restricts that conditional statement to S. It does not assume S⊆T or transport an unrestricted representative identity from T to S. At a point of S with η≠0, the actual support inclusion gives x∈T. The double indicator formula then contains η(ηu), and the actual ηu=u identity is used twice. At η=0, that same hypothesis forces u=0. Only after obtaining the scalar L² equality does `WeakSobolevJet.value_injective` on the open domain identify every weak derivative field. No global η²=η assertion is used.

**Localization returns the original state.** For the generic helper, η=1 on K and u=0 a.e. off K produce ηu=u on a single full-measure set. The state first transferred into the box is a real H² jet with genuine H¹₀ membership. Its regularity is supplied by the already proved box theorem. The fixed cutoff-return map is continuous for the complete H² topology, so the box approximation converges to its actual returned jet. The roundtrip equality identifies this limit with the original u. This uses continuity of a fixed map, not a uniform bound across all cutoffs or boxes; there is no rate or such uniform norm claim in the conclusion.

**Geometry and both signs.** Compactness supplies a ball containing K with strictly positive radius even when K is empty. The cutoff has full topological support in that open ball. Tangential box bounds are −R,R. On the upper half-space the normal interval is (0,R); on the lower one it is (−R,0). The estimate |xᵢ|≤‖x‖<R and the actual normal sign establish half-space∩tsupport η⊆box. Conversely the box’s r-bound directly gives membership in the half-space. The construction needs neither K⊆half-space nor an interior buffer between K and its boundary plane. It is the intersection of the half-space with the cutoff support that fits the attached box.

**Regularity is proved for the needed domains.** I checked the actual invocation of `exists_dirichlet_H2_of_tangential_invariance`: arbitrary original H¹₀ weak data and the complete SpatialTest Poisson identity are its inputs. For j≠r, coordinate invariance supplies the true translated-domain condition. The previously proved tangential difference-quotient bounds, mixed weak derivative symmetry, and isolation of the normal-normal derivative in the original weak equation produce a full H² jet with the same H¹ truncation. Neither the helper definition `DirichletH2Regular` nor its half-space/full-space proof presupposes that desired H² state. This is a regularity property of given weak solutions, not an assertion of solvability for every right-hand side.

**Actual smooth outputs and boundaries.** The imported box density theorem supplies global compact smooth functions with true zero boundary values. The return construction multiplies these actual functions by the actual cutoff. The dependency proves frontier preservation by equality of the two domains on the open set {η≠0}; where η=0 the product itself vanishes. This is a pointwise boundary argument, not evaluation of an Lp equivalence class on a null boundary. The H¹₀ membership and complete H² convergence use the actual cutoff PDE and closed graph map. No full H² zero extension across a boundary is silently assumed.

The generic local-box theorem exposes source regularity as an auxiliary input; the final half-space/full-space instances supply it internally. Their other hypotheses are exactly the actual original-state membership and compact a.e. support conditions stated above. There is no supplied approximating sequence, derivative convergence, target estimate, or extra smoothness of u.

## Dependency boundary

The fixed recursive Carleman import closure contains **296 modules**. Its **295 old modules are byte-identical to the mathematical base**; the only new module is `CompactHalfspaceDensity.lean`. I read the actual `StrongH2CutoffTransfer` and `BoundaryCutoffTransfer` constructions, the compact smooth cutoff construction, the tangential-invariance regularity argument, and the relevant full H² box density interfaces. In particular, the transfer PDE contains the genuine product terms ηf−2∇η·∇u−(Δη)u; both support directions justify its test transport and its target H¹₀ qualification.

The independently frozen T254 report was read and its committed bytes verified:

- report commit `8bb726bb7a7ce8fa35f60288e135c3dc6976f988`, file `governance/reviews/T254-local-acceptance.md`;
- checked proof `4a84f2b095e71ea776fa79ecf2d568f28270cbe1`, reviewed_at `2026-10-20T10:16:23+00:00`;
- 28/28 PASS; report 14,120 bytes, SHA256 `5f758128d72b74f47e3a8f82cd450098152e1124b280e90dfe8081676f372c16`.

That report was committed after the T255 proof, so it is a separately verified acceptance record, not claimed to be part of the proof tree. Actual dependency source equality was checked against the accepted versions: `DirichletDifferenceQuotient` at `528c5bf683ace24836aecdf64ddd73422a000473`, `InteriorSmoothCutoff` at `3d418d76a4959a094dcd26d2d157c213f297531d`, `BoxStrongH2Density` at `032d2ae56bb04dd52015641301e4f4903fc0a1ab`, and `BoundaryCutoffTransfer` at `4acd24f5158fda6688403c600ddbd9d2a131c379`. Their actual uses here respect the required open domains, complete weak equations, and support qualifications.

## Exact local evidence

I independently compared the fixed Git blobs with `/tmp/carleman-t255-local-source-manifest.txt`: **all 1,052 unique entries** match the exact tracked Lean sources and pinned toolchain/build files. The manifest is 114,188 bytes, SHA256 `48873b7c8a857bcccda9257b65f540ad4a43b7a9ed852a9a27497b3adae729d9`. The comparison is to the checked Git object, not a future worktree.

`/tmp/carleman-t255-local-evidence.json` has source `local`, status PASS, checked/source SHA both equal the proof above, actual build/audit command exit codes 0, and finished_at `2026-10-20T10:15:40.023409+00:00`. The read logs confirm:

| Evidence | Checked result | Bytes / SHA256 |
| --- | --- | --- |
| `/tmp/carleman-t255-target-build.log` | Target build succeeded, 3,481 jobs | 112 / `a89b355aeaae87c6df1a3bd166c332cbc5d883e0de891c77365e38769a2a1d9a` |
| `/tmp/carleman-t255-build.log` | Root build succeeded, 4,294 jobs | 80 / `14699bb670980215286deaa976fa194f3601cc7ecacb1adbda91141ed580f123` |
| `/tmp/carleman-t255-axioms.log` | Empty audit stderr | 0 / `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/carleman-t255-compact-halfspace-density-local-axioms.txt` | Full types and recursive audit PASS for 10,200 declarations | 3,419,218 / `6806fe55bb8a07710529d3ecae4aefb44102075006a3e906cde6c0f822907e88` |

All ten new printed dependency lists contain only `propext`, `Classical.choice`, and `Quot.sound`. Across the fixed raw output, the 4,096 printed axiom lists and 10 no-axiom records introduce no nonstandard axiom; the actual namespace-wide recursive audit covers 10,200 declarations, including generated helpers. Its collection/allowlist logic is unchanged from the base. There is no `sorryAx` or added mathematical axiom in the checked dependencies.

Lean is 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); the manifest pin and clean mathlib checkout agree at `56a005855ea17e0b0958f73ec801ae140b0a1679`. The fixed original paper remains SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`. The project instruction/protocol files match their previously read versions. These are verified local executor outputs tied to the fixed source; this report does not claim a new reviewer rebuild or remote CI success.

## Acceptance disposition

**Accept T255/C271 as AUXILIARY.** No mathematical or evidence defect was found in the ten explicit declarations. The same original compactly supported H²∩H¹₀ state is approximated, including the real full H² topology and, for the half-space theorem, true frontier zero values and original H¹₀ membership of every term. General curved-boundary density, its global finite gluing, the weak uniform convex Hessian estimate, and the original polytope exhaustion remain outside this acceptance. No paper-level status is advanced. This report and reviewed_at are frozen upon its single-file commit.
