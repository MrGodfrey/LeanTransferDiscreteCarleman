module

public import Carleman.Control.SupportedRegionSpace
public import Carleman.Control.BochnerKernelSpace
public import Carleman.Spatial.CartesianCellControlSupport

/-! Actual reconstructed control support, and recovery of regional controls from supported Bochner limits. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem cartesianTimeControl_supported (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ωsharp ω : Set (SpatialCoordinates d)) (hω : MeasurableSet ω)
    (hcell : ∀ a : CartesianInteriorIndex N, cartesianInteriorPoint o δ N a ∈ ωsharp →
      cartesianDualCell o δ N a ⊆ ω) (g : TimeGrid)
    (u : Fin g.steps → CartesianPhysicalControl o δ hδ N ωsharp) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 g.period),
      timeCellReconstruction g (fun i => cartesianCellControl o δ hδ N ωsharp (u i)) t ∈
        Physical.supportedRegionSpace ω := by
  change ∀ᵐ t ∂volume.restrict (Ioc 0 g.period),
    (Physical.restrictRegionCLM ωᶜ)
      (timeCellReconstruction g (fun i => cartesianCellControl o δ hδ N ωsharp (u i)) t) = 0
  let L := Physical.restrictRegionCLM
    (ν := volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) (E := ℝ) ωᶜ
  have hm := timeCellReconstruction_mem_bochnerKernel g L
    (fun i => cartesianCellControl o δ hδ N ωsharp (u i)) (fun i =>
      (Physical.mem_supportedRegionSpace_iff ω hω _).mpr
        (cartesianCellControl_zero_outside o δ hδ N ωsharp ω hcell (u i)))
  exact (mem_bochnerKernelSpace_iff L _
    (timeCellReconstruction g (fun i => cartesianCellControl o δ hδ N ωsharp (u i)))).mp hm

theorem cartesianTimeControl_supported_small_mesh {ωsharp ω : Set (SpatialCoordinates d)}
    (hc : IsCompact (closure ωsharp)) (ho : IsOpen ω) (hinc : closure ωsharp ⊆ ω) :
    ∃ h0 > (0:ℝ), ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (h : ℝ), 0 < h → h ≤ h0 → (∀ j, δ j ≤ h) →
      ∀ (g : TimeGrid) (u : Fin g.steps → CartesianPhysicalControl o δ hδ N ωsharp),
        ∀ᵐ t ∂volume.restrict (Ioc 0 g.period),
          timeCellReconstruction g (fun i => cartesianCellControl o δ hδ N ωsharp (u i)) t ∈
            Physical.supportedRegionSpace ω := by
  obtain ⟨h0,hh0,hcells⟩ := cartesianDualCell_subset_region hc ho hinc
  refine ⟨h0,hh0,?_⟩
  intro o δ hδ N h hh hsmall hstep g u
  exact cartesianTimeControl_supported o δ hδ N ωsharp ω ho.measurableSet
    (hcells o δ hδ N h hh hsmall hstep) g u

theorem supportedBochner_zeroExtension
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {ν : Measure Ω} (μ : Measure Ξ)
    (ω : Set Ω) (hω : MeasurableSet ω) (u : Lp (Lp ℝ 2 ν) 2 μ)
    (hu : ∀ᵐ t ∂μ, u t ∈ Physical.supportedRegionSpace ω) :
    ∃ v : Lp (Lp ℝ 2 (ν.restrict ω)) 2 μ,
      (Physical.restrictRegionCLM (ν := ν) (E := ℝ) ω).adjoint.compLp v = u ∧ ‖v‖ = ‖u‖ := by
  let R := Physical.restrictRegionCLM (ν := ν) (E := ℝ) ω
  let v := R.compLp u
  have he : R.adjoint.compLp v = u := by
    apply Lp.ext
    filter_upwards [R.adjoint.coeFn_compLp v,R.coeFn_compLp u,hu] with t ht hr hs
    rw [ht,hr,Physical.restrictRegion_adjoint ω hω]
    exact Physical.zeroExtend_restrict_of_supported ω hω (u t) hs
  refine ⟨v,he,?_⟩
  have hn : ‖R.adjoint.compLp v‖ = ‖v‖ := by
    rw [Lp.norm_def,Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [R.adjoint.coeFn_compLp v] with t ht
    rw [ht,Physical.restrictRegion_adjoint ω hω,zeroExtendLp_norm]
  exact hn.symm.trans (congrArg norm he)

theorem exists_regional_control_weak_subsequence
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {ν : Measure Ω} (μ : Measure Ξ)
    [TopologicalSpace.SeparableSpace (Lp (Lp ℝ 2 ν) 2 μ)]
    (ω : Set Ω) (hω : MeasurableSet ω) (u : ℕ → Lp (Lp ℝ 2 ν) 2 μ)
    (hu : ∀ n, ∀ᵐ t ∂μ, u n t ∈ Physical.supportedRegionSpace ω)
    {C : ℝ} (hb : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : Lp (Lp ℝ 2 (ν.restrict ω)) 2 μ, ‖v‖ ≤ C ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ z : Lp (Lp ℝ 2 ν) 2 μ,
        Tendsto (fun n => inner ℝ (u (φ n)) z) atTop
          (𝓝 (inner ℝ ((Physical.restrictRegionCLM (ν := ν) (E := ℝ) ω).adjoint.compLp v) z)) := by
  obtain ⟨v0,hv0,hvn,φ,hφ,ht⟩ := exists_bochnerKernel_weak_subsequence
    (Physical.restrictRegionCLM (ν := ν) (E := ℝ) ωᶜ) μ u hu hb
  obtain ⟨v,he,hn⟩ := supportedBochner_zeroExtension μ ω hω v0 hv0
  refine ⟨v,hn.trans_le hvn,φ,hφ,?_⟩
  intro z
  rw [he]
  exact ht z

end Carleman
