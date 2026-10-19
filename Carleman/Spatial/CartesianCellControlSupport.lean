module

public import Carleman.Spatial.CartesianCellReconstruction
public import Carleman.Geometry.KuhnAllowedWeightComparison
public import Mathlib.Topology.MetricSpace.Thickening

/-! Compactly contained active nodes give actual control support inside the original region. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Metric
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem cartesianDualCell_dist_le (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    {h : ℝ} (hh : 0 ≤ h) (hstep : ∀ j, δ j ≤ h) (a : CartesianInteriorIndex N)
    {x : SpatialCoordinates d} (hx : x ∈ cartesianDualCell o δ N a) :
    dist x (cartesianInteriorPoint o δ N a) ≤ (d:ℝ)*h := by
  apply closedCoordinateBox_diameter_bound
    (fun j => cartesianInteriorPoint o δ N a j-δ j/2)
    (fun j => cartesianInteriorPoint o δ N a j+δ j/2)
    (fun j => by linarith [hδ j]) h hh (fun j => by linarith [hstep j])
  · exact fun j => ⟨(hx j).1.le,(hx j).2.le⟩
  · exact fun j => ⟨by linarith [hδ j],by linarith [hδ j]⟩

theorem cartesianDualCell_subset_region {ωsharp ω : Set (SpatialCoordinates d)}
    (hc : IsCompact (closure ωsharp)) (ho : IsOpen ω) (hinc : closure ωsharp ⊆ ω) :
    ∃ h0 > (0:ℝ), ∀ (o δ : Fin d → ℝ) (_hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (h : ℝ), 0 < h → h ≤ h0 → (∀ j, δ j ≤ h) →
      ∀ a : CartesianInteriorIndex N, cartesianInteriorPoint o δ N a ∈ ωsharp →
        cartesianDualCell o δ N a ⊆ ω := by
  obtain ⟨ε,hε,hthick⟩ := hc.exists_cthickening_subset_open ho hinc
  refine ⟨ε/(d+1:ℝ),div_pos hε (by positivity),?_⟩
  intro o δ hδ N h hh hh0 hstep a ha x hx
  apply hthick
  apply mem_cthickening_of_dist_le x (cartesianInteriorPoint o δ N a) ε (closure ωsharp)
    (subset_closure ha)
  have hb := cartesianDualCell_dist_le o δ hδ N hh.le hstep a hx
  have hmul : h*(d+1:ℝ) ≤ ε := (le_div_iff₀ (by positivity : (0:ℝ)<d+1)).mp hh0
  linarith

theorem cartesianCellControl_zero_outside (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ωsharp ω : Set (SpatialCoordinates d))
    (hcell : ∀ a : CartesianInteriorIndex N, cartesianInteriorPoint o δ N a ∈ ωsharp →
      cartesianDualCell o δ N a ⊆ ω) (u : CartesianPhysicalControl o δ hδ N ωsharp) :
    ∀ᵐ x ∂volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
      x ∉ ω → cartesianCellControl o δ hδ N ωsharp u x = 0 := by
  have he := cartesianCellIsometry_ae o δ hδ N
    (cartesianPhysicalControlExtension o δ hδ N ωsharp u)
  filter_upwards [he] with x hx
  intro hout
  change cartesianCellIsometry o δ hδ N (cartesianPhysicalControlExtension o δ hδ N ωsharp u) x = 0
  rw [hx]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : cartesianInteriorPoint o δ N a ∈ ωsharp
  · exact Set.indicator_of_notMem (fun hxa => hout (hcell a ha hxa)) _
  · have hz : cartesianPhysicalControlExtension o δ hδ N ωsharp u a = 0 := by
      change (if ha : cartesianInteriorPoint o δ N a ∈ ωsharp then u ⟨a,ha⟩ else 0)=0
      simp only [dite_eq_right ha]
    simp [hz]

theorem cartesianCellControl_support_small_mesh {ωsharp ω : Set (SpatialCoordinates d)}
    (hc : IsCompact (closure ωsharp)) (ho : IsOpen ω) (hinc : closure ωsharp ⊆ ω) :
    ∃ h0 > (0:ℝ), ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (h : ℝ), 0 < h → h ≤ h0 → (∀ j, δ j ≤ h) →
      ∀ u : CartesianPhysicalControl o δ hδ N ωsharp,
        ∀ᵐ x ∂volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)),
          x ∉ ω → cartesianCellControl o δ hδ N ωsharp u x = 0 := by
  obtain ⟨h0,hh0,hcells⟩ := cartesianDualCell_subset_region hc ho hinc
  refine ⟨h0,hh0,?_⟩
  intro o δ hδ N h hh hsmall hstep u
  exact cartesianCellControl_zero_outside o δ hδ N ωsharp ω
    (hcells o δ hδ N h hh hsmall hstep) u

end Carleman
