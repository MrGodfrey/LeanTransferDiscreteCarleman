module

public import Carleman.Spatial.AffineWeakGradient
public import Carleman.Spatial.SimplexWeightedInverse
public import Carleman.Spatial.SimplicialPartition

/-! The actual global weak gradient restricts to the polynomial gradient
on every cell, including its null boundary. No nodal representation is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem simplexCell_ae_interior (U : Affine.Simplex ℝ (SpatialCoordinates d) d) :
    simplicialCell U.points =ᵐ[volume] interior (simplicialCell U.points) := by
  have hnull : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)), x ∉ frontier (simplicialCell U.points) := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using simplicialCell_frontier_null U.points
  filter_upwards [hnull] with x hx
  exact propext ⟨fun hk => (mem_interior_iff_notMem_frontier hk).mpr hx,fun hi => interior_subset hi⟩

instance simplexInterior_finiteMeasure (U : Affine.Simplex ℝ (SpatialCoordinates d) d) :
    IsFiniteMeasure (volume.restrict (interior (simplicialCell U.points))) := by
  rw [← Measure.restrict_congr_set (simplexCell_ae_interior U)]
  infer_instance

namespace SimplicialPartition
variable {ι : Type*} {S : Set (SpatialCoordinates d)} (M : SimplicialPartition S ι)

theorem cell_interior_subset (hS : IsOpen S) (hc : Convex ℝ S) (i : ι) : interior (M.cell i) ⊆ S := by
  by_cases hs : S.Nonempty
  · have he := hc.interior_closure_eq_interior_of_nonempty_interior (hS.interior_eq.symm ▸ hs)
    have hi := interior_mono (M.inside i)
    simpa only [he,hS.interior_eq] using hi
  · have he : S=∅ := Set.not_nonempty_iff_eq_empty.mp hs
    intro x hx
    have hi := M.inside i (interior_subset hx)
    simpa only [he,closure_empty] using hi

theorem cell_measure_le_domain (hS : IsOpen S) (hc : Convex ℝ S) (i : ι) :
    volume.restrict (M.cell i) ≤ volume.restrict S := by
  rw [Measure.restrict_congr_set (simplexCell_ae_interior (M.simplex i))]
  exact Measure.restrict_mono (M.cell_interior_subset hS hc i) le_rfl

theorem gradient_on_cell (hS : IsOpen S) (hc : Convex ℝ S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (i : ι)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ)
    (hu : ∀ᵐ x ∂volume.restrict S, x ∈ M.cell i → WeakSobolevJet.value u x=p x) :
    WeakSobolevJet.field 1 u =ᵐ[volume.restrict (M.cell i)]
      (fun x => derivativeOneFiber (fderiv ℝ p x)) := by
  let hIS := M.cell_interior_subset hS hc i
  let v := WeakSobolevJet.restrictSubdomain hIS u
  have hv : WeakSobolevJet.value v =ᵐ[volume.restrict (interior (M.cell i))] p := by
    rw [WeakSobolevJet.restrictSubdomain_value]
    filter_upwards [subdomainLp_ae hIS (WeakSobolevJet.value u),
      hu.filter_mono (ae_mono (Measure.restrict_mono hIS le_rfl)),
      ae_restrict_mem isOpen_interior.measurableSet] with x hx hy hz
    exact hx.trans (hy (interior_subset hz))
  have hg := WeakSobolevJet.gradient_eq_affine p isOpen_interior v hv
  have he : WeakSobolevJet.field 1 v =ᵐ[volume.restrict (interior (M.cell i))]
      WeakSobolevJet.field 1 u := subdomainLp_ae hIS (WeakSobolevJet.field 1 u)
  have hh := he.symm.trans hg
  rwa [← Measure.restrict_congr_set (simplexCell_ae_interior (M.simplex i))] at hh

end SimplicialPartition
end Carleman
