module

public import Carleman.Spatial.ConformingLocalPolynomial

/-! Exact integration over a genuine finite simplicial partition. Shared
cell boundaries have zero volume and no term is counted twice. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

omit [Fintype ι] in
theorem cell_restrict_domain (hS : IsOpen S) (hc : Convex ℝ S) (i : ι) :
    (volume.restrict S).restrict (M.cell i) = volume.restrict (M.cell i) := by
  have hi := simplexCell_ae_interior (M.simplex i)
  rw [Measure.restrict_congr_set (hi.filter_mono ae_restrict_le),
    Measure.restrict_restrict_of_subset (M.cell_interior_subset hS hc i),
    ← Measure.restrict_congr_set hi]

theorem integral_eq_sum_cells (hS : IsOpen S) (hc : Convex ℝ S)
    (f : SpatialCoordinates d → ℝ) (hf : Integrable f (volume.restrict S)) :
    (∫ x in S, f x) = ∑ i, ∫ x in M.cell i, f x := by
  classical
  have he : f =ᵐ[volume.restrict S] (fun x => ∑ i, (M.cell i).indicator f x) := by
    filter_upwards [M.ae_partition hS.measurableSet] with x hx
    obtain ⟨i,hi,hu⟩ := hx
    rw [Finset.sum_eq_single i]
    · exact (Set.indicator_of_mem hi f).symm
    · intro j _ hji
      exact Set.indicator_of_notMem (fun hj => hji (hu j hj)) f
    · simp
  calc
    _ = ∫ x in S, ∑ i, (M.cell i).indicator f x := integral_congr_ae he
    _ = ∑ i, ∫ x in S, (M.cell i).indicator f x :=
      integral_finsetSum _ (fun i _ => hf.indicator (simplicialCell_measurable (M.simplex i).points))
    _ = ∑ i, ∫ x in M.cell i, f x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (simplicialCell_measurable (M.simplex i).points),M.cell_restrict_domain hS hc i]

end Carleman.SimplicialPartition
