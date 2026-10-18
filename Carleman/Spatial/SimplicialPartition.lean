module

public import Carleman.Spatial.SimplicialCells

/-! Finite partitions by genuine nondegenerate simplices. This records
coverage and interior disjointness; face matching and shape regularity are
additional mesh properties and are not asserted by this structure. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {ι : Type*} [Fintype ι]

structure SimplicialPartition (S : Set (SpatialCoordinates d)) (ι : Type*) where
  simplex : ι → Affine.Simplex ℝ (SpatialCoordinates d) d
  inside : ∀ i, simplicialCell (simplex i).points ⊆ closure S
  cover : S ⊆ ⋃ i, simplicialCell (simplex i).points
  disjoint : Pairwise fun i j => Disjoint (interior (simplicialCell (simplex i).points))
    (interior (simplicialCell (simplex j).points))

namespace SimplicialPartition
variable {S : Set (SpatialCoordinates d)} (M : SimplicialPartition S ι)

abbrev cell (i : ι) : Set (SpatialCoordinates d) := simplicialCell (M.simplex i).points

omit [Fintype ι] in
theorem vertex_mem_closure (i : ι) (k : Fin (d+1)) : (M.simplex i).points k ∈ closure S :=
  M.inside i (subset_convexHull ℝ _ (Set.mem_range_self k))

theorem cells_union : (⋃ i, M.cell i) = closure S := by
  apply le_antisymm
  · exact iUnion_subset M.inside
  · exact closure_minimal M.cover (isClosed_iUnion_of_finite fun i => (simplicialCell_compact _).isClosed)

theorem ae_partition (hS : MeasurableSet S) :
    ∀ᵐ x ∂(volume.restrict S), ∃ i, x ∈ M.cell i ∧ ∀ j, x ∈ M.cell j → j=i :=
  simplicialCells_ae_partition (fun i => (M.simplex i).points) S M.cover M.disjoint hS

variable [IsFiniteMeasure (volume.restrict S)]

/-- Actual conforming P1-type space; the caller supplies only V and the
finite simplicial partition, not an unrelated finite dimensional X. -/
def conformingSpace (V : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) :
    Submodule ℝ (Lp ℝ 2 (volume.restrict S)) :=
  conformingPiecewiseAffineSpace M.cell (fun _ => simplicialCell_measurable _)
    (simplicialRadius fun i => (M.simplex i).points)
    (fun i => Filter.Eventually.of_forall fun _ hx => simplicialCell_norm_le _ i hx) V

instance conformingSpace_finiteDimensional (V : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) :
    FiniteDimensional ℝ (M.conformingSpace V) := by
  unfold conformingSpace
  infer_instance

theorem conformingSpace_le (V : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) :
    M.conformingSpace V ≤ V := inf_le_right

theorem mem_conformingSpace_iff (hS : MeasurableSet S)
    (V : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) (u : Lp ℝ 2 (volume.restrict S)) :
    u ∈ M.conformingSpace V ↔
      u ∈ V ∧ ∀ i, ∃ c : Fin (d+1) → ℝ, ∀ᵐ x ∂(volume.restrict S), x ∈ M.cell i →
        u x = c 0+∑ j : Fin d, c j.succ*x j :=
  mem_conformingPiecewiseAffineSpace_iff _ _ _ _ (M.ae_partition hS) V u

end SimplicialPartition
end Carleman
