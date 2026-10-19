module

public import Carleman.Geometry.KuhnNearestVertex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Actual coordinate midplanes are null; nearest-vertex geometry holds almost everywhere. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem coordinate_hyperplane_volume_zero (j : Fin d) (c : ℝ) :
    volume {x : SpatialCoordinates d | x j=c}=0 := by
  let s := (affineSpan ℝ ({c} : Set ℝ)).comap (EuclideanSpace.proj j).toLinearMap.toAffineMap
  have he : (s : Set (SpatialCoordinates d))={x | x j=c} := by
    ext x
    change x j ∈ affineSpan ℝ ({c} : Set ℝ) ↔ x j=c
    simp
  have hs : s ≠ ⊤ := by
    intro ht
    have hx : (c+1) • EuclideanSpace.basisFun (Fin d) ℝ j ∈ s := by rw [ht]; trivial
    change (c+1) • EuclideanSpace.basisFun (Fin d) ℝ j ∈ (s : Set (SpatialCoordinates d)) at hx
    rw [he] at hx
    simp at hx
  rw [← he]
  exact Measure.addHaar_affineSubspace volume s hs

theorem coordinate_ne_ae (j : Fin d) (c : ℝ) :
    ∀ᵐ x : SpatialCoordinates d ∂volume, x j ≠ c := by
  simpa only [ae_iff,not_not] using coordinate_hyperplane_volume_zero j c

theorem cartesianKuhnSimplex_nearest_vertex_ae (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    ∀ᵐ x ∂volume.restrict (simplicialCell (cartesianKuhnSimplex o δ hδ z π).points),
      ∃ k : Fin (d+1), ∀ j,
        |x j-(cartesianKuhnSimplex o δ hδ z π).points k j| < δ j/2 := by
  have hn : ∀ᵐ x : SpatialCoordinates d ∂volume,
      ∀ j, x j ≠ o j+((z j:ℝ)+(1:ℝ)/2)*δ j :=
    ae_all_iff.mpr (fun j => coordinate_ne_ae j _)
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem (simplicialCell_measurable (cartesianKuhnSimplex o δ hδ z π).points)] with x hx hm
  exact cartesianKuhnSimplex_nearest_vertex o δ hδ z π hm hx

end Carleman
