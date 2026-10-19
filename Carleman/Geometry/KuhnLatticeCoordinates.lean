module

public import Carleman.Geometry.KuhnCellInterior
public import Carleman.Spatial.SimplexPositiveSupport

/-! Integral vertex coordinates of actual Kuhn cells. Each coordinate and
each coordinate difference has integral width at most one on the vertices. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def cartesianGridPoint (o δ : Fin d → ℝ) (z : Fin d → ℤ) : SpatialCoordinates d :=
  WithLp.toLp 2 (fun j => o j+(z j:ℝ)*δ j)

def cartesianGridCoordinate (o δ : Fin d → ℝ) (j : Fin d) :
    SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  (δ j)⁻¹ • (EuclideanSpace.proj j).toLinearMap.toAffineMap -
    AffineMap.const ℝ (SpatialCoordinates d) (o j/δ j)

theorem cartesianGridCoordinate_apply (o δ : Fin d → ℝ) (j : Fin d)
    (x : SpatialCoordinates d) : cartesianGridCoordinate o δ j x=(x j-o j)/δ j := by
  change (δ j)⁻¹*x j-o j/δ j=_
  ring

theorem cartesianGridCoordinate_point (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (j : Fin d) :
    cartesianGridCoordinate o δ j (cartesianGridPoint o δ z)=(z j:ℝ) := by
  rw [cartesianGridCoordinate_apply]
  change (o j+(z j:ℝ)*δ j-o j)/δ j=_
  apply (div_eq_iff (hδ j).ne').mpr
  ring

def kuhnVertexIndex (z : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (k : Fin (d+1)) : Fin d → ℤ := fun j => z j+if (π.symm j).val < k.val then 1 else 0

theorem cartesianKuhnSimplex_points_eq_gridPoint (o δ : Fin d → ℝ)
    (hδ : ∀ j, 0 < δ j) (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (k : Fin (d+1)) :
    (cartesianKuhnSimplex o δ hδ z π).points k=
      cartesianGridPoint o δ (kuhnVertexIndex z π k) := by
  apply PiLp.ext
  intro j
  rw [cartesianKuhnSimplex_points]
  simp [cartesianGridPoint,kuhnVertexIndex]

theorem cartesianGridCoordinate_vertex (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (k : Fin (d+1)) (j : Fin d) :
    cartesianGridCoordinate o δ j ((cartesianKuhnSimplex o δ hδ z π).points k)=
      (kuhnVertexIndex z π k j:ℝ) := by
  rw [cartesianKuhnSimplex_points_eq_gridPoint,cartesianGridCoordinate_point o δ hδ]

theorem kuhnVertexIndex_width (z : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (k l : Fin (d+1)) (j : Fin d) :
    kuhnVertexIndex z π k j ≤ kuhnVertexIndex z π l j+1 := by
  simp only [kuhnVertexIndex]
  split_ifs <;> omega

theorem kuhnVertexIndex_difference_width (z : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (k l : Fin (d+1)) (i j : Fin d) :
    kuhnVertexIndex z π k i-kuhnVertexIndex z π k j ≤
      kuhnVertexIndex z π l i-kuhnVertexIndex z π l j+1 := by
  simp only [kuhnVertexIndex]
  split_ifs <;> omega

theorem cartesianKuhn_positive_vertex_upper (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) {x : SpatialCoordinates d}
    (hx : x ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z π).points)
    (k : Fin (d+1)) (hk : 0 < simplexBarycentric (cartesianKuhnSimplex o δ hδ z π) k x)
    (j : Fin d) (c : ℤ) (hc : cartesianGridCoordinate o δ j x ≤ (c:ℝ)) :
    kuhnVertexIndex z π k j ≤ c :=
  simplex_integer_affine_le_of_pos _ (cartesianGridCoordinate o δ j)
    (fun l => kuhnVertexIndex z π l j) (fun l => cartesianGridCoordinate_vertex o δ hδ z π l j)
    (fun l m => kuhnVertexIndex_width z π l m j) c hx hc k hk

theorem cartesianKuhn_positive_vertex_lower (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) {x : SpatialCoordinates d}
    (hx : x ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z π).points)
    (k : Fin (d+1)) (hk : 0 < simplexBarycentric (cartesianKuhnSimplex o δ hδ z π) k x)
    (j : Fin d) (c : ℤ) (hc : (c:ℝ) ≤ cartesianGridCoordinate o δ j x) :
    c ≤ kuhnVertexIndex z π k j := by
  have he := simplex_integer_affine_le_of_pos (cartesianKuhnSimplex o δ hδ z π)
    (-(cartesianGridCoordinate o δ j)) (fun l => -kuhnVertexIndex z π l j)
    (fun l => by simp [cartesianGridCoordinate_vertex o δ hδ])
    (fun l m => by have h := kuhnVertexIndex_width z π m l j; omega) (-c) hx
    (by simpa using neg_le_neg hc) k hk
  omega

theorem cartesianKuhn_positive_vertex_difference (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) {x : SpatialCoordinates d}
    (hx : x ∈ simplicialCell (cartesianKuhnSimplex o δ hδ z π).points)
    (k : Fin (d+1)) (hk : 0 < simplexBarycentric (cartesianKuhnSimplex o δ hδ z π) k x)
    (i j : Fin d) (c : ℤ)
    (hc : cartesianGridCoordinate o δ i x-cartesianGridCoordinate o δ j x ≤ (c:ℝ)) :
    kuhnVertexIndex z π k i-kuhnVertexIndex z π k j ≤ c :=
  simplex_integer_affine_le_of_pos _
    (cartesianGridCoordinate o δ i-cartesianGridCoordinate o δ j)
    (fun l => kuhnVertexIndex z π l i-kuhnVertexIndex z π l j)
    (fun l => by simp [cartesianGridCoordinate_vertex o δ hδ])
    (fun l m => kuhnVertexIndex_difference_width z π l m i j) c hx hc k hk

end Carleman
