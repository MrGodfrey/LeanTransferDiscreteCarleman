module

public import Carleman.Spatial.AffineSimplexShapeInverse

/-! A genuine affine change between any two full-dimensional simplices. -/
@[expose] public noncomputable section
namespace Carleman
variable {d : ℕ} (T U : Affine.Simplex ℝ (SpatialCoordinates d) d)

def simplexCoordinateLinearEquiv : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d :=
  (((simplexAffineBasis T).basisOf 0).equiv ((simplexAffineBasis U).basisOf 0)
    (Equiv.refl _)).toContinuousLinearEquiv

theorem simplexCoordinateLinearEquiv_sub (i : Fin (d+1)) :
    simplexCoordinateLinearEquiv T U (T.points i-T.points 0) = U.points i-U.points 0 := by
  by_cases hi : i=0
  · subst i
    simp only [sub_self,map_zero]
  · have h := Module.Basis.equiv_apply ((simplexAffineBasis T).basisOf 0)
      (i := ⟨i,hi⟩) ((simplexAffineBasis U).basisOf 0) (Equiv.refl _)
    simp only [AffineBasis.basisOf_apply,Equiv.refl_apply,simplexAffineBasis_apply,
      vsub_eq_sub] at h
    exact h

def simplexCoordinateShift : SpatialCoordinates d :=
  U.points 0-simplexCoordinateLinearEquiv T U (T.points 0)

theorem affineSimplex_coordinate_eq :
    affineSimplex T (simplexCoordinateLinearEquiv T U) (simplexCoordinateShift T U) = U := by
  apply Affine.Simplex.ext
  intro i
  rw [affineSimplex_points,affineChange_apply]
  have h := simplexCoordinateLinearEquiv_sub T U i
  rw [map_sub] at h
  dsimp only [simplexCoordinateShift]
  calc
    _ = (simplexCoordinateLinearEquiv T U (T.points i)-
        simplexCoordinateLinearEquiv T U (T.points 0))+U.points 0 := by abel
    _ = (U.points i-U.points 0)+U.points 0 := by rw [h]
    _ = U.points i := sub_add_cancel _ _

def referenceSimplex (n : ℕ) : Affine.Simplex ℝ (SpatialCoordinates n) n := by
  let B : AffineBasis (Fin (n+1)) ℝ (SpatialCoordinates n) := Classical.choice
    (AffineBasis.exists_affineBasis_of_finiteDimensional (k := ℝ) (V := SpatialCoordinates n)
      (P := SpatialCoordinates n) (ι := Fin (n+1)) (by simp [SpatialCoordinates]))
  exact ⟨B,B.ind⟩

theorem simplex_shape_inverse (n : ℕ) (κ : ℝ) (hκ : 0 < κ) : ∃ C > (0:ℝ),
    ∀ (U : Affine.Simplex ℝ (SpatialCoordinates n) n) (a : SpatialCoordinates n)
      (r h : ℝ), 0 < r → 0 < h →
      Metric.ball a r ⊆ simplicialCell U.points → h ≤ κ*r →
    ∀ c : Fin (n+1) → ℝ,
    ‖simplexNodalGradientLp U c‖ ≤ (C/h)*‖simplexNodalLp U c‖ := by
  obtain ⟨C,hC,hbound⟩ := affineSimplex_shape_inverse (referenceSimplex n) κ hκ
  refine ⟨C,hC,?_⟩
  intro U a r h hr hh hball hshape c
  have hU := affineSimplex_coordinate_eq (referenceSimplex n) U
  have hb := hbound (simplexCoordinateLinearEquiv (referenceSimplex n) U)
    (simplexCoordinateShift (referenceSimplex n) U) a r h hr hh
  rw [hU] at hb
  exact hb hball hshape c

end Carleman
