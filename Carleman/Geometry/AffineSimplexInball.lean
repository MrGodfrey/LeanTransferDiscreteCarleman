module

public import Carleman.Spatial.AffineSimplex
public import Carleman.Spatial.SimplexNodalLp

/-! Genuine contained balls in a full-dimensional simplex and its actual
affine images, with radius controlled by the inverse operator norm. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem simplex_exists_inball (T : Affine.Simplex ℝ (SpatialCoordinates d) d) :
    ∃ a : SpatialCoordinates d, ∃ r > (0:ℝ), Metric.ball a r ⊆ simplicialCell T.points := by
  obtain ⟨a,ha⟩ := simplicialCell_interior_nonempty T
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior a ha
  exact ⟨a,r,hr,hball.trans interior_subset⟩

theorem affineSimplex_contains_ball (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (a : SpatialCoordinates d) (r : ℝ) (hball : Metric.ball a r ⊆ simplicialCell T.points)
    (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d) (b : SpatialCoordinates d)
    (Γ : ℝ) (hΓ : 0 < Γ) (hinv : ‖A.symm.toContinuousLinearMap‖ ≤ Γ) :
    Metric.ball (affineChange A b a) (r/Γ) ⊆ simplicialCell (affineSimplex T A b).points := by
  intro y hy
  rw [affineSimplex_cell]
  refine ⟨A.symm (y-b),hball ?_,?_⟩
  · rw [Metric.mem_ball,dist_eq_norm]
    have he : A.symm (y-b)-a=A.symm (y-affineChange A b a) := by
      apply A.injective
      simp only [map_sub,ContinuousLinearEquiv.apply_symm_apply,affineChange_apply]
      abel
    rw [he]
    calc
      _ ≤ ‖A.symm.toContinuousLinearMap‖*‖y-affineChange A b a‖ := A.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ Γ*‖y-affineChange A b a‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
      _ < Γ*(r/Γ) := mul_lt_mul_of_pos_left (by simpa only [Metric.mem_ball,dist_eq_norm] using hy) hΓ
      _ = r := mul_div_cancel₀ r hΓ.ne'
  · rw [affineChange_apply,ContinuousLinearEquiv.apply_symm_apply,sub_add_cancel]

end Carleman
