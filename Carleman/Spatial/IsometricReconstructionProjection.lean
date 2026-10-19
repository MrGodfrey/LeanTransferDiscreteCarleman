module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Exact best approximation by an isometric reconstruction followed by its genuine adjoint. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Carleman
variable {X H : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (E : X →ₗᵢ[ℝ] H)

theorem reconstruction_adjoint_left_inverse (v : X) : E.toContinuousLinearMap.adjoint (E v) = v := by
  have he := congrArg (fun L : X →L[ℝ] X => L v) E.adjoint_comp_self
  exact he

theorem reconstruction_residual_orthogonal (u : H) (v : X) :
    inner ℝ (u-E (E.toContinuousLinearMap.adjoint u)) (E v) = 0 := by
  change inner ℝ (u-E (E.toContinuousLinearMap.adjoint u)) (E.toContinuousLinearMap v) = 0
  rw [← ContinuousLinearMap.adjoint_inner_left,map_sub,reconstruction_adjoint_left_inverse,
    sub_self,inner_zero_left]

theorem reconstruction_error_pythagoras (u : H) (v : X) :
    ‖u-E v‖^2 = ‖u-E (E.toContinuousLinearMap.adjoint u)‖^2 +
      ‖E.toContinuousLinearMap.adjoint u-v‖^2 := by
  have he : u-E v = (u-E (E.toContinuousLinearMap.adjoint u)) +
      E (E.toContinuousLinearMap.adjoint u-v) := by rw [map_sub]; abel
  rw [he,norm_add_sq_real,reconstruction_residual_orthogonal,LinearIsometry.norm_map]
  ring

theorem reconstruction_best_approximation (u : H) (v : X) :
    ‖u-E (E.toContinuousLinearMap.adjoint u)‖ ≤ ‖u-E v‖ := by
  have he := reconstruction_error_pythagoras E u v
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg (‖E.toContinuousLinearMap.adjoint u-v‖)])

end Carleman
