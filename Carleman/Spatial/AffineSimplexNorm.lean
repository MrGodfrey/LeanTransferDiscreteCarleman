module

public import Carleman.Spatial.AffineSimplex
public import Carleman.Spatial.LpDominatedLimit

/-! Exact L² scaling of actual affine nodal polynomials and gradients. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman

theorem lp_two_norm_sq_integral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (u : Lp E 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  have h := lp_two_norm_sub_sq_integral u 0
  rw [sub_zero] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
  rw [hx,Pi.zero_apply,sub_zero]

variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
  (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d) (b : SpatialCoordinates d)

theorem simplexNodalLp_norm_sq (c : Fin (d+1) → ℝ) :
    ‖simplexNodalLp T c‖^2 =
      ∫ x in simplicialCell T.points, ‖simplexNodalInterpolant T c x‖^2 := by
  rw [lp_two_norm_sq_integral]
  exact integral_congr_ae ((simplexNodalLp_ae T c).fun_comp (fun y => ‖y‖^2))

theorem simplexNodalGradientLp_norm_sq (c : Fin (d+1) → ℝ) :
    ‖simplexNodalGradientLp T c‖^2 =
      ∫ _x in simplicialCell T.points, ‖derivativeOneFiber (simplexNodalDerivativeLinear T c)‖^2 := by
  rw [lp_two_norm_sq_integral]
  have h : simplexNodalGradientLp T c =ᵐ[volume.restrict (simplicialCell T.points)]
    (fun _ => derivativeOneFiber (simplexNodalDerivativeLinear T c)) := MemLp.coeFn_toLp _
  exact integral_congr_ae (h.fun_comp (fun y => ‖y‖^2))

theorem affineSimplex_nodal_norm_sq (c : Fin (d+1) → ℝ) :
    ‖simplexNodalLp (affineSimplex T A b) c‖^2 = affineJacobian A*‖simplexNodalLp T c‖^2 := by
  have h := integral_comp_affineChange A b (simplicialCell T.points)
    (fun y => ‖simplexNodalInterpolant (affineSimplex T A b) c y‖^2)
  simp only [affineSimplex_nodal_comp,← affineSimplex_cell,← simplexNodalLp_norm_sq] at h
  rw [h]
  field_simp [(affineJacobian_pos A).ne']

theorem affineSimplex_gradient_norm_sq (c : Fin (d+1) → ℝ) :
    ‖simplexNodalGradientLp (affineSimplex T A b) c‖^2 =
      affineJacobian A * ∫ _x in simplicialCell T.points,
        ‖derivativeOneFiber ((simplexNodalDerivativeLinear T c).comp A.symm.toContinuousLinearMap)‖^2 := by
  rw [simplexNodalGradientLp_norm_sq,affineSimplex_derivative]
  have h := integral_comp_affineChange A b (simplicialCell T.points)
    (fun _ => ‖derivativeOneFiber ((simplexNodalDerivativeLinear T c).comp A.symm.toContinuousLinearMap)‖^2)
  rw [← affineSimplex_cell] at h
  rw [h]
  field_simp [(affineJacobian_pos A).ne']

end Carleman
