module

public import Carleman.Spatial.SimplexTaylorInterpolation

/-! True Lebesgue squared interpolation errors on a simplex, including the
actual Euclidean gradient fiber. These use classical derivative bounds. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

theorem simplexNodal_error_sq_integral
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ x ∈ simplicialCell T.points, DifferentiableAt ℝ f x)
    (L : ℝ≥0) (hL : LipschitzOnWith L (fderiv ℝ f) (simplicialCell T.points))
    {h : ℝ} (hh : 0 ≤ h)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h) :
    (∫ x in simplicialCell T.points,
      (f x-simplexNodalInterpolant T (fun i => f (T.points i)) x)^2) ≤
      (2*L*h^2)^2*volume.real (simplicialCell T.points) := by
  have hc : ContinuousOn f (simplicialCell T.points) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hi := (hc.sub (simplexNodalInterpolant T (fun i => f (T.points i))).continuous_of_finiteDimensional.continuousOn).pow 2
  calc
    _ ≤ ∫ _x in simplicialCell T.points, (2*(L:ℝ)*h^2)^2 := by
      apply integral_mono_ae (hi.integrableOn_compact (simplicialCell_compact T.points)) (integrable_const _)
      filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
      change (f x-simplexNodalInterpolant T (fun i => f (T.points i)) x)^2 ≤ (2*(L:ℝ)*h^2)^2
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
        (simplexNodal_error_of_lipschitz_derivative T f hf L hL hh hdiam hx)
    _ = _ := by simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_comm]

theorem simplexNodal_gradient_error_sq_integral
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ x ∈ simplicialCell T.points, DifferentiableAt ℝ f x)
    (L : ℝ≥0) (hL : LipschitzOnWith L (fderiv ℝ f) (simplicialCell T.points))
    {a : SpatialCoordinates d} {r h κ : ℝ} (hr : 0 < r) (hh : 0 ≤ h)
    (hball : Metric.ball a r ⊆ simplicialCell T.points) (hshape : h ≤ κ*r)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h) :
    (∫ x in simplicialCell T.points,
      ‖derivativeOneFiber (fderiv ℝ f x-
        affineScalarDerivative (simplexNodalInterpolant T (fun i => f (T.points i))))‖^2) ≤
      (‖derivativeOneFiber (d := d)‖*((1+4*κ)*L*h))^2*volume.real (simplicialCell T.points) := by
  have hk : 0 ≤ κ := by nlinarith only [hshape,hh,hr]
  have hc : ContinuousOn (fun x => derivativeOneFiber (fderiv ℝ f x-
      affineScalarDerivative (simplexNodalInterpolant T (fun i => f (T.points i)))))
      (simplicialCell T.points) := (derivativeOneFiber (d := d)).continuous.comp_continuousOn
    (hL.continuousOn.sub continuous_const.continuousOn)
  have hi := hc.norm.pow 2
  calc
    _ ≤ ∫ _x in simplicialCell T.points,
        (‖derivativeOneFiber (d := d)‖*((1+4*κ)*(L:ℝ)*h))^2 := by
      apply integral_mono_ae (hi.integrableOn_compact (simplicialCell_compact T.points)) (integrable_const _)
      filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact (derivativeOneFiber.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left
          (simplexNodal_gradient_error_of_lipschitz_derivative T f hf L hL hr hh hball hshape hdiam hx)
          (norm_nonneg _))
    _ = _ := by simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_comm]

theorem derivative_lipschitzOn_of_second_derivative_bound
    {K : Set (SpatialCoordinates d)} (hK : Convex ℝ K) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ x ∈ K, DifferentiableAt ℝ (fderiv ℝ f) x)
    (L : ℝ≥0) (hL : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ L) :
    LipschitzOnWith L (fderiv ℝ f) K :=
  hK.lipschitzOnWith_of_nnnorm_fderiv_le hf hL

end Carleman
