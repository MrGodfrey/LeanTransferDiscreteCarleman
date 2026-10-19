module

public import Carleman.Spatial.WeightedL2

/-! Scalar weighted norm formulas for actual almost-everywhere representatives. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.BoundedMultiplier
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} (w : BoundedMultiplier μ)

theorem integrable_scalar_density_ae (u : Lp ℝ 2 μ) (f : X → ℝ) (hf : u =ᵐ[μ] f) :
    Integrable (fun x => |w.value x|^2*(f x)^2) μ := by
  apply (w.integrable_density u).congr
  filter_upwards [hf] with x hx
  simp only [hx,Real.norm_eq_abs,sq_abs]

theorem seminorm_sq_scalar_ae (u : Lp ℝ 2 μ) (f : X → ℝ) (hf : u =ᵐ[μ] f) :
    (w.seminorm u)^2=∫ x, |w.value x|^2*(f x)^2 ∂μ := by
  rw [w.seminorm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  simp only [hx,Real.norm_eq_abs,sq_abs]

end Carleman.BoundedMultiplier
