module

public import Carleman.Weights.SquaredCellDerivatives
public import Carleman.Spatial.NodalResidualLp
public import Carleman.Spatial.AllowedReciprocalWeight

/-! Exact identities between actual squared-weight integrals and the original
allowed multiplier seminorms, including the reciprocal weight. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem allowed_weight_sq_integral (ρ : SpatialProfile (volume.restrict S))
    (w : TimeWeight) (τ t η : ℝ) (u : Lp E 2 (volume.restrict S)) :
    (((ρ.scaled η).multiplier w τ t).seminorm u)^2 =
      ∫ x in S, allowedSquaredWeight ρ.value (w.q t) τ η x*‖u x‖^2 := by
  rw [BoundedMultiplier.seminorm_sq_integral]
  apply integral_congr_ae
  filter_upwards with x
  rw [allowedSquaredWeight_multiplier_value]
  simp only [sq_abs]

theorem allowed_inverse_weight_sq_integral (ρ : SpatialProfile (volume.restrict S))
    (w : TimeWeight) (τ t η : ℝ) (u : Lp E 2 (volume.restrict S)) :
    (((ρ.scaled (-η)).multiplier w (-τ) t).seminorm u)^2 =
      ∫ x in S, ‖u x‖^2/allowedSquaredWeight ρ.value (w.q t) τ η x := by
  rw [BoundedMultiplier.seminorm_sq_integral]
  apply integral_congr_ae
  filter_upwards with x
  rw [ρ.scaled_multiplier_inverse_value,allowedSquaredWeight_multiplier_value]
  simp only [abs_inv,inv_pow,sq_abs,div_eq_mul_inv,mul_comm]

end Carleman
