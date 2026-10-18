module

public import Carleman.Control.PhysicalSpatialWeights

/-! Uniform polynomial/exponential budgets for the physical observation proof. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.Physical

theorem cubic_exponential_bound (r q : ℝ) (hr : 0 < r) (hq : 0 ≤ q) :
    q^3*Real.exp (-2*r*q) ≤ 6/r^3 := by
  have he := Real.pow_div_factorial_le_exp (r*q) (mul_nonneg hr.le hq) 3
  norm_num only [Nat.factorial,Nat.cast_ofNat,Nat.reduceMul,mul_pow] at he
  have hp : r^3*q^3 ≤ 6*Real.exp (r*q) := by linarith only [he]
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-2*r*q)).le
  have hid : Real.exp (r*q)*Real.exp (-2*r*q) = Real.exp (-r*q) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hu : Real.exp (-r*q) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hr,hq])
  rw [mul_assoc 6,hid] at hm
  apply (le_div_iff₀ (pow_pos hr 3)).mpr
  nlinarith only [hm,hu]

theorem linear_exponential_decay (c S : ℝ) (hc : 0 < c) (hS : 0 ≤ S) :
    S*Real.exp (-c*S) ≤ (2/c)*Real.exp (-(c/2)*S) := by
  have he := Real.pow_div_factorial_le_exp (c*S/2) (show 0 ≤ c*S/2 by positivity) 1
  norm_num only [pow_one,Nat.factorial,Nat.cast_one,div_one] at he
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-c*S)).le
  have hid : Real.exp (c*S/2)*Real.exp (-c*S) = Real.exp (-(c/2)*S) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid] at hm
  have hm2 := mul_le_mul_of_nonneg_left hm (div_pos (by norm_num : (0:ℝ) < 2) hc).le
  convert hm2 using 1
  field_simp

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν) (w : TimeWeight)

theorem spatial_observation_weight_bound (rstar t : ℝ) (hrstar : 0 < rstar)
    (hneg : ∀ᵐ x ∂ν, ρ.value x ≤ -rstar) (u : Lp E 2 ν) :
    w.q t^3*((ρ.multiplier w 0 t).seminorm u)^2 ≤ (6/rstar^3)*‖u‖^2 := by
  have hh := mul_le_mul_of_nonneg_left (spatial_weight_upper_sq ρ w rstar t hneg u)
    (pow_nonneg (w.nonneg t) 3)
  have he := mul_le_mul_of_nonneg_right (cubic_exponential_bound rstar (w.q t) hrstar (w.nonneg t))
    (sq_nonneg ‖u‖)
  exact hh.trans (by simpa only [mul_assoc] using he)

end Carleman.Physical
