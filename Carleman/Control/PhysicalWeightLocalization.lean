module

public import Carleman.Control.PhysicalWeightSecond
public import Carleman.Control.PhysicalRamp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Localization of the original sine weight near the endpoints and on
the middle third of the physical time interval. -/
@[expose] public noncomputable section
namespace Carleman.Physical

theorem sine_reflect (T t : ℝ) (hT : T ≠ 0) :
    Real.sin (Real.pi*(T-t)/T) = Real.sin (Real.pi*t/T) := by
  have he : Real.pi*(T-t)/T = Real.pi-Real.pi*t/T := by field_simp
  rw [he,Real.sin_pi_sub]

theorem sine_endpoint_bound (T t : ℝ) (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
    |Real.sin (Real.pi*t/T)| ≤ (Real.pi/T)*endpointDistance T t := by
  have hl : |Real.sin (Real.pi*t/T)| ≤ (Real.pi/T)*t := by
    calc
      _ ≤ |Real.pi*t/T| := Real.abs_sin_le_abs
      _ = (Real.pi/T)*t := by rw [abs_of_nonneg (by positivity)]; ring
  have hr : |Real.sin (Real.pi*t/T)| ≤ (Real.pi/T)*(T-t) := by
    rw [← sine_reflect T t (ne_of_gt hT)]
    calc
      _ ≤ |Real.pi*(T-t)/T| := Real.abs_sin_le_abs
      _ = (Real.pi/T)*(T-t) := by rw [abs_of_nonneg (by positivity)]; ring
  by_cases hc : t ≤ T-t
  · simpa only [endpointDistance,min_eq_left hc] using hl
  · simpa only [endpointDistance,min_eq_right (le_of_not_ge hc)] using hr

theorem physicalWeight_near_endpoint (qb δ T t : ℝ)
    (hqb : 0 ≤ qb) (hδ : 0 < δ) (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T)
    (hnear : endpointDistance T t ≤ 3*δ*T) :
    (qb/δ)/Real.sqrt (1+9*Real.pi^2) ≤ physicalWeight qb δ T t := by
  have hs : |Real.sin (Real.pi*t/T)| ≤ 3*Real.pi*δ := by
    have hh := (sine_endpoint_bound T t hT ht htT).trans
      (mul_le_mul_of_nonneg_left hnear (div_pos Real.pi_pos hT).le)
    have he : (Real.pi/T)*(3*δ*T) = 3*Real.pi*δ := by field_simp
    simpa only [he] using hh
  have hC : 0 < Real.sqrt (1+9*Real.pi^2) := Real.sqrt_pos.mpr (by positivity)
  have hD := physicalWeightDenom_pos δ T t hδ
  have hden : physicalWeightDenom δ T t ≤ δ*Real.sqrt (1+9*Real.pi^2) := by
    apply (sq_le_sq₀ hD.le (mul_pos hδ hC).le).mp
    rw [physicalWeightDenom_sq,mul_pow,Real.sq_sqrt (by positivity)]
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 3*Real.pi*δ)).mpr hs
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hh := div_le_div_of_nonneg_left hqb hD hden
  change qb/(δ*Real.sqrt (1+9*Real.pi^2)) ≤ physicalWeight qb δ T t at hh
  simpa only [div_div] using hh

theorem sine_middle_lower (T t : ℝ) (hT : 0 < T)
    (ht : T/3 ≤ t) (htT : t ≤ 2*T/3) : 1/2 ≤ Real.sin (Real.pi*t/T) := by
  have hhalf (s : ℝ) (hs : T/3 ≤ s) (hsT : s ≤ T/2) : 1/2 ≤ Real.sin (Real.pi*s/T) := by
    have hangle : Real.pi*s/T ≤ Real.pi/2 := by
      apply (div_le_iff₀ hT).mpr
      nlinarith [Real.pi_pos]
    have hsmall : Real.pi/6 ≤ Real.pi*s/T := by
      apply (le_div_iff₀ hT).mpr
      nlinarith [Real.pi_pos]
    simpa only [Real.sin_pi_div_six] using
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hangle hsmall
  by_cases hh : t ≤ T/2
  · exact hhalf t ht hh
  · have hs := hhalf (T-t) (by linarith only [htT]) (by linarith only [hh])
    simpa only [sine_reflect T t (ne_of_gt hT)] using hs

theorem physicalWeight_middle_upper (qb δ T t : ℝ) (hqb : 0 ≤ qb) (hδ : 0 < δ)
    (hT : 0 < T) (ht : T/3 ≤ t) (htT : t ≤ 2*T/3) : physicalWeight qb δ T t ≤ 2*qb := by
  have hs := sine_middle_lower T t hT ht htT
  have hD := physicalWeightDenom_pos δ T t hδ
  have hden : (1:ℝ)/2 ≤ physicalWeightDenom δ T t := by
    apply (sq_le_sq₀ (by norm_num) hD.le).mp
    rw [physicalWeightDenom_sq]
    nlinarith [sq_nonneg δ]
  have hh := div_le_div_of_nonneg_left hqb (by norm_num : (0:ℝ) < 1/2) hden
  change physicalWeight qb δ T t ≤ qb/(1/2) at hh
  convert hh using 1
  ring

end Carleman.Physical
