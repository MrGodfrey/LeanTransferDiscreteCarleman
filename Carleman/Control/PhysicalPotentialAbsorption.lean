module

public import Carleman.Control.PhysicalQClass

/-! A uniform original-amplitude budget for absorbing the bounded potential. -/
@[expose] public noncomputable section
namespace Carleman.Physical

theorem physicalWeight_lower_half (qb δ T t : ℝ) (hqb : 0 ≤ qb)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1/16) : qb/2 ≤ physicalWeight qb δ T t := by
  have hd : 0 < Real.sqrt (1+δ^2) := Real.sqrt_pos.mpr (by positivity)
  have hdu : Real.sqrt (1+δ^2) ≤ 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 2)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith only [hδ,hδsmall]
  exact (div_le_div_of_nonneg_left hqb hd hdu).trans
    (physicalWeight_bounds qb δ T t hqb hδ).1

theorem physical_potential_budget (Cb qc T M δ CCE t : ℝ)
    (hCb : 1 ≤ Cb) (hbudget : 32*CCE ≤ Cb) (hqc : 1 ≤ qc)
    (hT : 0 < T) (hM : 0 ≤ M) (hδ : 0 < δ) (hδsmall : δ ≤ 1/16) :
    2*CCE*M^2 ≤ physicalWeight (physicalBaseAmplitude Cb qc T M) δ T t^3/2 := by
  have hC : 0 ≤ Cb := by linarith only [hCb]
  obtain ⟨hq,_,hpot⟩ := physicalBaseAmplitude_bounds Cb qc T M hC (by linarith only [hqc]) hT hM
  have hqnonneg : 0 ≤ physicalBaseAmplitude Cb qc T M :=
    (mul_nonneg hC (by linarith only [hqc])).trans hq
  have hc2 : 1 ≤ Cb^2 := one_le_pow₀ hCb
  have hc3 : 32*CCE ≤ Cb^3 := by
    have hh := mul_le_mul_of_nonneg_left hc2 hC
    nlinarith only [hh,hbudget]
  have hp := (mul_le_mul_of_nonneg_right hc3 (sq_nonneg M)).trans hpot
  have hl := physicalWeight_lower_half (physicalBaseAmplitude Cb qc T M) δ T t hqnonneg hδ hδsmall
  have hpow := pow_le_pow_left₀ (div_nonneg hqnonneg (by norm_num : (0:ℝ) ≤ 2)) hl 3
  nlinarith only [hp,hpow]

end Carleman.Physical
