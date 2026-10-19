module

public import Carleman.Spatial.WeightedL2
public import Mathlib.MeasureTheory.Integral.Prod

/-! Actual averages of a.e. bounded potentials, with the original bound and representative independence. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set
namespace Carleman.BoundedMultiplier
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {μ : Measure Ω} {ν : Measure Ξ}

def ofMeasureLE (b : BoundedMultiplier μ) {μ' : Measure Ω} (h : μ' ≤ μ) :
    BoundedMultiplier μ' where
  value := b.value
  measurable := b.measurable.mono_measure h
  bound := b.bound
  bound_nonneg := b.bound_nonneg
  bounded := ae_mono h b.bounded

theorem ofMeasureLE_bound (b : BoundedMultiplier μ) {μ' : Measure Ω} (h : μ' ≤ μ) :
    (b.ofMeasureLE h).bound = b.bound := rfl

theorem integrable [IsFiniteMeasure μ] (b : BoundedMultiplier μ) : Integrable b.value μ := by
  apply (integrable_const b.bound).mono' b.measurable
  simpa only [Real.norm_eq_abs] using b.bounded

def averageFirst [IsFiniteMeasure μ] [SFinite ν] (b : BoundedMultiplier (μ.prod ν))
    (mass : ℝ) (hm : 0 < mass) (hvol : μ.real univ = mass) : BoundedMultiplier ν where
  value x := mass⁻¹ * ∫ t, b.value (t,x) ∂μ
  measurable := b.measurable.prod_swap.integral_prod_right'.const_mul _
  bound := b.bound
  bound_nonneg := b.bound_nonneg
  bounded := by
    have hb := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae b.bounded)
    filter_upwards [hb] with x hx
    have hi := norm_integral_le_of_norm_le_const (f := fun t => b.value (t,x))
      (by simpa only [Real.norm_eq_abs,Prod.swap] using hx)
    rw [hvol,Real.norm_eq_abs] at hi
    rw [abs_mul,abs_of_pos (inv_pos.mpr hm)]
    calc
      mass⁻¹ * |∫ t, b.value (t,x) ∂μ| ≤ mass⁻¹ * (b.bound*mass) :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hm.le)
      _ = b.bound := by field_simp

theorem averageFirst_bound [IsFiniteMeasure μ] [SFinite ν] (b : BoundedMultiplier (μ.prod ν))
    (mass : ℝ) (hm : 0 < mass) (hvol : μ.real univ = mass) :
    (b.averageFirst mass hm hvol).bound = b.bound := rfl

theorem averageFirst_congr [IsFiniteMeasure μ] [SFinite ν]
    (b c : BoundedMultiplier (μ.prod ν)) (mass : ℝ) (hm : 0 < mass)
    (hvol : μ.real univ = mass) (h : b.value =ᵐ[μ.prod ν] c.value) :
    (b.averageFirst mass hm hvol).value =ᵐ[ν] (c.averageFirst mass hm hvol).value := by
  have hh := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae h)
  filter_upwards [hh] with x hx
  exact congrArg (mass⁻¹ * ·) (integral_congr_ae hx)

theorem setAverage_bound [IsFiniteMeasure μ] (b : BoundedMultiplier μ)
    (K : Set Ω) {mass : ℝ} (hm : 0 < mass) (hvol : μ.real K = mass) :
    |mass⁻¹ * ∫ x in K, b.value x ∂μ| ≤ b.bound := by
  have hi := norm_setIntegral_le_of_norm_le_const_ae (f := b.value) (measure_lt_top μ K)
    (by simpa only [Real.norm_eq_abs] using (ae_restrict_of_ae b.bounded :
      ∀ᵐ x ∂μ.restrict K, |b.value x| ≤ b.bound))
  rw [Real.norm_eq_abs,hvol] at hi
  rw [abs_mul,abs_of_pos (inv_pos.mpr hm)]
  calc
    mass⁻¹ * |∫ x in K, b.value x ∂μ| ≤ mass⁻¹ * (b.bound*mass) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hm.le)
    _ = b.bound := by field_simp

theorem averageFirst_setIntegral [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b : BoundedMultiplier (μ.prod ν)) (mass : ℝ) (hm : 0 < mass)
    (hvol : μ.real univ = mass) (K : Set Ξ) :
    (∫ x in K, (b.averageFirst mass hm hvol).value x ∂ν) =
      mass⁻¹ * ∫ t, ∫ x in K, b.value (t,x) ∂ν ∂μ := by
  change (∫ x in K, mass⁻¹ * ∫ t, b.value (t,x) ∂μ ∂ν) = _
  rw [integral_const_mul]
  congr 1
  exact (integral_integral_swap (f := fun t x => b.value (t,x))
    (b.integrable.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self))).symm

end Carleman.BoundedMultiplier
