module

public import Carleman.Continuous.WeakTimeConstant
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! The Bochner primitive of an L² derivative satisfies the actual weak
identity. Scalar absolute continuity is used only inside the proof. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
theorem TimeGrid.intervalIntegrable_of_memLp {g : TimeGrid} {f : ℝ → H}
    (hf : MemLp f 2 g.timeMeasure) : IntervalIntegrable f volume 0 g.period :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le g.period_pos.le).mpr
    (MemLp.integrable (by norm_num) hf)

omit [CompleteSpace H] in
theorem TimeGrid.primitive_continuousOn {g : TimeGrid} {f : ℝ → H}
    (hf : MemLp f 2 g.timeMeasure) :
    ContinuousOn (fun t => ∫ x in 0..t, f x) (Icc 0 g.period) := by
  simpa only [uIcc_of_le g.period_pos.le] using
    intervalIntegral.continuousOn_primitive_interval' (TimeGrid.intervalIntegrable_of_memLp hf)
      left_mem_uIcc

theorem HasWeakTimeDerivative.scalar_primitive {g : TimeGrid} {f : ℝ → ℝ}
    (hf : MemLp f 2 g.timeMeasure) :
    HasWeakTimeDerivative g (fun t => ∫ x in 0..t, f x) f := by
  let F : ℝ → ℝ := fun t => ∫ x in 0..t, f x
  have hi := TimeGrid.intervalIntegrable_of_memLp hf
  have hAC := hi.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  intro φ hφ _ hsφ
  have hφAC : AbsolutelyContinuousOnInterval φ 0 g.period :=
    (hφ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have he := hφAC.integral_mul_deriv_eq_deriv_mul hAC
  have hzero : φ 0 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl 0) (hsφ h).1)
  have hperiod : φ g.period = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl g.period) (hsφ h).2)
  have hder : (∫ t in 0..g.period, φ t * deriv F t) = ∫ t in 0..g.period, φ t * f t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    rw [(ht (uIoc_subset_uIcc hmem) 0 left_mem_uIcc).deriv]
  change (∫ t in 0..g.period, φ t * deriv F t) =
    φ g.period * F g.period - φ 0 * F 0 - ∫ t in 0..g.period, deriv φ t * F t at he
  rw [hder, hzero, hperiod, zero_mul, zero_mul, sub_self, zero_sub] at he
  rw [g.timeIntegral_eq_intervalIntegral, g.timeIntegral_eq_intervalIntegral]
  simp only [smul_eq_mul]
  exact (neg_eq_iff_eq_neg.mpr he).symm

/-- The primitive is genuinely H-valued; no scalar surrogate replaces it. -/
theorem HasWeakTimeDerivative.primitive {g : TimeGrid} {f : ℝ → H}
    (hf : MemLp f 2 g.timeMeasure) :
    HasWeakTimeDerivative g (fun t => ∫ x in 0..t, f x) f := by
  let F : ℝ → H := fun t => ∫ x in 0..t, f x
  have hF := g.memLp_of_continuousOn (TimeGrid.primitive_continuousOn hf)
  intro φ hφ hcφ hsφ
  have hip : Integrable (fun t => φ t • f t) g.timeMeasure :=
    memLp_one_iff_integrable.mp ((g.memLp_of_continuousOn hφ.continuous.continuousOn).smul hf)
  have hid : Integrable (fun t => deriv φ t • F t) g.timeMeasure :=
    memLp_one_iff_integrable.mp
      ((g.memLp_of_continuousOn (hφ.continuous_deriv (by simp)).continuousOn).smul hF)
  apply ext_inner_left ℝ
  intro h
  let L : H →L[ℝ] ℝ := innerSL ℝ h
  have hLf : MemLp (fun t => L (f t)) 2 g.timeMeasure := hf.continuousLinearMap_comp L
  have hw := HasWeakTimeDerivative.scalar_primitive hLf φ hφ hcφ hsφ
  have hcomm : (fun t => ∫ x in 0..t, L (f x)) =ᵐ[g.timeMeasure] (fun t => L (F t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    apply L.intervalIntegral_comp_comm
    apply (TimeGrid.intervalIntegrable_of_memLp hf).mono_set
    rw [uIcc_of_le g.period_pos.le, uIcc_of_le ht.1.le]
    exact Icc_subset_Icc le_rfl ht.2.le
  have htest : (∫ t, deriv φ t * (∫ x in 0..t, L (f x)) ∂g.timeMeasure) =
      ∫ t, deriv φ t * L (F t) ∂g.timeMeasure := by
    apply integral_congr_ae
    filter_upwards [hcomm] with t ht
    rw [ht]
  simp only [smul_eq_mul] at hw
  rw [htest] at hw
  change L (∫ t, deriv φ t • F t ∂g.timeMeasure) = L (-(∫ t, φ t • f t ∂g.timeMeasure))
  rw [map_neg, ← L.integral_comp_comm hid, ← L.integral_comp_comm hip]
  simpa only [map_smul, smul_eq_mul] using hw

end Carleman
