module

public import Carleman.Spatial.SimplexBarycentricDistribution

/-! Real layer-cake identity for bounded second moments. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem integral_sq_eq_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) (hn : 0 ≤ᵐ[μ] f)
    (hb : f ≤ᵐ[μ] (fun _ => 1)) :
    (∫ x, (f x)^2 ∂μ) = 2 * ∫ t in Ioc (0:ℝ) 1, t * μ.real {x | t ≤ f x} := by
  have hg : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using ht.le
  have h := lintegral_comp_eq_lintegral_meas_le_mul μ hn hf
    (g := fun t : ℝ => t) (fun t _ => continuous_id.intervalIntegrable 0 t) hg
  simp only [integral_id,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero] at h
  have hm : Measurable (fun t : ℝ => μ {x | t ≤ f x}) :=
    Antitone.measurable (fun _ _ hst => measure_mono (fun _ hx => hst.trans hx))
  have hr : (∫ t in Ioi (0:ℝ), t * μ.real {x | t ≤ f x}) =
      (∫⁻ t in Ioi (0:ℝ), μ {x | t ≤ f x} * ENNReal.ofReal t).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      apply lintegral_congr_ae
      filter_upwards [hg] with t ht
      rw [ENNReal.ofReal_mul ht,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ _),mul_comm]
    · filter_upwards [hg] with t ht using mul_nonneg ht (measureReal_nonneg)
    · exact (measurable_id.mul hm.ennreal_toReal).aestronglyMeasurable
  have hl : (∫ x, (f x)^2/2 ∂μ) =
      (∫⁻ x, ENNReal.ofReal ((f x)^2/2) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => by positivity))
      ((hf.pow_const 2).div_const 2).aestronglyMeasurable
  have he : (∫ x, (f x)^2 ∂μ)/2 = ∫ t in Ioi (0:ℝ), t * μ.real {x | t ≤ f x} := by
    rw [← integral_div,hl,h,hr]
  have ht : (∫ t in Ioi (0:ℝ), t * μ.real {x | t ≤ f x}) =
      ∫ t in Ioc (0:ℝ) 1, t * μ.real {x | t ≤ f x} := by
    apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_Ioi Ioc_subset_Ioi_self
    apply Filter.Eventually.of_forall
    intro t ht
    have ht1 : 1 < t := by simp_all only [Set.mem_sdiff,mem_Ioi,mem_Ioc,not_and,not_le]
    have hz : μ {x | 1 < f x} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hb] with x hx using not_lt.mpr hx
    have hz' : μ {x | t ≤ f x} = 0 :=
      measure_mono_null (fun x hx => ht1.trans_le hx) hz
    simp [measureReal_def,hz']
  rw [ht] at he
  linarith

end Carleman
