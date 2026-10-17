module

public import Carleman.Continuous.WeakTimeFTC

/-! A proved H¹-to-C bound, with its explicit period dependence. This is
the trace convergence estimate; it is not a T-uniform graph estimate. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
namespace TimeGrid
variable (g : TimeGrid)

theorem timeMeasure_real_univ : g.timeMeasure.real univ = g.period := by
  simp [timeMeasure, Measure.real, g.period_pos.le]

def timeUnit : Lp ℝ 2 g.timeMeasure := (memLp_const (1 : ℝ)).toLp (fun _ => 1)

theorem timeUnit_ae : g.timeUnit =ᵐ[g.timeMeasure] (fun _ => 1) :=
  (memLp_const (1 : ℝ)).coeFn_toLp

theorem timeUnit_norm : ‖g.timeUnit‖ = Real.sqrt g.period := by
  have hs : ‖g.timeUnit‖^2 = g.period := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    calc
      _ = ∫ _ : ℝ, (1 : ℝ) ∂g.timeMeasure := by
        apply integral_congr_ae
        filter_upwards [g.timeUnit_ae] with t ht
        simp [ht]
      _ = g.period := by simp [integral_const, g.timeMeasure_real_univ]
  exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt hs)

variable {H : Type*} [NormedAddCommGroup H]

/-- Cauchy–Schwarz for the actual Bochner L² norm on the period. -/
theorem integral_norm_le_l2 {f : ℝ → H} (hf : MemLp f 2 g.timeMeasure) :
    (∫ t, ‖f t‖ ∂g.timeMeasure) ≤ Real.sqrt g.period * ‖hf.toLp f‖ := by
  let v : Lp ℝ 2 g.timeMeasure := hf.norm.toLp (fun t => ‖f t‖)
  have hi : inner ℝ g.timeUnit v = ∫ t, ‖f t‖ ∂g.timeMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [g.timeUnit_ae, hf.norm.coeFn_toLp] with t ht hv
    change v t = ‖f t‖ at hv
    rw [ht, hv]
    simp
  have hn : ‖v‖ = ‖hf.toLp f‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm _ hf.aestronglyMeasurable]
  rw [← hi, ← g.timeUnit_norm, ← hn]
  exact real_inner_le_norm _ _
end TimeGrid

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem HasWeakTimeDerivative.norm_sub_le_integral_norm {g : TimeGrid} {u du : ℝ → H}
    (hw : HasWeakTimeDerivative g u du) (hu : ContinuousOn u (Icc 0 g.period))
    (hd : MemLp du 2 g.timeMeasure) {a b : ℝ}
    (ha : a ∈ Icc 0 g.period) (hb : b ∈ Icc 0 g.period) :
    ‖u b - u a‖ ≤ ∫ t, ‖du t‖ ∂g.timeMeasure := by
  rw [← hw.integral_eq_sub hu hd ha hb]
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  have hi : IntegrableOn (fun t => ‖du t‖) (Icc 0 g.period) volume := by
    change Integrable (fun t => ‖du t‖) (volume.restrict (Icc 0 g.period))
    simpa only [TimeGrid.timeMeasure, restrict_Ioo_eq_restrict_Icc] using
      (MemLp.integrable (by norm_num) hd).norm
  change _ ≤ ∫ t in Ioo 0 g.period, ‖du t‖
  rw [restrict_Ioo_eq_restrict_Icc]
  apply setIntegral_mono_set hi (Filter.Eventually.of_forall fun t => norm_nonneg _)
  exact Filter.Eventually.of_forall fun t ht =>
    (uIcc_subset_Icc ha hb) (uIoc_subset_uIcc ht)

/-- Full closed-period trace control by the actual value and weak derivative L² norms. -/
theorem HasWeakTimeDerivative.trace_bound {g : TimeGrid} {u du : ℝ → H}
    (hw : HasWeakTimeDerivative g u du) (hu : ContinuousOn u (Icc 0 g.period))
    (hd : MemLp du 2 g.timeMeasure) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    ‖u t‖ ≤ (Real.sqrt g.period / g.period) * ‖(g.memLp_of_continuousOn hu).toLp u‖ +
      Real.sqrt g.period * ‖hd.toLp du‖ := by
  have hui := MemLp.integrable (by norm_num) (g.memLp_of_continuousOn hu)
  have hpoint : ∀ᵐ a ∂g.timeMeasure,
      ‖u t‖ ≤ ‖u a‖ + ∫ x, ‖du x‖ ∂g.timeMeasure := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    calc
      ‖u t‖ ≤ ‖u a‖ + ‖u t - u a‖ := by
        simpa only [add_sub_cancel] using norm_add_le (u a) (u t - u a)
      _ ≤ _ := add_le_add le_rfl (hw.norm_sub_le_integral_norm hu hd ⟨ha.1.le, ha.2.le⟩ ht)
  have hint := integral_mono_ae (integrable_const ‖u t‖) (hui.norm.fun_add (integrable_const _)) hpoint
  rw [integral_const, integral_add hui.norm (integrable_const _), integral_const,
    g.timeMeasure_real_univ, smul_eq_mul, smul_eq_mul] at hint
  have hb1 := g.integral_norm_le_l2 (g.memLp_of_continuousOn hu)
  have hb2 := g.integral_norm_le_l2 hd
  have hmul := mul_le_mul_of_nonneg_left hb2 g.period_pos.le
  apply (mul_le_mul_iff_right₀ g.period_pos).mp
  have hT := g.period_pos.ne'
  convert hint.trans (add_le_add hb1 hmul) using 1
  field_simp [hT]

end Carleman
