module

public import Carleman.Continuous.WeakTimeEnergy

/-! Actual scalar weak FTC and affine Green identity recover both endpoint traces. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
theorem HasWeakTimeDerivative.scalar_affine_green {g : TimeGrid} {f df : ℝ → ℝ}
    (hw : HasWeakTimeDerivative g f df) (hc : ContinuousOn f (Icc 0 g.period))
    (hd : MemLp df 2 g.timeMeasure) (c : ℝ) :
    (∫ t, (f t+(t-c)*df t) ∂g.timeMeasure)=
      (g.period-c)*f g.period+c*f 0 := by
  have hAC := hw.absolutelyContinuous hc hd
  have hα : AbsolutelyContinuousOnInterval (fun t : ℝ => t-c) 0 g.period :=
    (contDiff_id.sub contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  have he := hα.integral_deriv_mul_eq_sub hAC
  rw [← g.timeIntegral_eq_intervalIntegral] at he
  have hder : (fun t => deriv (fun s : ℝ => s-c) t*f t+(t-c)*deriv f t) =ᵐ[g.timeMeasure]
      (fun t => f t+(t-c)*df t) := by
    filter_upwards [hw.ae_hasDerivAt hc hd] with t ht
    have ha : deriv (fun s : ℝ => s-c) t=1 := by
      simpa only [id_eq] using ((hasDerivAt_id t).sub_const c).deriv
    rw [ha,ht.deriv,one_mul]
  rw [integral_congr_ae hder] at he
  simpa only [zero_sub,neg_mul,sub_neg_eq_add] using he

theorem HasWeakTimeDerivative.scalar_endpoints {g : TimeGrid} {f df : ℝ → ℝ}
    (hw : HasWeakTimeDerivative g f df) (hc : ContinuousOn f (Icc 0 g.period))
    (hd : MemLp df 2 g.timeMeasure) (a : ℝ)
    (hzero : a+(∫ t, df t ∂g.timeMeasure)=0)
    (hlin : (∫ t, f t ∂g.timeMeasure)+(∫ t, t*df t ∂g.timeMeasure)=0) :
    f 0=a ∧ f g.period=0 := by
  have hgreen := hw.scalar_affine_green hc hd 0
  have hi : Integrable f g.timeMeasure := (g.memLp_of_continuousOn hc).integrable (by norm_num)
  have hit : Integrable (fun t => t*df t) g.timeMeasure :=
    memLp_one_iff_integrable.mp ((g.memLp_of_continuousOn continuousOn_id).mul hd)
  simp only [sub_zero,zero_mul,add_zero] at hgreen
  rw [integral_add hi hit,hlin] at hgreen
  have hT : f g.period=0 := (mul_eq_zero.mp hgreen.symm).resolve_left g.period_pos.ne'
  have hftc := hw.integral_eq_sub hc hd (show 0 ∈ Icc 0 g.period from ⟨le_rfl,g.period_pos.le⟩)
    (show g.period ∈ Icc 0 g.period from ⟨g.period_pos.le,le_rfl⟩)
  rw [← g.timeIntegral_eq_intervalIntegral,hT] at hftc
  exact ⟨by linarith,hT⟩

end Carleman
