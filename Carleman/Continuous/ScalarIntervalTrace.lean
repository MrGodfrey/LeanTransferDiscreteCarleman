module

public import Carleman.Continuous.WeakIntervalTrace
public import Carleman.Continuous.WeakTimeEnergy

/-! Explicit endpoint trace formulas for arbitrary scalar weak H¹ classes.
These integral formulas will define measurable face traces on product domains. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.TimeGrid
variable (g : TimeGrid)

theorem weakIntervalTrace_affine_green (z : weakTimeSubmodule (H := ℝ) g) (c : ℝ) :
    (∫ t, (z.val.1 t+(t-c)*z.val.2 t) ∂g.timeMeasure)=
      (g.period-c)*g.weakIntervalTrace ⟨g.period,g.period_pos.le,le_rfl⟩ z+
        c*g.weakIntervalTrace ⟨0,le_rfl,g.period_pos.le⟩ z := by
  let U : ℝ → ℝ := g.clampPath (g.weakTracePath z)
  have hc : ContinuousOn U (Icc 0 g.period) :=
    (g.clampPath (g.weakTracePath z)).continuous.continuousOn
  have hw : HasWeakTimeDerivative g U z.val.2 := g.weakTracePath_weak z
  have hAC := hw.absolutelyContinuous hc (Lp.memLp z.val.2)
  have hα : AbsolutelyContinuousOnInterval (fun t : ℝ => t-c) 0 g.period :=
    (contDiff_id.sub contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  have he := hα.integral_deriv_mul_eq_sub hAC
  rw [← g.timeIntegral_eq_intervalIntegral] at he
  have hder : (fun t => deriv (fun s : ℝ => s-c) t*U t+(t-c)*deriv U t) =ᵐ[g.timeMeasure]
      (fun t => z.val.1 t+(t-c)*z.val.2 t) := by
    filter_upwards [hw.ae_hasDerivAt hc (Lp.memLp z.val.2),g.weakTracePath_ae z] with t ht hz
    have ha : deriv (fun s : ℝ => s-c) t=1 := by
      simpa only [id_eq] using ((hasDerivAt_id t).sub_const c).deriv
    rw [ha,ht.deriv,one_mul]
    exact congrArg (fun a => a+(t-c)*z.val.2 t) hz.symm
  rw [integral_congr_ae hder] at he
  dsimp only [U] at he
  rw [g.clampPath_on _ g.period ⟨g.period_pos.le,le_rfl⟩,
    g.clampPath_on _ 0 ⟨le_rfl,g.period_pos.le⟩] at he
  change (∫ t, (z.val.1 t+(t-c)*z.val.2 t) ∂g.timeMeasure)=
    (g.period-c)*g.weakTracePath z ⟨g.period,g.period_pos.le,le_rfl⟩+
      c*g.weakTracePath z ⟨0,le_rfl,g.period_pos.le⟩
  simpa only [zero_sub,neg_mul,sub_neg_eq_add] using he

theorem weakIntervalTrace_zero_formula (z : weakTimeSubmodule (H := ℝ) g) :
    g.weakIntervalTrace ⟨0,le_rfl,g.period_pos.le⟩ z=
      (∫ t, (z.val.1 t+(t-g.period)*z.val.2 t) ∂g.timeMeasure)/g.period := by
  have he := g.weakIntervalTrace_affine_green z g.period
  simp only [sub_self,zero_mul,zero_add] at he
  rw [he,mul_div_cancel_left₀ _ g.period_pos.ne']

theorem weakIntervalTrace_end_formula (z : weakTimeSubmodule (H := ℝ) g) :
    g.weakIntervalTrace ⟨g.period,g.period_pos.le,le_rfl⟩ z=
      (∫ t, (z.val.1 t+t*z.val.2 t) ∂g.timeMeasure)/g.period := by
  have he := g.weakIntervalTrace_affine_green z 0
  simp only [sub_zero,zero_mul,add_zero] at he
  rw [he,mul_div_cancel_left₀ _ g.period_pos.ne']

end Carleman.TimeGrid
