module

public import Carleman.Continuous.TimeInterval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Classical H-valued trajectories supply the genuine distributional
identity. This is used for approximants only, not imposed on B1 solutions. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

namespace TimeGrid
variable (g : TimeGrid)

theorem timeIntegral_eq_intervalIntegral [CompleteSpace H] (f : ℝ → H) :
    (∫ t, f t ∂g.timeMeasure) = ∫ t in 0..g.period, f t := by
  rw [intervalIntegral.integral_of_le g.period_pos.le, integral_Ioc_eq_integral_Ioo]
  rfl

theorem memLp_of_continuousOn {f : ℝ → H} (hf : ContinuousOn f (Icc 0 g.period)) :
    MemLp f 2 g.timeMeasure := by
  let p : g.TracePath (H := H) := ⟨(Icc 0 g.period).domRestrict f,
    continuousOn_iff_continuous_domRestrict.mp hf⟩
  apply (g.pathL2_memLp p).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact g.clampPath_on p t ⟨ht.1.le, ht.2.le⟩
end TimeGrid
end Carleman

namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Interior classical differentiability implies the original Bochner weak
identity. Endpoints require only H continuity; derivative integrability is explicit. -/
theorem HasWeakTimeDerivative.of_hasDerivAt {g : TimeGrid} {u du : ℝ → H}
    (hu : ContinuousOn u (Icc 0 g.period))
    (hd : ∀ t ∈ Ioo 0 g.period, HasDerivAt u (du t) t)
    (hi : IntervalIntegrable du volume 0 g.period) : HasWeakTimeDerivative g u du := by
  intro φ hs _ hsup
  have hzero : φ 0 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl 0) (hsup h).1)
  have hperiod : φ g.period = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl g.period) (hsup h).2)
  have he := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    hs.continuous.continuousOn
    (show ContinuousOn u (uIcc 0 g.period) by simpa only [uIcc_of_le g.period_pos.le] using hu)
    (fun t _ => (hs.differentiable (by simp) t).hasDerivAt)
    (fun t ht => hd t (by
      simpa only [min_eq_left g.period_pos.le, max_eq_right g.period_pos.le] using ht))
    (hs.continuous_deriv (by simp)).continuousOn.intervalIntegrable hi
  rw [hzero, hperiod, zero_smul, zero_smul, sub_self, zero_sub] at he
  rw [g.timeIntegral_eq_intervalIntegral, g.timeIntegral_eq_intervalIntegral]
  have hn := congrArg Neg.neg he
  simpa only [neg_neg] using hn.symm
end Carleman
