module

public import Carleman.Weights.TemporalMollification
public import Carleman.Spatial.PeriodicHeatFlux
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation of the actual temporal convolution, with a proved integrable majorant. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Convolution ContDiff Topology
namespace Carleman

theorem temporalMollification_hasDerivAt {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    {D : ℝ} (hD : ∀ t, |deriv q t| ≤ D) (n : ℕ) (t : ℝ) :
    HasDerivAt (temporalMollification q n) (temporalMollification (deriv q) n t) t := by
  let κ := (temporalBump n).normed (volume : Measure ℝ)
  have hk : Continuous κ := (temporalBump n).continuous_normed
  have hqc := hq.continuous
  have hq' := hq.continuous_deriv_one
  have hFi : Integrable (fun s => κ s*q (t-s)) volume :=
    (temporalBump n).hasCompactSupport_normed.convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) hk hqc.locallyIntegrable t
  have hFm : ∀ᶠ x in 𝓝 t, AEStronglyMeasurable (fun s => κ s*q (x-s)) volume := by
    filter_upwards with x
    exact (hk.mul (hqc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable (fun s => κ s*deriv q (t-s)) volume :=
    (hk.mul (hq'.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hbound : ∀ᵐ s ∂(volume : Measure ℝ), ∀ x ∈ (univ : Set ℝ),
      ‖κ s*deriv q (x-s)‖ ≤ κ s*D := by
    filter_upwards with s
    intro x _
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ((temporalBump n).nonneg_normed s),Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hD (x-s)) ((temporalBump n).nonneg_normed s)
  have hdiff : ∀ᵐ s ∂(volume : Measure ℝ), ∀ x ∈ (univ : Set ℝ),
      HasDerivAt (fun y => κ s*q (y-s)) (κ s*deriv q (x-s)) x := by
    filter_upwards with s
    intro x _
    convert! (((hq.differentiable one_ne_zero (x-s)).hasDerivAt).comp x
      ((hasDerivAt_id x).sub_const s)).const_mul (κ s) using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ) (by simp)
    hFm hFi hF'm hbound ((temporalBump n).integrable_normed.mul_const D) hdiff).2

theorem temporalMollification_deriv_periodic {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    {T : ℝ} (hT : 0 < T) (hp : Function.Periodic q T) (n : ℕ) :
    deriv (temporalMollification q n)=temporalMollification (deriv q) n := by
  have hp' : Function.Periodic (deriv q) T := smoothD_periodic hp 1
  obtain ⟨D,_hD,hbound⟩ := continuous_periodic_bounded hq.continuous_deriv_one hT hp'
  exact funext fun t => (temporalMollification_hasDerivAt hq hbound n t).deriv

theorem temporalMollification_second_deriv_periodic {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q)
    {T : ℝ} (hT : 0 < T) (hp : Function.Periodic q T) (n : ℕ) :
    deriv (deriv (temporalMollification q n))=temporalMollification (deriv (deriv q)) n := by
  have hq1 : ContDiff ℝ 1 q := hq.of_le (by norm_num)
  have hdq : ContDiff ℝ 1 (deriv q) := (hq.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  rw [temporalMollification_deriv_periodic hq1 hT hp,
    temporalMollification_deriv_periodic hdq hT (show Function.Periodic (deriv q) T from smoothD_periodic hp 1)]

end Carleman
