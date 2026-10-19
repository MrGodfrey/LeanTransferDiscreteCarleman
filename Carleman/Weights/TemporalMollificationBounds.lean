module

public import Carleman.Weights.TemporalMollificationDerivative
public import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative local bounds for the actual temporal convolution. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Convolution ContDiff Topology
namespace Carleman

theorem temporal_derivative_difference {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    {D : ℝ} (hD : ∀ t, |deriv q t| ≤ D) (s t : ℝ) :
    |q s-q t| ≤ D*|s-t| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le (s := (univ : Set ℝ))
      (fun x _ => hq.differentiable one_ne_zero x)
      (fun x _ => by simpa only [Real.norm_eq_abs] using hD x) convex_univ
      (mem_univ t) (mem_univ s)

theorem temporalMollification_uniform_error {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ t, |deriv q t| ≤ D) (n : ℕ) (t : ℝ) :
    |temporalMollification q n t-q t| ≤ D*(temporalBump n).rOut := by
  have hh := (temporalBump n).dist_normed_convolution_le (μ := volume)
    hq.continuous.aestronglyMeasurable (x₀ := t) (ε := D*(temporalBump n).rOut)
  apply hh
  intro s hs
  have hd := temporal_derivative_difference hq hD s t
  have hst : |s-t| ≤ (temporalBump n).rOut := by
    simpa only [Metric.mem_ball,Real.dist_eq] using hs.le
  simpa only [Real.dist_eq] using hd.trans (mul_le_mul_of_nonneg_left hst hD0)

theorem temporalMollification_local_norm_bound {f : ℝ → ℝ} (n : ℕ) (t B : ℝ)
    (hf : ∀ s ∈ Metric.ball (0:ℝ) (temporalBump n).rOut, |f (t-s)| ≤ B) :
    |temporalMollification f n t| ≤ B := by
  have hk := (temporalBump n).integrable_normed (μ := volume)
  have hh : ‖temporalMollification f n t‖ ≤ ∫ s, (temporalBump n).normed volume s*B := by
    apply norm_integral_le_of_norm_le (hk.mul_const B)
    filter_upwards with s
    change ‖(temporalBump n).normed volume s*f (t-s)‖ ≤ _
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ((temporalBump n).nonneg_normed s),Real.norm_eq_abs]
    by_cases hs : s ∈ Metric.ball (0:ℝ) (temporalBump n).rOut
    · exact mul_le_mul_of_nonneg_left (hf s hs) ((temporalBump n).nonneg_normed s)
    · have hz : (temporalBump n).normed volume s=0 := by
        apply Function.notMem_support.mp
        rwa [(temporalBump n).support_normed_eq]
      simp only [hz,zero_mul,le_refl]
  rw [integral_mul_const,(temporalBump n).integral_normed,one_mul,Real.norm_eq_abs] at hh
  exact hh

theorem temporalMollification_support_comparison {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q)
    {D qc : ℝ} (hD0 : 0 ≤ D) (hD : ∀ t, |deriv q t| ≤ D)
    (hqc : ∀ t, qc ≤ q t) (n : ℕ) (hn : D*(temporalBump n).rOut ≤ qc/2)
    (t s : ℝ) (hs : s ∈ Metric.ball (0:ℝ) (temporalBump n).rOut) :
    q (t-s) ≤ 3*temporalMollification q n t := by
  have herr := (temporalMollification_uniform_error hq hD0 hD n t).trans hn
  have hd := temporal_derivative_difference hq hD (t-s) t
  have hs' : |s| ≤ (temporalBump n).rOut := by
    have hh := hs
    rw [Metric.mem_ball,Real.dist_eq,sub_zero] at hh
    exact hh.le
  have hds : |q (t-s)-q t| ≤ qc/2 := by
    have he : |t-s-t|=|s| := by rw [show t-s-t=-s by ring,abs_neg]
    rw [he] at hd
    exact hd.trans ((mul_le_mul_of_nonneg_left hs' hD0).trans hn)
  have h1 := (abs_le.mp herr).1
  have h2 := (abs_le.mp hds).2
  linarith [hqc t]

end Carleman
