module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Field.Periodic

/-! Actual normalized smooth convolutions on real time, retaining periodicity and bounds. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Convolution ContDiff Topology
namespace Carleman

def temporalBump (n : ℕ) : ContDiffBump (0:ℝ) where
  rIn := 1/((n:ℝ)+1)
  rOut := 2/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

def temporalMollification (q : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (temporalBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] q

theorem temporalMollification_smooth {q : ℝ → ℝ} (hq : Continuous q) (n : ℕ) :
    ContDiff ℝ ∞ (temporalMollification q n) :=
  (temporalBump n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (temporalBump n).contDiff_normed hq.locallyIntegrable

theorem temporalMollification_periodic {q : ℝ → ℝ} {T : ℝ}
    (hq : Function.Periodic q T) (n : ℕ) : Function.Periodic (temporalMollification q n) T := by
  intro t
  change (∫ y, (temporalBump n).normed volume y*q (t+T-y))=
    ∫ y, (temporalBump n).normed volume y*q (t-y)
  apply integral_congr_ae
  filter_upwards with y
  rw [show t+T-y=(t-y)+T by ring,hq]

theorem temporalMollification_bounds {q : ℝ → ℝ} (hq : Continuous q)
    {a b : ℝ} (ha : ∀ t, a ≤ q t) (hb : ∀ t, q t ≤ b) (n : ℕ) (t : ℝ) :
    a ≤ temporalMollification q n t ∧ temporalMollification q n t ≤ b := by
  have hi : Integrable (fun y => (temporalBump n).normed volume y*q (t-y)) volume :=
    (temporalBump n).hasCompactSupport_normed.convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (temporalBump n).continuous_normed hq.locallyIntegrable t
  have hk := (temporalBump n).integrable_normed (μ := volume)
  have h1 := integral_mono (hk.mul_const a) hi
    (fun y => mul_le_mul_of_nonneg_left (ha (t-y)) ((temporalBump n).nonneg_normed y))
  have h2 := integral_mono hi (hk.mul_const b)
    (fun y => mul_le_mul_of_nonneg_left (hb (t-y)) ((temporalBump n).nonneg_normed y))
  rw [integral_mul_const,(temporalBump n).integral_normed,one_mul] at h1 h2
  exact ⟨h1,h2⟩

theorem temporalBump_radius_tendsto : Tendsto (fun n => (temporalBump n).rOut) atTop (𝓝 (0:ℝ)) := by
  have hh := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  convert! hh.const_mul 2 using 1 <;> simp [temporalBump,div_eq_mul_inv]

theorem temporalMollification_tendsto {q : ℝ → ℝ} (hq : Continuous q) (t : ℝ) :
    Tendsto (fun n => temporalMollification q n t) atTop (𝓝 (q t)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous temporalBump_radius_tendsto hq t

theorem continuous_periodic_bounded {q : ℝ → ℝ} (hq : Continuous q) {T : ℝ}
    (hT : 0 < T) (hp : Function.Periodic q T) : ∃ B : ℝ, 0 < B ∧ ∀ t, |q t| ≤ B := by
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0:ℝ) T) hq.continuousOn
  refine ⟨|D|+1,by positivity,?_⟩
  intro t
  obtain ⟨s,hs,he⟩ := hp.exists_mem_Ico₀ hT t
  have hh := hD s (Ico_subset_Icc_self hs)
  rw [he,← Real.norm_eq_abs]
  linarith [le_abs_self D]

end Carleman
