module

public import Carleman.Spatial.DirichletSpace
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Strong L² convergence from actual a.e. convergence and an integrable
bound for squared differences; this will be applied to mollified fields. -/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace Carleman
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E]

theorem lp_two_norm_sub_sq_integral (u v : Lp E 2 μ) :
    ‖u-v‖^2 = ∫ x, ‖u x-v x‖^2 ∂μ := by
  have hn : ‖u-v‖ = Real.sqrt (∫ x, ‖(u-v) x‖^2 ∂μ) := by
    rw [Lp.norm_def,toReal_eLpNorm,
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp)
        (Lp.aestronglyMeasurable (u-v))]
    simp [Real.sqrt_eq_rpow]
  rw [hn,Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v] with x hx
  rw [hx,Pi.sub_apply]

theorem lp_two_tendsto_of_dominated_norm_sq (u : ℕ → Lp E 2 μ) (v : Lp E 2 μ)
    (b : α → ℝ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖u n x-v x‖^2 ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    Tendsto u atTop (𝓝 v) := by
  have hi : Tendsto (fun n => ∫ x, ‖u n x-v x‖^2 ∂μ) atTop (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence b
    · intro n
      exact ((Lp.aestronglyMeasurable (u n)).sub (Lp.aestronglyMeasurable v)).norm.pow 2
    · exact hb
    · intro n
      filter_upwards [hbound n] with x hx
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖u n x-v x‖)] using hx
    · filter_upwards [hlim] with x hx
      have hc : Tendsto (fun _n : ℕ => v x) atTop (𝓝 (v x)) := tendsto_const_nhds
      simpa only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] using
        (hx.sub hc).norm.pow 2
  simp only [integral_zero,← lp_two_norm_sub_sq_integral] at hi
  have hn := hi.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hn
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr hn

theorem lp_two_tendsto_of_bounded_support (u : ℕ → Lp E 2 μ) (v : Lp E 2 μ)
    (K : Set α) (hK : MeasurableSet K) (hfin : μ K < ∞) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ B ∧ (x ∉ K → u n x = 0))
    (hv : ∀ᵐ x ∂μ, ‖v x‖ ≤ B ∧ (x ∉ K → v x = 0))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    Tendsto u atTop (𝓝 v) := by
  apply lp_two_tendsto_of_dominated_norm_sq u v (K.indicator (fun _ => (2*B)^2))
  · exact memLp_one_iff_integrable.mp
      (memLp_indicator_const _ hK.nullMeasurableSet _ (.inr hfin.ne))
  · intro n
    filter_upwards [hu n,hv] with x hx hy
    by_cases h : x ∈ K
    · rw [Set.indicator_of_mem h]
      have hh : ‖u n x-v x‖ ≤ 2*B := (norm_sub_le _ _).trans (by linarith [hx.1,hy.1])
      nlinarith [norm_nonneg (u n x-v x)]
    · rw [Set.indicator_of_notMem h,hx.2 h,hy.2 h]
      simp
  · exact hlim

end Carleman
