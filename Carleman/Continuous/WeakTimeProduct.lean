module

public import Carleman.Continuous.WeakTimeEnergy

/-! Multiplication of general H-valued weak trajectories by time-dependent
bounded operators. Absolute continuity, rather than everywhere classical
regularity of the trajectory, justifies the product rule. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff
namespace Carleman

/-- Operator evaluation preserves absolute continuity on a compact interval. -/
theorem absolutelyContinuous_clm_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}
    {W : ℝ → E →L[ℝ] F} {u : ℝ → E}
    (hW : AbsolutelyContinuousOnInterval W a b) (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t => W t (u t)) a b := by
  obtain ⟨C, hC⟩ := hW.exists_bound
  obtain ⟨D, hD⟩ := hu.exists_bound
  unfold AbsolutelyContinuousOnInterval at hW hu ⊢
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
    ?_ (by simpa using (hu.const_mul C).add (hW.const_mul D))
  rw [eventually_inf_principal]
  filter_upwards with p hp
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hx := (hp.1 i hi).1
  have hy := (hp.1 i hi).2
  calc
    _ ≤ dist (W (p.2 i).1 (u (p.2 i).1)) (W (p.2 i).1 (u (p.2 i).2)) +
        dist (W (p.2 i).1 (u (p.2 i).2)) (W (p.2 i).2 (u (p.2 i).2)) := dist_triangle _ _ _
    _ ≤ C*dist (u (p.2 i).1) (u (p.2 i).2) + D*dist (W (p.2 i).1) (W (p.2 i).2) := by
      simp only [dist_eq_norm, ← map_sub, ← sub_apply]
      apply add_le_add
      · exact ((W (p.2 i).1).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hC _ hx) (norm_nonneg _))
      · exact ((W (p.2 i).1-W (p.2 i).2).le_opNorm _).trans (by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left (hD _ hy) (norm_nonneg (W (p.2 i).1-W (p.2 i).2)))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- AC plus an a.e. strong derivative in L² yields the actual H-valued
Bochner weak derivative. Scalar projections suffice without H separability. -/
theorem HasWeakTimeDerivative.of_ac_ae {g : TimeGrid} {u du : ℝ → H}
    (hu : AbsolutelyContinuousOnInterval u 0 g.period) (hd : MemLp du 2 g.timeMeasure)
    (hder : ∀ᵐ t ∂g.timeMeasure, HasDerivAt u (du t) t) : HasWeakTimeDerivative g u du := by
  have huc : ContinuousOn u (Icc 0 g.period) := by
    simpa only [uIcc_of_le g.period_pos.le] using hu.continuousOn
  intro φ hφ _ hsupp
  have hφ0 : φ 0=0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl 0) (hsupp h).1)
  have hφT : φ g.period=0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl g.period) (hsupp h).2)
  have hiu : Integrable (fun t => deriv φ t • u t) g.timeMeasure :=
    memLp_one_iff_integrable.mp ((g.memLp_of_continuousOn
      (hφ.continuous_deriv (by simp)).continuousOn).smul (g.memLp_of_continuousOn huc))
  have hid : Integrable (fun t => φ t • du t) g.timeMeasure :=
    memLp_one_iff_integrable.mp ((g.memLp_of_continuousOn hφ.continuous.continuousOn).smul hd)
  apply ext_inner_left ℝ
  intro z
  have hscalar : AbsolutelyContinuousOnInterval (fun t => inner ℝ z (u t)) 0 g.period :=
    (innerSL ℝ z).lipschitzWith.comp_absolutelyContinuousOnInterval hu
  have hφAC : AbsolutelyContinuousOnInterval φ 0 g.period :=
    (hφ.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have he := (hφAC.fun_mul hscalar).integral_deriv_eq_sub
  rw [hφ0, hφT, zero_mul, zero_mul, sub_self, ← g.timeIntegral_eq_intervalIntegral] at he
  have ha : (fun t => deriv (fun s => φ s * inner ℝ z (u s)) t) =ᵐ[g.timeMeasure]
      (fun t => deriv φ t * inner ℝ z (u t) + φ t * inner ℝ z (du t)) := by
    filter_upwards [hder] with t ht
    have hi := (innerSL ℝ z).hasFDerivAt.comp_hasDerivAt t ht
    exact ((hφ.differentiable (by simp) t).hasDerivAt.fun_mul hi).deriv
  have hi1 := hiu.const_inner (𝕜 := ℝ) z
  have hi2 := hid.const_inner (𝕜 := ℝ) z
  simp only [inner_smul_right] at hi1 hi2
  rw [integral_congr_ae ha, integral_add hi1 hi2] at he
  rw [inner_neg_right, ← integral_inner hiu z, ← integral_inner hid z]
  simp only [inner_smul_right]
  linarith

/-- Genuine weak product rule for an operator-valued AC coefficient. -/
theorem HasWeakTimeDerivative.clm_apply {g : TimeGrid} {u du : ℝ → H}
    (hu : HasWeakTimeDerivative g u du) (huc : ContinuousOn u (Icc 0 g.period))
    (hdu : MemLp du 2 g.timeMeasure) {W dW : ℝ → H →L[ℝ] H}
    (hW : AbsolutelyContinuousOnInterval W 0 g.period)
    (hdW : ∀ᵐ t ∂g.timeMeasure, HasDerivAt W (dW t) t)
    (hi : MemLp (fun t => dW t (u t) + W t (du t)) 2 g.timeMeasure) :
    HasWeakTimeDerivative g (fun t => W t (u t)) (fun t => dW t (u t) + W t (du t)) := by
  apply HasWeakTimeDerivative.of_ac_ae (absolutelyContinuous_clm_apply hW (hu.absolutelyContinuous huc hdu)) hi
  filter_upwards [hdW, hu.ae_hasDerivAt huc hdu] with t h1 h2
  exact h1.clm_apply h2
end Carleman
