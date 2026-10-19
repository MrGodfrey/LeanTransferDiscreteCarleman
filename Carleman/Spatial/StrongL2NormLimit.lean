module

public import Carleman.Spatial.L2LimitRepresentative
public import Carleman.Continuous.BochnerNormAlgebra

/-! Genuine L² error convergence implies norm and energy convergence;
Fatou also transfers convergent scalar energy bounds to an a.e. limit. -/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Carleman
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {ν : Measure Ω}

theorem bochnerL2Norm_reverse_triangle {f g : Ω → E} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    |bochnerL2Norm ν f-bochnerL2Norm ν g| ≤ bochnerL2Norm ν (fun x => f x-g x) := by
  change |bochnerL2Norm ν f-bochnerL2Norm ν g| ≤ bochnerL2Norm ν (f-g)
  rw [bochnerL2Norm_eq f hf,bochnerL2Norm_eq g hg,bochnerL2Norm_eq _ (hf.sub hg)]
  rw [MemLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _

theorem bochnerL2Norm_tendsto_of_error {f : Ω → E} {F : ℕ → Ω → E}
    (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (ht : Tendsto (fun n => bochnerL2Norm ν (fun x => F n x-f x)) atTop (𝓝 0)) :
    Tendsto (fun n => bochnerL2Norm ν (F n)) atTop (𝓝 (bochnerL2Norm ν f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun n => abs_nonneg _) (fun n => bochnerL2Norm_reverse_triangle (hF n) hf) ht

theorem l2_square_integral_tendsto_of_error {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (ht : Tendsto (fun n => bochnerL2Norm ν (fun x => F n x-f x)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (F n x)^2 ∂ν) atTop (𝓝 (∫ x, (f x)^2 ∂ν)) := by
  simpa only [integral_sq_eq_bochnerL2Norm_sq hf,integral_sq_eq_bochnerL2Norm_sq (hF _)] using
    (bochnerL2Norm_tendsto_of_error hf hF ht).pow 2

theorem l2_square_bound_of_ae_of_bound_tendsto {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (hl : ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {B : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b) (ht : Tendsto B atTop (𝓝 b))
    (hbound : ∀ n, (∫ x, (F n x)^2 ∂ν) ≤ B n) : (∫ x, (f x)^2 ∂ν) ≤ b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply l2_square_bound_of_ae_tendsto hf hF hl (by positivity)
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : b < b+ε))] with n hn
  exact (hbound n).trans hn.le

end Carleman
