module

public import Carleman.Spatial.StrongL2NormLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Strong L² convergence under actual bounded scalar multipliers. These
limits are used to pass a smooth scalar chain rule to weak derivatives. -/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem memLp_mul_of_ae_bound {a g : Ω → ℝ} (ha : AEStronglyMeasurable a ν)
    (hg : MemLp g 2 ν) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ x ∂ν, |a x| ≤ M) :
    MemLp (fun x => a x*g x) 2 ν := by
  apply (hg.norm.const_mul M).of_le (ha.mul hg.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖a x*g x‖ ≤ ‖M*‖g x‖‖
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hM,abs_abs] using
    mul_le_mul_of_nonneg_right hx (abs_nonneg (g x))

theorem bochnerL2Norm_mul_le_of_ae_bound {a g : Ω → ℝ} (ha : AEStronglyMeasurable a ν)
    (hg : MemLp g 2 ν) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ x ∂ν, |a x| ≤ M) :
    bochnerL2Norm ν (fun x => a x*g x) ≤ M*bochnerL2Norm ν g := by
  have hm := memLp_mul_of_ae_bound ha hg hM hb
  rw [bochnerL2Norm_eq _ hm,bochnerL2Norm_eq _ hg]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hm.coeFn_toLp,hg.coeFn_toLp,hb] with x hx hy hz
  rw [hx,hy,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_right hz (abs_nonneg (g x))

theorem l2_bounded_multiplier_zero_tendsto {a : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) ν) (hg : MemLp g 2 ν)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ n, ∀ᵐ x ∂ν, |a n x| ≤ M)
    (ht : ∀ᵐ x ∂ν, Tendsto (fun n => a n x) atTop (𝓝 0)) :
    Tendsto (fun n => bochnerL2Norm ν (fun x => a n x*g x)) atTop (𝓝 0) := by
  have hm (n : ℕ) := memLp_mul_of_ae_bound (ha n) hg hM (hb n)
  have he : Tendsto (fun n => ∫ x, (a n x*g x)^2 ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (F := fun n x => (a n x*g x)^2) (f := fun _ => (0:ℝ)) (fun x => M^2*(g x)^2)
      (fun n => (hm n).aestronglyMeasurable.pow 2) (hg.integrable_sq.const_mul (M^2))
      (fun n => (hb n).mono fun x hx => ?_) (ht.mono fun x hx => ?_)
    · simpa only [integral_zero] using h
    · rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),mul_pow]
      exact mul_le_mul_of_nonneg_right (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr hx)
        (sq_nonneg (g x))
    · simpa only [zero_mul,zero_pow (by decide : 2 ≠ 0)] using (hx.mul_const (g x)).pow 2
  have hs := he.sqrt
  simpa only [integral_sq_eq_bochnerL2Norm_sq (hm _),Real.sqrt_sq (bochnerL2Norm_nonneg _),Real.sqrt_zero] using hs

theorem l2_bounded_multiplier_strong_tendsto {a : ℕ → Ω → ℝ} {b g : Ω → ℝ}
    {G : ℕ → Ω → ℝ} (ha : ∀ n, AEStronglyMeasurable (a n) ν)
    (hb : AEStronglyMeasurable b ν) (hg : MemLp g 2 ν) (hG : ∀ n, MemLp (G n) 2 ν)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ n, ∀ᵐ x ∂ν, |a n x| ≤ M)
    (hboundb : ∀ᵐ x ∂ν, |b x| ≤ M)
    (ht : ∀ᵐ x ∂ν, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (hstrong : Tendsto (fun n => bochnerL2Norm ν (fun x => G n x-g x)) atTop (𝓝 0)) :
    Tendsto (fun n => bochnerL2Norm ν (fun x => a n x*G n x-b x*g x)) atTop (𝓝 0) := by
  have hdiff (n : ℕ) : ∀ᵐ x ∂ν, |a n x-b x| ≤ 2*M := by
    filter_upwards [hbound n,hboundb] with x hx hy
    exact (abs_sub _ _).trans (by linarith)
  have hzero := l2_bounded_multiplier_zero_tendsto (fun n => (ha n).sub hb) hg
    (by positivity : 0 ≤ 2*M) hdiff (ht.mono fun x hx => by simpa using hx.sub_const (b x))
  have hle (n : ℕ) : bochnerL2Norm ν (fun x => a n x*G n x-b x*g x) ≤
      M*bochnerL2Norm ν (fun x => G n x-g x)+bochnerL2Norm ν (fun x => (a n x-b x)*g x) := by
    have hid : (fun x => a n x*G n x-b x*g x) =
        (fun x => a n x*(G n x-g x))+(fun x => (a n x-b x)*g x) := by funext x; simp only [Pi.add_apply]; ring
    rw [hid]
    exact (bochnerL2Norm_add (memLp_mul_of_ae_bound (ha n) ((hG n).sub hg) hM (hbound n))
      (memLp_mul_of_ae_bound ((ha n).sub hb) hg (by positivity) (hdiff n))).trans
      (add_le_add (bochnerL2Norm_mul_le_of_ae_bound (ha n) ((hG n).sub hg) hM (hbound n)) le_rfl)
  apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) hle
  have hh := (hstrong.const_mul M).add hzero
  simp only [mul_zero,add_zero] at hh
  exact hh

end Carleman
