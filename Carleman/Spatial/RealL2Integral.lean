module

public import Carleman.Spatial.SpacetimeWeightedNorm

/-! Integral formulas and Cauchy--Schwarz for genuine scalar L² functions. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}

theorem integral_mul_eq_L2_inner (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]

theorem integral_sq_eq_bochnerL2Norm_sq (hf : MemLp f 2 μ) :
    (∫ x, f x^2 ∂μ) = (bochnerL2Norm μ f)^2 := by
  rw [bochnerL2Norm_sq_integral hf]
  simp only [Real.norm_eq_abs, sq_abs]

theorem integral_mul_sq_le (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ)*(∫ x, g x^2 ∂μ) := by
  rw [integral_mul_eq_L2_inner hf hg, integral_sq_eq_bochnerL2Norm_sq hf,
    integral_sq_eq_bochnerL2Norm_sq hg, bochnerL2Norm_eq _ hf, bochnerL2Norm_eq _ hg]
  have h := sq_le_sq₀ (abs_nonneg (inner ℝ (hf.toLp f) (hg.toLp g)))
    (mul_nonneg (norm_nonneg (hf.toLp f)) (norm_nonneg (hg.toLp g)))
  simpa only [sq_abs, mul_pow] using h.mpr (abs_real_inner_le_norm _ _)

theorem abs_integral_mul_le (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x*g x ∂μ| ≤ bochnerL2Norm μ f*bochnerL2Norm μ g := by
  rw [integral_mul_eq_L2_inner hf hg, bochnerL2Norm_eq _ hf, bochnerL2Norm_eq _ hg]
  exact abs_real_inner_le_norm _ _

end Carleman
