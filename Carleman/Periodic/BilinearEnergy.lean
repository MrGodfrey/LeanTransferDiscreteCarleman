module

public import Carleman.Periodic.EulerVariational

/-! Exact cyclic energy identities for a symmetric bilinear form and a
variable scalar shift. The permutation formulation covers both directions. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- The periodic boundary terms cancel for every symmetric bilinear form. -/
theorem sum_bilinear_increment (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (τ : ι ≃ ι) (u : ι → E) :
    2 * (∑ i, B (u i - u (τ i)) (u i)) =
      ∑ i, B (u i - u (τ i)) (u i - u (τ i)) := by
  have hs := Equiv.sum_comp τ (fun i => B (u i) (u i))
  have hc : (∑ i, B (u i) (u (τ i))) = ∑ i, B (u (τ i)) (u i) :=
    Finset.sum_congr rfl fun i _ => hB _ _
  simp only [map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, hs, hc]
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact variable-shift correction. For D+ the forward increment appears;
for D- its reflected analogue appears, with the same sign and constants. -/
theorem sum_weighted_increment (τ : ι ≃ ι) (μ : ι → ℝ) (u : ι → H) :
    2 * (∑ i, μ i * inner ℝ (u i - u (τ i)) (u i)) =
      (∑ i, μ i * ‖u i - u (τ i)‖^2) -
      ∑ i, (μ (τ.symm i) - μ i) * ‖u i‖^2 := by
  have hs : (∑ i, μ i * inner ℝ (u (τ i)) (u (τ i))) =
      ∑ i, μ (τ.symm i) * inner ℝ (u i) (u i) := by
    simpa only [Equiv.symm_apply_apply] using
      Equiv.sum_comp τ (fun i => μ (τ.symm i) * inner ℝ (u i) (u i))
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    mul_sub, Finset.sum_sub_distrib, hs]
  have hc : (∑ i, μ i * inner ℝ (u i) (u (τ i))) =
      ∑ i, μ i * inner ℝ (u (τ i)) (u i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (u i) (u (τ i))]
  rw [hc]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

end Carleman
