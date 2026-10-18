module

public import Carleman.Periodic.BilinearEnergy

/-! Section 4's exact weighted time identity for a varying symmetric test
operator. The permutation formulation covers both original time directions.
No scalar-weight reduction or commutation of neighboring operators is used. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

theorem sum_variable_bilinear_increment (B : ι → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ i v w, B i v w = B i w v) (τ : ι ≃ ι) (u : ι → E) :
    2 * (∑ i, B i (u i - u (τ i)) (u i)) =
      (∑ i, B i (u i - u (τ i)) (u i - u (τ i))) +
      ∑ i, (B i (u i) (u i) - B (τ.symm i) (u i) (u i)) := by
  have hs : (∑ i, B i (u (τ i)) (u (τ i))) =
      ∑ i, B (τ.symm i) (u i) (u i) := by
    simpa only [Equiv.symm_apply_apply] using
      Equiv.sum_comp τ (fun i => B (τ.symm i) (u i) (u i))
  have hc : (∑ i, B i (u i) (u (τ i))) = ∑ i, B i (u (τ i)) (u i) :=
    Finset.sum_congr rfl fun i _ => hB i _ _
  simp only [map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, hs, hc]
  ring

namespace TimeGrid
variable (g : TimeGrid) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `eq:weighted-time-summation`, including the actual dt pairing and the
forward test-operator increment for D+, with its reflected version for D-. -/
theorem pairing_variable_operator (s : Orientation) (T : g.Index → H →ₗ[ℝ] H)
    (hT : ∀ i v w, inner ℝ v (T i w) = inner ℝ w (T i v)) (u : g.Sequence H) :
    g.pairing (s.difference g u) (fun i => T i (u i)) =
      (1 / 2) * (∑ i, inner ℝ (u i - u (s.neighbor g i))
        (T i (u i - u (s.neighbor g i)))) +
      (1 / 2) * ∑ i, inner ℝ (u i) ((T i - T ((s.neighbor g).symm i)) (u i)) := by
  let B : g.Index → H →ₗ[ℝ] H →ₗ[ℝ] ℝ :=
    fun i => (innerₗ H).compl₂ (T i)
  have he := sum_variable_bilinear_increment B hT (s.neighbor g) u
  change 2 * (∑ i, inner ℝ (u i - u (s.neighbor g i)) (T i (u i))) =
    (∑ i, inner ℝ (u i - u (s.neighbor g i)) (T i (u i - u (s.neighbor g i)))) +
    ∑ i, (inner ℝ (u i) (T i (u i)) -
      inner ℝ (u i) (T ((s.neighbor g).symm i) (u i))) at he
  simp only [pairing, Orientation.difference_neighbor, real_inner_smul_left,
    ← Finset.mul_sum, LinearMap.sub_apply, inner_sub_right]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt g.dt_pos), one_mul]
  linarith only [he]

/-- Positivity discards the increment energy; the only negative contribution
is the actual variation of the test operator, bounded node by node. -/
theorem pairing_variable_operator_lower (s : Orientation) (T : g.Index → H →ₗ[ℝ] H)
    (hT : ∀ i v w, inner ℝ v (T i w) = inner ℝ w (T i v))
    (hpos : ∀ i v, 0 ≤ inner ℝ v (T i v)) (u : g.Sequence H)
    (b : g.Index → ℝ)
    (hinc : ∀ i, inner ℝ (u i) ((T ((s.neighbor g).symm i) - T i) (u i)) ≤
      g.dt * b i) :
    -(1 / 2) * g.dt * ∑ i, b i ≤
      g.pairing (s.difference g u) (fun i => T i (u i)) := by
  rw [g.pairing_variable_operator s T hT u]
  have hp := Finset.sum_nonneg (s := Finset.univ) fun i _ =>
    hpos i (u i - u (s.neighbor g i))
  have hi := Finset.sum_le_sum (s := Finset.univ) fun i _ => hinc i
  simp only [LinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hi ⊢
  linarith

end TimeGrid
end Carleman
