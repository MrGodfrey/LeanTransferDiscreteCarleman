module

public import Carleman.Periodic.WeightedNorm

/-! Algebra and Cauchy–Schwarz for the actual dt-weighted seminorm sums.
The spatial energy and inverse-weight test norms may differ. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.TimeGrid
variable (g : TimeGrid) {E F : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem weightedNorm_nonneg (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    0 ≤ g.weightedNorm p u := Real.sqrt_nonneg _

theorem weightedNorm_product_sum (p : g.Index → Seminorm ℝ E)
    (q : g.Index → Seminorm ℝ F) (u : g.Sequence E) (v : g.Sequence F) :
    g.dt * ∑ i, p i (u i) * q i (v i) ≤ g.weightedNorm p u * g.weightedNorm q v := by
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => p i (u i)) (fun i => q i (v i))
  have he (r : g.Index → ℝ) :
      Real.sqrt (g.dt * ∑ i, r i ^ 2) = Real.sqrt g.dt * Real.sqrt (∑ i, r i ^ 2) :=
    Real.sqrt_mul g.dt_pos.le _
  change _ ≤ Real.sqrt (g.dt * ∑ i, (p i (u i))^2) *
    Real.sqrt (g.dt * ∑ i, (q i (v i))^2)
  rw [he, he]
  calc
    _ ≤ g.dt * (Real.sqrt (∑ i, (p i (u i))^2) * Real.sqrt (∑ i, (q i (v i))^2)) :=
      mul_le_mul_of_nonneg_left hc g.dt_pos.le
    _ = (Real.sqrt g.dt)^2 *
        (Real.sqrt (∑ i, (p i (u i))^2) * Real.sqrt (∑ i, (q i (v i))^2)) := by
      rw [Real.sq_sqrt g.dt_pos.le]
    _ = _ := by ring

theorem weightedNorm_add_le (p : g.Index → Seminorm ℝ E) (u v : g.Sequence E) :
    g.weightedNorm p (u+v) ≤ g.weightedNorm p u + g.weightedNorm p v := by
  apply (sq_le_sq₀ (g.weightedNorm_nonneg p (u+v))
    (add_nonneg (g.weightedNorm_nonneg p u) (g.weightedNorm_nonneg p v))).mp
  rw [g.weightedNorm_sq]
  have hs : g.weightedSq p (u+v) ≤
      g.weightedSq p u + g.weightedSq p v + 2*(g.dt*∑ i, p i (u i)*p i (v i)) := by
    unfold weightedSq
    calc
      _ ≤ g.dt * ∑ i, (p i (u i)+p i (v i))^2 := by
        apply mul_le_mul_of_nonneg_left _ g.dt_pos.le
        apply Finset.sum_le_sum
        intro i _
        exact (sq_le_sq₀ (apply_nonneg _ _) (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))).mpr
          (map_add_le_add (p i) (u i) (v i))
      _ = _ := by
        simp only [add_sq, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
        ring
  have hc := g.weightedNorm_product_sum p p u v
  rw [← g.weightedNorm_sq p u, ← g.weightedNorm_sq p v] at hs
  nlinarith

theorem weightedNorm_sub_le (p : g.Index → Seminorm ℝ E) (u v : g.Sequence E) :
    g.weightedNorm p (u-v) ≤ g.weightedNorm p u + g.weightedNorm p v := by
  have he : g.weightedNorm p (-v) = g.weightedNorm p v := by
    simp only [weightedNorm, weightedSq, Pi.neg_apply, map_neg_eq_map]
  simpa only [sub_eq_add_neg, he] using g.weightedNorm_add_le p u (-v)

theorem weightedNorm_le_of_bound (p : g.Index → Seminorm ℝ E)
    (q : g.Index → Seminorm ℝ F) (u : g.Sequence E) (v : g.Sequence F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, p i (u i) ≤ C*q i (v i)) :
    g.weightedNorm p u ≤ C*g.weightedNorm q v := by
  apply (sq_le_sq₀ (g.weightedNorm_nonneg p u)
    (mul_nonneg hC (g.weightedNorm_nonneg q v))).mp
  rw [mul_pow, g.weightedNorm_sq, g.weightedNorm_sq]
  apply g.weightedSq_le
  intro i
  rw [← mul_pow]
  exact (sq_le_sq₀ (apply_nonneg _ _) (mul_nonneg hC (apply_nonneg _ _))).mpr (hb i)

/-- Lift the actual nodewise shifted-form or stiffness-defect estimate to
the periodic weighted L² norms, with exactly the same constant. -/
theorem weighted_bilinear_sum_bound (p : g.Index → Seminorm ℝ E)
    (q : g.Index → Seminorm ℝ F) (B : g.Index → E → F → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ i u v, |B i u v| ≤ C*p i u*q i v)
    (u : g.Sequence E) (v : g.Sequence F) :
    |g.dt * ∑ i, B i (u i) (v i)| ≤ C*g.weightedNorm p u*g.weightedNorm q v := by
  rw [abs_mul, abs_of_pos g.dt_pos]
  calc
    _ ≤ g.dt * ∑ i, |B i (u i) (v i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) g.dt_pos.le
    _ ≤ g.dt * ∑ i, C*p i (u i)*q i (v i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hB i (u i) (v i)) g.dt_pos.le
    _ = C*(g.dt*∑ i, p i (u i)*q i (v i)) := by
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (g.weightedNorm_product_sum p q u v) hC

end Carleman.TimeGrid
