module

public import Carleman.Periodic.CellExtension
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The manuscript's weighted sequence norms

`weightedSq` is exactly δt ∑ ‖uⁿ‖² for prescribed nodewise spatial
seminorms. Genuine weighted norms are included; seminorms are also needed for
observations and spatial differential expressions. No finite dimensionality
of the load or observation space is used. `powerSq` inserts the actual q
power into this same finite sum, rather than introducing an unrelated scalar.
-/

@[expose] public noncomputable section
open scoped BigOperators

namespace Carleman.TimeGrid
variable (g : Carleman.TimeGrid) {E F : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def weightedSq (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) : ℝ :=
  g.dt * ∑ i, (p i (u i)) ^ 2

def weightedNorm (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) : ℝ :=
  Real.sqrt (g.weightedSq p u)

theorem weightedSq_nonneg (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    0 ≤ g.weightedSq p u :=
  mul_nonneg g.dt_pos.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem weightedNorm_sq (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    g.weightedNorm p u ^ 2 = g.weightedSq p u :=
  Real.sq_sqrt (g.weightedSq_nonneg p u)

theorem weightedSq_eq_zero_iff (p : g.Index → Seminorm ℝ E)
    (hp : ∀ i x, p i x = 0 → x = 0) (u : g.Sequence E) :
    g.weightedSq p u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hs : ∑ i, (p i (u i)) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left (ne_of_gt g.dt_pos)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (p i (u i)))).mp hs
    funext i
    exact hp i (u i) (sq_eq_zero_iff.mp (hi i (Finset.mem_univ i)))
  · rintro rfl
    simp [weightedSq]

theorem weightedSq_le (p : g.Index → Seminorm ℝ E)
    (q : g.Index → Seminorm ℝ F) (u : g.Sequence E) (v : g.Sequence F)
    {C : ℝ} (h : ∀ i, (p i (u i)) ^ 2 ≤ C * (q i (v i)) ^ 2) :
    g.weightedSq p u ≤ C * g.weightedSq q v := by
  unfold weightedSq
  calc
    _ ≤ g.dt * ∑ i, C * (q i (v i)) ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) g.dt_pos.le
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Squared triangle inequality in the actual weighted sequence space. -/
theorem weightedSq_add_le (p : g.Index → Seminorm ℝ E) (u v : g.Sequence E) :
    g.weightedSq p (u + v) ≤ 2 * (g.weightedSq p u + g.weightedSq p v) := by
  unfold weightedSq
  calc
    _ ≤ g.dt * ∑ i, 2 * ((p i (u i)) ^ 2 + (p i (v i)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ g.dt_pos.le
      apply Finset.sum_le_sum
      intro i _
      have h := map_add_le_add (p i) (u i) (v i)
      have hn := apply_nonneg (p i) (u i + v i)
      have ha := apply_nonneg (p i) (u i)
      have hb := apply_nonneg (p i) (v i)
      change (p i (u i + v i)) ^ 2 ≤ _
      nlinarith [sq_nonneg (p i (u i) - p i (v i))]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]; ring

/-- Square of the norm with weight `q^(s/2) θ`. -/
def powerSq (q : g.Sequence ℝ) (s : ℝ) (p : g.Index → Seminorm ℝ E)
    (u : g.Sequence E) : ℝ :=
  g.dt * ∑ i, (q i) ^ s * (p i (u i)) ^ 2

theorem powerSq_nonneg (q : g.Sequence ℝ) (hq : ∀ i, 0 ≤ q i)
    (s : ℝ) (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    0 ≤ g.powerSq q s p u := by
  apply mul_nonneg g.dt_pos.le
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hq i) s) (sq_nonneg _)

@[simp] theorem powerSq_zero (q : g.Sequence ℝ) (p : g.Index → Seminorm ℝ E)
    (u : g.Sequence E) : g.powerSq q 0 p u = g.weightedSq p u := by
  simp [powerSq, weightedSq]

/-- This identifies the power convention with actual nodewise scalar multiplication. -/
theorem powerSq_eq_weightedSq (q : g.Sequence ℝ) (hq : ∀ i, 0 < q i)
    (s : ℝ) (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    g.powerSq q s p u = g.weightedSq p (fun i => (q i) ^ (s / 2) • u i) := by
  unfold powerSq weightedSq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hq i) _), mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hq i).le]
  congr 1
  ring

end Carleman.TimeGrid

@[expose] public noncomputable section
namespace Carleman

/-- Both signs of the excess exponent occur in the state-defect budget. -/
theorem rpow_le_max_one {q Q a : ℝ} (hq : 1 ≤ q) (hQ : q ≤ Q) :
    q ^ a ≤ max 1 (Q ^ a) := by
  by_cases ha : 0 ≤ a
  · exact (Real.rpow_le_rpow (by linarith) hQ ha).trans (le_max_right _ _)
  · exact (Real.rpow_le_one_of_one_le_of_nonpos hq (le_of_not_ge ha)).trans (le_max_left _ _)

namespace TimeGrid
variable (g : TimeGrid) {E F : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem powerSq_le (q : g.Sequence ℝ) (hq : ∀ i, 0 ≤ q i) (s : ℝ)
    (p : g.Index → Seminorm ℝ E) (p' : g.Index → Seminorm ℝ F)
    (u : g.Sequence E) (v : g.Sequence F) {C : ℝ}
    (h : ∀ i, (p i (u i)) ^ 2 ≤ C * (p' i (v i)) ^ 2) :
    g.powerSq q s p u ≤ C * g.powerSq q s p' v := by
  unfold powerSq
  calc
    _ ≤ g.dt * ∑ i, q i ^ s * (C * (p' i (v i)) ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (h i) (Real.rpow_nonneg (hq i) s)) g.dt_pos.le
    _ = _ := by simp only [mul_left_comm (q _ ^ s) C, ← Finset.mul_sum]; ring

theorem powerSq_add_le (q : g.Sequence ℝ) (hq : ∀ i, 0 ≤ q i) (s : ℝ)
    (p : g.Index → Seminorm ℝ E) (u v : g.Sequence E) :
    g.powerSq q s p (u + v) ≤ 2 * (g.powerSq q s p u + g.powerSq q s p v) := by
  unfold powerSq
  calc
    _ ≤ g.dt * ∑ i, q i ^ s * (2 * ((p i (u i)) ^ 2 + (p i (v i)) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ g.dt_pos.le
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hq i) s)
      have h := map_add_le_add (p i) (u i) (v i)
      have hn := apply_nonneg (p i) (u i + v i)
      have ha := apply_nonneg (p i) (u i)
      have hb := apply_nonneg (p i) (v i)
      change (p i (u i + v i)) ^ 2 ≤ _
      nlinarith [sq_nonneg (p i (u i) - p i (v i))]
    _ = _ := by simp only [mul_add, mul_left_comm (q _ ^ s) 2,
      Finset.sum_add_distrib, ← Finset.mul_sum]; ring

/-- Exact exponent loss relative to any other q-power, including negative excess. -/
theorem powerSq_change_exponent (q : g.Sequence ℝ) (hq : ∀ i, 1 ≤ q i)
    (Q : ℝ) (hQ : ∀ i, q i ≤ Q) (s t : ℝ)
    (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    g.powerSq q s p u ≤ max 1 (Q ^ (s - t)) * g.powerSq q t p u := by
  unfold powerSq
  calc
    _ ≤ g.dt * ∑ i, max 1 (Q ^ (s - t)) * (q i ^ t * (p i (u i)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ g.dt_pos.le
      apply Finset.sum_le_sum
      intro i _
      have hqi : 0 < q i := lt_of_lt_of_le zero_lt_one (hq i)
      have hp : q i ^ s = q i ^ (s - t) * q i ^ t := by
        rw [← Real.rpow_add hqi]; congr 1; ring
      rw [hp, mul_assoc]
      exact mul_le_mul_of_nonneg_right (rpow_le_max_one (hq i) (hQ i))
        (mul_nonneg (Real.rpow_nonneg hqi.le _) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem powerSq_mono_exponent (q : g.Sequence ℝ) (hq : ∀ i, 1 ≤ q i)
    {s t : ℝ} (hst : s ≤ t) (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    g.powerSq q s p u ≤ g.powerSq q t p u := by
  apply mul_le_mul_of_nonneg_left _ g.dt_pos.le
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (hq i) hst) (sq_nonneg _)

end TimeGrid
end Carleman

@[expose] public noncomputable section
namespace Carleman.TimeGrid
open scoped BigOperators
variable (g : Carleman.TimeGrid) {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem powerSq_node_smul_le (q : g.Sequence ℝ) (hq : ∀ i, 0 < q i)
    (s r : ℝ) (p : g.Index → Seminorm ℝ E) (μ : g.Sequence ℝ) (u : g.Sequence E)
    {C : ℝ} (hμ : ∀ i, μ i ^ 2 ≤ C * q i ^ r) :
    g.powerSq q s p (fun i => μ i • u i) ≤ C * g.powerSq q (s + r) p u := by
  unfold powerSq
  calc
    _ ≤ g.dt * ∑ i, C * (q i ^ (s + r) * (p i (u i)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ g.dt_pos.le
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul_eq_mul, Real.norm_eq_abs, mul_pow, sq_abs, Real.rpow_add (hq i)]
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hμ i) (sq_nonneg (p i (u i))))
        (Real.rpow_nonneg (hq i).le s)
      nlinarith only [h]
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Nonnegative powers cost exactly Q^s, without the spurious max at 1. -/
theorem powerSq_le_max_pow (q : g.Sequence ℝ) (hq : ∀ i, 1 ≤ q i)
    (Q : ℝ) (hQ : ∀ i, q i ≤ Q) (s : ℝ) (hs : 0 ≤ s)
    (p : g.Index → Seminorm ℝ E) (u : g.Sequence E) :
    g.powerSq q s p u ≤ Q ^ s * g.weightedSq p u := by
  have h := g.powerSq_change_exponent q hq Q hQ s 0 p u
  have hQ1 : 1 ≤ Q := (hq ⟨0, g.steps_pos⟩).trans (hQ ⟨0, g.steps_pos⟩)
  simpa only [sub_zero, powerSq_zero, max_eq_right (Real.one_le_rpow hQ1 hs)] using h
end Carleman.TimeGrid
