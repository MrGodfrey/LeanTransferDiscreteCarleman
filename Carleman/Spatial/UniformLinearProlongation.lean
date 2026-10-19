module

public import Carleman.Spatial.LinearRefinementCell

/-! Genuine piecewise linear interpolation of coarse nodal values on a
uniform fine grid, and its exact cell decomposition. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman

def uniformLinearProlongation (m : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  linearRefinementValue m (u (k/m)) (u (k/m+1)) (k%m)

theorem linearRefinementValue_zero (m : ℕ) (a b : ℝ) : linearRefinementValue m a b 0 = a := by
  simp [linearRefinementValue]

theorem linearRefinementValue_end (m : ℕ) (hm : 0 < m) (a b : ℝ) :
    linearRefinementValue m a b m = b := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp [linearRefinementValue,hm0]

theorem uniformLinearProlongation_node (m : ℕ) (hm : 0 < m) (u : ℕ → ℝ) (j : ℕ) :
    uniformLinearProlongation m u (m*j) = u j := by
  simp [uniformLinearProlongation,hm.ne',linearRefinementValue_zero]

theorem uniformLinearProlongation_cell (m : ℕ) (hm : 0 < m) (u : ℕ → ℝ)
    (j k : ℕ) (hk : k ≤ m) :
    uniformLinearProlongation m u (m*j+k) = linearRefinementValue m (u j) (u (j+1)) k := by
  rcases lt_or_eq_of_le hk with hk|hk
  · have hdiv : (m*j+k)/m = j := by
      rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hk,Nat.add_zero]
    have hmod : (m*j+k)%m = k := by simp [Nat.add_mod,Nat.mod_eq_of_lt hk]
    simp only [uniformLinearProlongation,hdiv,hmod]
  · subst k
    rw [show m*j+m=m*(j+1) by ring,uniformLinearProlongation_node m hm,
      linearRefinementValue_end m hm]

theorem sum_uniform_blocks (m K : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (m*K), f k) =
      ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range m, f (m*j+k) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih,Finset.sum_range_succ]

theorem uniformLinearProlongation_energy_cells (m K : ℕ) (hm : 0 < m) (u : ℕ → ℝ) :
    (∑ k ∈ Finset.range (m*K),
      (uniformLinearProlongation m u (k+1)-uniformLinearProlongation m u k)^2) =
      ∑ j ∈ Finset.range K, linearRefinementEnergy m (u j) (u (j+1)) := by
  rw [sum_uniform_blocks]
  apply Finset.sum_congr rfl
  intro j _
  unfold linearRefinementEnergy
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [show m*j+k+1=m*j+(k+1) by omega,uniformLinearProlongation_cell m hm u j (k+1) (by omega),
    uniformLinearProlongation_cell m hm u j k (by omega)]

theorem uniformLinearProlongation_mass_cells (m K : ℕ) (hm : 0 < m) (u : ℕ → ℝ) :
    (∑ k ∈ Finset.range (m*K),
      ((uniformLinearProlongation m u k)^2+(uniformLinearProlongation m u (k+1))^2)/2) =
      ∑ j ∈ Finset.range K, linearRefinementMass m (u j) (u (j+1)) := by
  rw [sum_uniform_blocks]
  apply Finset.sum_congr rfl
  intro j _
  unfold linearRefinementMass
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [show m*j+k+1=m*j+(k+1) by omega,uniformLinearProlongation_cell m hm u j (k+1) (by omega),
    uniformLinearProlongation_cell m hm u j k (by omega)]

end Carleman
