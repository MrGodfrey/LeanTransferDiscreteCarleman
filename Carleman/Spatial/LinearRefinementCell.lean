module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-! Exact cell mass and edge energy of linear interpolation on a uniformly
refined interval. The coefficient twelve is independent of the refinement. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman

def linearRefinementValue (m : ℕ) (a b : ℝ) (k : ℕ) : ℝ :=
  a+(k:ℝ)/(m:ℝ)*(b-a)

def linearRefinementMass (m : ℕ) (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, ((linearRefinementValue m a b k)^2+
    (linearRefinementValue m a b (k+1))^2)/2

def linearRefinementEnergy (m : ℕ) (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, (linearRefinementValue m a b (k+1)-linearRefinementValue m a b k)^2

theorem sum_affine_sq (n : ℕ) (a b : ℝ) :
    (∑ k ∈ Finset.range n, (a+(k:ℝ)*b)^2) =
      (n:ℝ)*a^2+a*b*(n:ℝ)*((n:ℝ)-1)+b^2*(n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)/6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; push_cast; ring

theorem linearRefinementMass_eq (m : ℕ) (hm : 0 < m) (a b : ℝ) :
    linearRefinementMass m a b =
      (m:ℝ)*(a^2+a*b+b^2)/3+(a-b)^2/(6*(m:ℝ)) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he (k : ℕ) : linearRefinementValue m a b (k+1) =
      (a+(b-a)/(m:ℝ))+(k:ℝ)*((b-a)/(m:ℝ)) := by
    unfold linearRefinementValue
    push_cast
    ring
  have he0 (k : ℕ) : linearRefinementValue m a b k = a+(k:ℝ)*((b-a)/(m:ℝ)) := by
    unfold linearRefinementValue
    ring
  unfold linearRefinementMass
  simp only [he]
  simp only [he0]
  rw [← Finset.sum_div,Finset.sum_add_distrib,sum_affine_sq,sum_affine_sq]
  field_simp
  ring

theorem linearRefinementEnergy_eq (m : ℕ) (hm : 0 < m) (a b : ℝ) :
    linearRefinementEnergy m a b = (b-a)^2/(m:ℝ) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he (k : ℕ) : linearRefinementValue m a b (k+1)-linearRefinementValue m a b k = (b-a)/(m:ℝ) := by
    unfold linearRefinementValue
    push_cast
    ring
  simp only [linearRefinementEnergy,he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,div_pow]
  field_simp

theorem linearRefinement_inverse (m : ℕ) (hm : 0 < m) (a b : ℝ) :
    linearRefinementEnergy m a b ≤ 12/(m:ℝ)^2*linearRefinementMass m a b := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  rw [linearRefinementEnergy_eq m hm,linearRefinementMass_eq m hm]
  apply (mul_le_mul_iff_left₀ (show 0 < (m:ℝ)^2 by positivity)).mp
  field_simp
  nlinarith [sq_nonneg (a+b),sq_nonneg (a-b)]

end Carleman
