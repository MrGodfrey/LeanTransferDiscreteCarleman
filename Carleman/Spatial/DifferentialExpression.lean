module

public import Carleman.Spatial.OperatorMultiplier
public import Carleman.Transfer.Weights
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite-order expressions with bounded spatial coefficients

Each coefficient acts on an actual L² derivative field (possibly a Euclidean
collection). The expression is a finite sum of those pointwise actions. Its
order bound is proved, not supplied as a norm inequality. Identification of
input fields with Sobolev derivatives is a separate spatial realization.
-/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  {m : ℕ} {E : Fin (m+1) → Type*}
  [∀ k, NormedAddCommGroup (E k)] [∀ k, NormedSpace ℝ (E k)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Coefficients of an expression of order at most j. Higher-order fields are
excluded by construction, not by a hypothesis about the resulting norm. -/
structure DifferentialExpression (ν : Measure Ω) (E : Fin (m+1) → Type*)
    [∀ k, NormedAddCommGroup (E k)] [∀ k, NormedSpace ℝ (E k)]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) where
  coefficient : ∀ k, OperatorMultiplier ν (E k) F

namespace DifferentialExpression
variable {j : ℕ} (D : DifferentialExpression ν E F j)

/-- The square-sum of fixed spatial coefficient bounds, independent of weights. -/
def boundSq : ℝ := ∑ k : Fin (m+1), (D.coefficient k).bound ^ 2

theorem boundSq_nonneg : 0 ≤ D.boundSq := Finset.sum_nonneg fun _ _ => sq_nonneg _

def orders (_D : DifferentialExpression ν E F j) : Finset (Fin (m+1)) := Finset.univ.filter (fun k => k.val ≤ j)

def apply (u : ∀ k, Lp (E k) 2 ν) : Lp F 2 ν :=
  ∑ k ∈ D.orders, (D.coefficient k).map (u k)

/-- Representative identity for the finite spatial differential expression. -/
theorem apply_ae (u : ∀ k, Lp (E k) 2 ν) :
    D.apply u =ᵐ[ν] (fun x => ∑ k ∈ D.orders, (D.coefficient k).value x (u k x)) := by
  filter_upwards [Lp.coeFn_finsetSum D.orders (fun k => (D.coefficient k).map (u k)),
    ae_all_iff.mpr (fun k => (D.coefficient k).map_ae (u k))] with x hx ha
  dsimp only [apply]
  rw [hx, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => ha k)

def linearMap : (∀ k, Lp (E k) 2 ν) →ₗ[ℝ] Lp F 2 ν where
  toFun := D.apply
  map_add' u v := by simp only [apply, Pi.add_apply, OperatorMultiplier.map_add, Finset.sum_add_distrib]
  map_smul' c u := by simp only [apply, Pi.smul_apply, OperatorMultiplier.map_smul, Finset.smul_sum, RingHom.id_apply]

/-- Real spatial weighted L² estimate before inserting temporal q powers. -/
theorem weighted_sq_le (w : BoundedMultiplier ν) (u : ∀ k, Lp (E k) 2 ν) :
    (w.seminorm (D.apply u))^2 ≤ D.boundSq * ∑ k ∈ D.orders, (w.seminorm (u k))^2 := by
  have htri : w.seminorm (D.apply u) ≤
      ∑ k ∈ D.orders, (D.coefficient k).bound * w.seminorm (u k) := by
    calc
      _ ≤ ∑ k ∈ D.orders, w.seminorm ((D.coefficient k).map (u k)) := by
        change ‖w.linearMap (∑ k ∈ D.orders, (D.coefficient k).map (u k))‖ ≤ _
        rw [map_sum]
        exact norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun k _ => (D.coefficient k).weighted_seminorm_le w (u k)
  have hsq := sq_le_sq₀ (apply_nonneg w.seminorm _) (Finset.sum_nonneg fun k _ =>
    mul_nonneg (D.coefficient k).bound_nonneg (apply_nonneg w.seminorm _)) |>.mpr htri
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq D.orders (fun k => (D.coefficient k).bound)
    (fun k => w.seminorm (u k))
  have hb : (∑ k ∈ D.orders, (D.coefficient k).bound^2) ≤ D.boundSq :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  exact hsq.trans (hcs.trans (mul_le_mul_of_nonneg_right hb
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)))

/-- The exact exponent arithmetic of Section 5, including lower-order terms. -/
theorem weighted_density_le (w : BoundedMultiplier ν) (u : ∀ k, Lp (E k) 2 ν)
    {q c b : ℝ} (hq : 1 ≤ q)
    (hexp : ∀ k : Fin (m+1), k.val ≤ j → c ≤ 2 * (m-k.val : ℕ) + b) :
    q^c * (w.seminorm (D.apply u))^2 ≤
      D.boundSq * ∑ k : Fin (m+1), q^(2*(m-k.val : ℕ)+b) * (w.seminorm (u k))^2 := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  calc
    _ ≤ q^c * (D.boundSq * ∑ k ∈ D.orders, (w.seminorm (u k))^2) :=
      mul_le_mul_of_nonneg_left (D.weighted_sq_le w u) (Real.rpow_nonneg hq0 c)
    _ = D.boundSq * ∑ k ∈ D.orders, q^c * (w.seminorm (u k))^2 := by
      rw [← Finset.mul_sum]; ring
    _ ≤ D.boundSq * ∑ k ∈ D.orders,
        q^(2*(m-k.val : ℕ)+b) * (w.seminorm (u k))^2 := by
      apply mul_le_mul_of_nonneg_left _ D.boundSq_nonneg
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hq (hexp k (Finset.mem_filter.mp hk).2)) (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => mul_nonneg (Real.rpow_nonneg hq0 _) (sq_nonneg _))) D.boundSq_nonneg
end DifferentialExpression

/-- c_j is bounded by every graph exponent with derivative order k <= j. -/
theorem CarlemanExponents.order_exponent_le (a : CarlemanExponents) (j : Fin a.m)
    (k : Fin (a.m+1)) (hk : k.val ≤ j.val+1) :
    a.c j ≤ 2 * (a.m-k.val : ℕ) + a.energyPower j := by
  have hd : (a.m-(j.val+1) : ℕ) ≤ a.m-k.val := Nat.sub_le_sub_left hk a.m
  have hdr : ((a.m-(j.val+1) : ℕ) : ℝ) ≤ (a.m-k.val : ℕ) := by exact_mod_cast hd
  have hm := le_max_right 0 (a.c j - 2 * (a.m-(j.val+1) : ℕ))
  change a.c j ≤ _ + max 0 _
  linarith
end Carleman
