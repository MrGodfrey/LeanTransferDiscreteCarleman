module

public import Carleman.Spatial.ComponentNorms

/-! Full-order weighted parameter norm comparison from the actual weak
Leibniz formula. The constant is fixed before the parameter and states. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

def leibnizConstant (d n : ℕ) : ℝ :=
  1 + ∑ k : Fin (n+1), Real.sqrt (Fintype.card (Sym (Fin d) k.val)) * (2:ℝ)^k.val

theorem leibnizConstant_pos : 0 < leibnizConstant d n := by
  unfold leibnizConstant
  positivity

/-- Enlarging the parameter only enlarges the actual finite spatial graph norm. -/
theorem parameterNorm_mono {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r)
    (w : BoundedMultiplier ν) (u : WeakSobolevJet d n ν S) :
    parameterNorm q w u ≤ parameterNorm r w u := by
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq hqr _) (apply_nonneg _ _)

/-- Collect all components and all derivative orders after the full product expansion. -/
theorem parameterNorm_leibniz_bound (a : List (Fin d) → BoundedMultiplier ν)
    (outer w : BoundedMultiplier ν) {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (ha : ∀ l, l.length ≤ n → ∀ᵐ x ∂ν,
      |outer.value x*(a l).value x| ≤ C*q^l.length*|w.value x|)
    (u v : WeakSobolevJet d n ν S)
    (hv : ∀ l, l.length ≤ n → wordField v l = leibnizField a u l) :
    parameterNorm q outer v ≤ leibnizConstant d n*C*parameterNorm q w u := by
  have hk (k : Fin (n+1)) : q^(n-k.val)*outer.seminorm (field k v) ≤
      Real.sqrt (Fintype.card (Sym (Fin d) k.val))*((2:ℝ)^k.val*C*parameterNorm q w u) := by
    apply derivativeField_scaled_bound (outer.map (field k v)) (pow_nonneg hq _)
      (by positivity [parameterNorm_nonneg hq w u])
    intro α
    rw [derivativeComponent_multiplier]
    have hh := weighted_leibnizField_bound a outer w hq hC ha u (coordinateVector α).toList
      (by simpa using Nat.le_of_lt_succ k.isLt)
    rw [← hv _ (by simpa using Nat.le_of_lt_succ k.isLt),
      wordField_vector v (Nat.le_of_lt_succ k.isLt), coordinateVector_represents] at hh
    simpa only [List.Vector.toList_length, BoundedMultiplier.seminorm_apply] using hh
  calc
    _ ≤ ∑ k : Fin (n+1), Real.sqrt (Fintype.card (Sym (Fin d) k.val))*
        ((2:ℝ)^k.val*C*parameterNorm q w u) := Finset.sum_le_sum fun k _ => hk k
    _ = (∑ k : Fin (n+1), Real.sqrt (Fintype.card (Sym (Fin d) k.val))*(2:ℝ)^k.val)*
        (C*parameterNorm q w u) := by rw [Finset.sum_mul]; congr 1; ext k; ring
    _ ≤ _ := by
      have hp := parameterNorm_nonneg hq w u
      dsimp [leibnizConstant]
      nlinarith

/-- N ≤ R ≤ (n+1)N for the actual finite collection of spatial L² norms. -/
theorem weightedNorm_le_parameterNorm {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u : WeakSobolevJet d n ν S) : weightedNorm q w u ≤ parameterNorm q w u := by
  apply (sq_le_sq₀ (weightedNorm_nonneg q w u) (parameterNorm_nonneg hq w u)).mp
  rw [weightedNorm_sq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => mul_nonneg (pow_nonneg hq _) (apply_nonneg _ _))

theorem parameterNorm_le_weightedNorm {q : ℝ} (hq : 0 ≤ q) (w : BoundedMultiplier ν)
    (u : WeakSobolevJet d n ν S) : parameterNorm q w u ≤ (n+1:ℝ)*weightedNorm q w u := by
  calc
    _ ≤ ∑ _k : Fin (n+1), weightedNorm q w u :=
      Finset.sum_le_sum fun k _ => weighted_component_le hq w u k
    _ = _ := by simp
end Carleman.WeakSobolevJet
