module

public import Carleman.Spatial.LeibnizBounds
public import Carleman.Spatial.MultiplierAlgebra

/-! Relate all symmetric coordinate components to the actual Euclidean L²
field norm, with no change of derivative convention. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d k : ℕ} {ν : Measure (SpatialCoordinates d)}

theorem derivativeComponent_multiplier (w : BoundedMultiplier ν)
    (α : Sym (Fin d) k) (u : Lp (DerivativeFiber d k) 2 ν) :
    derivativeComponent α (w.map u) = w.map (derivativeComponent α u) :=
  (OperatorMultiplier.const (EuclideanSpace.proj α)).map_weight w u

theorem derivativeField_norm_sq (u : Lp (DerivativeFiber d k) 2 ν) :
    ‖u‖^2 = ∑ α : Sym (Fin d) k, ‖derivativeComponent α u‖^2 := by
  have hi (α : Sym (Fin d) k) : Integrable (fun x => (derivativeComponent α u x)^2) ν := by
    exact (Lp.memLp (derivativeComponent α u)).integrable_sq
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ x, ∑ α : Sym (Fin d) k, (derivativeComponent α u x)^2 ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr (fun α => derivativeComponent_ae α u)] with x hx
      simp only [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq, hx]
    _ = ∑ α : Sym (Fin d) k, ∫ x, (derivativeComponent α u x)^2 ∂ν :=
      integral_finsetSum _ (fun α _ => hi α)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro α _
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem derivativeField_scaled_bound (u : Lp (DerivativeFiber d k) 2 ν)
    {r B : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B)
    (h : ∀ α, r*‖derivativeComponent α u‖ ≤ B) :
    r*‖u‖ ≤ Real.sqrt (Fintype.card (Sym (Fin d) k))*B := by
  apply (sq_le_sq₀ (mul_nonneg hr (norm_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) hB)).mp
  rw [mul_pow, derivativeField_norm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Finset.mul_sum]
  calc
    _ ≤ ∑ _α : Sym (Fin d) k, B^2 := by
      apply Finset.sum_le_sum
      intro α _
      rw [← mul_pow]
      exact (sq_le_sq₀ (mul_nonneg hr (norm_nonneg _)) hB).mpr (h α)
    _ = _ := by simp

namespace WeakSobolevJet
variable {n : ℕ} [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

theorem wordField_vector (u : WeakSobolevJet d n ν S) {k : ℕ} (hk : k ≤ n)
    (v : List.Vector (Fin d) k) :
    wordField u v.toList = derivativeComponent (Sym.ofVector v) (field ⟨k, by omega⟩ u) := by
  rcases v with ⟨l, hl⟩
  simp only [List.Vector.toList_mk]
  subst k
  rw [wordField, dite_eq_left hk]
  rfl

theorem weighted_leibnizField_bound (a : List (Fin d) → BoundedMultiplier ν)
    (outer w : BoundedMultiplier ν) {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (ha : ∀ l, l.length ≤ n → ∀ᵐ x ∂ν,
      |outer.value x*(a l).value x| ≤ C*q^l.length*|w.value x|)
    (u : WeakSobolevJet d n ν S) (l : List (Fin d)) (hl : l.length ≤ n) :
    q^(n-l.length)*outer.seminorm (leibnizField a u l) ≤
      (2:ℝ)^l.length*C*parameterNorm q w u := by
  have he : outer.map (leibnizField a u l) = leibnizField (fun j => outer.mul (a j)) u l := by
    change outer.linearMap ((derivativeSplits l).map _).sum = _
    rw [map_list_sum]
    simp only [List.map_map, leibnizField, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    exact (outer.mul_map (a p.1) (wordField u p.2)).symm
  change q^(n-l.length)*‖outer.map (leibnizField a u l)‖ ≤ _
  rw [he]
  exact leibnizField_bound _ w hq hC ha u l hl
end WeakSobolevJet
end Carleman
