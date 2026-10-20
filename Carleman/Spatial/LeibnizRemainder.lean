module

public import Carleman.Spatial.SmallParameterInterpolation

/-! Separate the unique no-weight-derivative term from the full weak Leibniz
expansion. Every remaining term strictly lowers the state derivative order. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped BigOperators ContDiff
namespace Carleman
theorem derivativeSplits_empty_left {ι : Type*} (l : List ι) :
    (derivativeSplits l).filter (fun p => p.1.isEmpty)=[([],l)] := by
  induction l with
  | nil => simp [derivativeSplits]
  | cons i l ih =>
    simp only [derivativeSplits,List.filter_append,List.filter_map]
    simp [Function.comp_def,ih]

def derivativeRemainderSplits {ι : Type*} (l : List ι) :=
  (derivativeSplits l).filter (fun p => !p.1.isEmpty)

theorem derivativeRemainderSplits_lt {ι : Type*} {l : List ι} {p : List ι × List ι}
    (hp : p ∈ derivativeRemainderSplits l) : p.2.length<l.length := by
  have hh := List.mem_filter.mp hp
  have he := derivativeSplits_lengths l p hh.1
  have hne : p.1 ≠ [] := by simpa using hh.2
  have hl := List.length_pos_iff.mpr hne
  omega

namespace WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

def leibnizRemainder (a : List (Fin d) → BoundedMultiplier ν)
    (u : WeakSobolevJet d n ν S) (l : List (Fin d)) : Lp ℝ 2 ν :=
  ((derivativeRemainderSplits l).map (fun p => (a p.1).map (wordField u p.2))).sum

theorem leibnizField_eq_principal_add (a : List (Fin d) → BoundedMultiplier ν)
    (u : WeakSobolevJet d n ν S) (l : List (Fin d)) :
    leibnizField a u l=(a []).map (wordField u l)+leibnizRemainder a u l := by
  classical
  have h := List.sum_map_filter_add_sum_map_filter_not
    (fun p : List (Fin d) × List (Fin d) => p.1.isEmpty=true)
    (fun p => (a p.1).map (wordField u p.2)) (derivativeSplits l)
  simpa only [Bool.decide_coe,decide_not,derivativeSplits_empty_left,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,leibnizField,leibnizRemainder,derivativeRemainderSplits] using h.symm

theorem lowerParameterNorm_component {q : ℝ} (hq : 0 ≤ q)
    (u : WeakSobolevJet d n ν S) (k : Fin n) :
    q^(n-k.val)*‖field k.castSucc u‖ ≤ lowerParameterNorm q u :=
  Finset.single_le_sum (f := fun j : Fin n => q^(n-j.val)*‖field j.castSucc u‖)
    (fun _ _ => mul_nonneg (pow_nonneg hq _) (norm_nonneg _)) (Finset.mem_univ k)

theorem lowerParameterNorm_le_parameterNorm {q : ℝ} (hq : 0 ≤ q)
    (u : WeakSobolevJet d n ν S) :
    lowerParameterNorm q u ≤ parameterNorm q BoundedMultiplier.one u := by
  simpa using lowerParameterNorm_rescale hq (le_refl (1 : ℝ)) u

theorem leibnizRemainder_term_bound (a : List (Fin d) → BoundedMultiplier ν)
    (outer : BoundedMultiplier ν) {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (ha : ∀ l, l.length ≤ n → ∀ᵐ x ∂ν, |outer.value x*(a l).value x| ≤ C*q^l.length)
    (u : WeakSobolevJet d n ν S) (l : List (Fin d)) (hl : l.length ≤ n)
    (p : List (Fin d) × List (Fin d)) (hp : p ∈ derivativeRemainderSplits l) :
    q^(n-l.length)*‖outer.map ((a p.1).map (wordField u p.2))‖ ≤ C*lowerParameterNorm q u := by
  have hlen := derivativeSplits_lengths l p (List.mem_filter.mp hp).1
  have hlt := derivativeRemainderSplits_lt hp
  have h1 : p.1.length ≤ n := by omega
  have h2 : p.2.length < n := by omega
  have he := (outer.mul (a p.1)).seminorm_le_of_weight_le BoundedMultiplier.one
    (C*q^p.1.length) (by simpa only [BoundedMultiplier.mul,BoundedMultiplier.one,abs_one,mul_one] using ha p.1 h1)
    (wordField u p.2)
  simp only [BoundedMultiplier.seminorm_apply,BoundedMultiplier.mul_map,BoundedMultiplier.one_map] at he
  have hw := wordField_norm_le u p.2 (by omega)
  have hb := lowerParameterNorm_component hq u ⟨p.2.length,h2⟩
  have hpow : q^(n-l.length)*q^p.1.length=q^(n-p.2.length) := by
    rw [←pow_add]
    congr 1
    omega
  calc
    _ ≤ q^(n-l.length)*(C*q^p.1.length*‖wordField u p.2‖) := mul_le_mul_of_nonneg_left he (pow_nonneg hq _)
    _ ≤ q^(n-l.length)*(C*q^p.1.length*‖field ⟨p.2.length,by omega⟩ u‖) := by gcongr
    _ = C*(q^(n-p.2.length)*‖field (Fin.castSucc ⟨p.2.length,h2⟩) u‖) := by
      change q^(n-l.length)*(C*q^p.1.length*‖field ⟨p.2.length,by omega⟩ u‖)=C*(q^(n-p.2.length)*‖field ⟨p.2.length,by omega⟩ u‖)
      rw [←hpow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hC

theorem leibnizRemainder_weighted_bound (a : List (Fin d) → BoundedMultiplier ν)
    (outer : BoundedMultiplier ν) {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (ha : ∀ l, l.length ≤ n → ∀ᵐ x ∂ν, |outer.value x*(a l).value x| ≤ C*q^l.length)
    (u : WeakSobolevJet d n ν S) (l : List (Fin d)) (hl : l.length ≤ n) :
    q^(n-l.length)*‖outer.map (leibnizRemainder a u l)‖ ≤
      (2:ℝ)^l.length*C*lowerParameterNorm q u := by
  have he : outer.map (leibnizRemainder a u l)=
      ((derivativeRemainderSplits l).map (fun p => outer.map ((a p.1).map (wordField u p.2)))).sum := by
    change outer.linearMap ((derivativeRemainderSplits l).map _).sum=_
    rw [map_list_sum,List.map_map]
    rfl
  rw [he]
  have hn := norm_list_sum_le (derivativeRemainderSplits l) (fun p => outer.map ((a p.1).map (wordField u p.2)))
  have hb := List.sum_le_sum (fun p hp => leibnizRemainder_term_bound a outer hq hC ha u l hl p hp)
  have hscale : q^(n-l.length)*
      ((derivativeRemainderSplits l).map (fun p => ‖outer.map ((a p.1).map (wordField u p.2))‖)).sum=
      ((derivativeRemainderSplits l).map (fun p => q^(n-l.length)*‖outer.map ((a p.1).map (wordField u p.2))‖)).sum := by
    rw [List.sum_map_mul_left]
  have hcount : ((derivativeRemainderSplits l).length : ℝ) ≤ (2:ℝ)^l.length := by
    exact_mod_cast (List.length_filter_le _ (derivativeSplits l)).trans_eq (derivativeSplits_length l)
  have hconst : ((derivativeRemainderSplits l).map (fun _ => C*lowerParameterNorm q u)).sum=
      (derivativeRemainderSplits l).length*(C*lowerParameterNorm q u) := by simp [nsmul_eq_mul]
  exact ((mul_le_mul_of_nonneg_left hn (pow_nonneg hq _)).trans_eq hscale).trans
    ((hb.trans_eq hconst).trans (by nlinarith [mul_le_mul_of_nonneg_right hcount (mul_nonneg hC (lowerParameterNorm_nonneg hq u))]))

variable [IsLocallyFiniteMeasure ν] (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)

include hS hν in
theorem conjugated_word_remainder_bound (a : List (Fin d) → BoundedMultiplier ν)
    (ha : ∀ l, ContDiffOn ℝ ∞ (a l).value S)
    (hd : ∀ l i, (a (i::l)).value =ᵐ[ν]
      (fun x => fderiv ℝ (a l).value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (outer : BoundedMultiplier ν) (hinv : ∀ᵐ x ∂ν, outer.value x*(a []).value x=1)
    {q C : ℝ} (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hb : ∀ l, l.length ≤ n → ∀ᵐ x ∂ν, |outer.value x*(a l).value x| ≤ C*q^l.length)
    (u v : WeakSobolevJet d n ν S) (hv : value v=(a []).map (value u))
    (l : List (Fin d)) (hl : l.length ≤ n) :
    ‖outer.map (wordField v l)-wordField u l‖ ≤ (2:ℝ)^n*C*lowerParameterNorm q u := by
  rw [wordField_mul hS hν a ha hd u v hv l hl,leibnizField_eq_principal_add,
    outer.map_add,outer.map_inverse (a []) hinv,add_sub_cancel_left]
  have hp : 1 ≤ q^(n-l.length) := one_le_pow₀ hq
  have he := leibnizRemainder_weighted_bound a outer (zero_le_one.trans hq) hC hb u l hl
  exact ((le_mul_of_one_le_left (norm_nonneg _) hp).trans he).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hl) hC) (lowerParameterNorm_nonneg (zero_le_one.trans hq) u))

end WeakSobolevJet
end Carleman
