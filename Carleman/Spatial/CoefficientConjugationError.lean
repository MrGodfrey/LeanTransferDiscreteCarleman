module

public import Carleman.Spatial.LeibnizRemainder
public import Carleman.Spatial.CoefficientJetForm
public import Carleman.Spatial.IntrinsicMultipliers

/-! The actual conjugated coefficient form differs from the original form
by lower-order weak derivative terms; coefficient smoothness is not needed. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped BigOperators ContDiff
namespace Carleman

variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

theorem jetScalarComponent_parameter_le {q : ℝ} (hq : 1 ≤ q)
    (u : WeakSobolevJet d n ν S) (α : MultiDerivativeIndex d n) :
    ‖jetScalarComponent α u‖ ≤ WeakSobolevJet.parameterNorm q BoundedMultiplier.one u := by
  have he := jetScalarComponent_weighted_le hq BoundedMultiplier.one u α
  simp only [BoundedMultiplier.one_seminorm] at he
  exact he.trans (WeakSobolevJet.weightedNorm_le_parameterNorm (zero_le_one.trans hq) _ _)

theorem coefficientJetForm_inverse_pairing
    (a : MultiDerivativeIndex d n → MultiDerivativeIndex d n → BoundedMultiplier ν)
    (w ξ : BoundedMultiplier ν) (hinv : ∀ᵐ x ∂ν, w.value x*ξ.value x=1)
    (v z : WeakSobolevJet d n ν S) :
    coefficientJetForm a v z=∑ α, ∑ β,
      inner ℝ ((a α β).map (w.map (jetScalarComponent β v))) (ξ.map (jetScalarComponent α z)) := by
  rw [coefficientJetForm_apply]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [w.map_map_comm (a α β),w.inner_inverse ξ hinv]

theorem coefficientJetForm_error_of_components
    (a : MultiDerivativeIndex d n → MultiDerivativeIndex d n → BoundedMultiplier ν)
    (w ξ : BoundedMultiplier ν) (hinv : ∀ᵐ x ∂ν, w.value x*ξ.value x=1)
    {q K : ℝ} (hq : 1 ≤ q) (hK : 0 ≤ K)
    (u v z : WeakSobolevJet d n ν S)
    (hv : ∀ α, ‖w.map (jetScalarComponent α v)-jetScalarComponent α u‖ ≤
      K*WeakSobolevJet.lowerParameterNorm q u)
    (hz : ∀ α, ‖ξ.map (jetScalarComponent α z)-jetScalarComponent α u‖ ≤
      K*WeakSobolevJet.lowerParameterNorm q u) :
    |coefficientJetForm a v z-coefficientJetForm a u u| ≤
      (∑ α, ∑ β, (a α β).bound)*K*(K+2)*WeakSobolevJet.lowerParameterNorm q u*
        WeakSobolevJet.parameterNorm q BoundedMultiplier.one u := by
  let L := WeakSobolevJet.lowerParameterNorm q u
  let R := WeakSobolevJet.parameterNorm q BoundedMultiplier.one u
  have hL : 0 ≤ L := WeakSobolevJet.lowerParameterNorm_nonneg (zero_le_one.trans hq) u
  have hR : 0 ≤ R := WeakSobolevJet.parameterNorm_nonneg (zero_le_one.trans hq) _ u
  have hLR : L ≤ R := WeakSobolevJet.lowerParameterNorm_le_parameterNorm (zero_le_one.trans hq) u
  have hcomp (α) : ‖jetScalarComponent α u‖ ≤ R := jetScalarComponent_parameter_le hq u α
  have hweighted (α) : ‖ξ.map (jetScalarComponent α z)‖ ≤ (K+1)*R := by
    have he := norm_sub_norm_le (ξ.map (jetScalarComponent α z)) (jetScalarComponent α u)
    nlinarith [hz α,hcomp α,mul_le_mul_of_nonneg_left hLR hK]
  have hterm (α β) :
      |inner ℝ ((a α β).map (w.map (jetScalarComponent β v))) (ξ.map (jetScalarComponent α z))-
        inner ℝ ((a α β).map (jetScalarComponent β u)) (jetScalarComponent α u)| ≤
        (a α β).bound*K*(K+2)*L*R := by
    let x := w.map (jetScalarComponent β v)
    let y := ξ.map (jetScalarComponent α z)
    let p := jetScalarComponent β u
    let t := jetScalarComponent α u
    have hsub : (a α β).map (x-p)=(a α β).map x-(a α β).map p := (a α β).linearMap.map_sub x p
    have hA : ‖(a α β).map (x-p)‖ ≤ (a α β).bound*K*L := by
      calc
        _ ≤ (a α β).bound*‖x-p‖ := (a α β).seminorm_le _
        _ ≤ (a α β).bound*(K*L) := mul_le_mul_of_nonneg_left (hv β) (a α β).bound_nonneg
        _ = _ := by ring
    have hB : ‖(a α β).map p‖ ≤ (a α β).bound*R :=
      ((a α β).seminorm_le _).trans (mul_le_mul_of_nonneg_left (hcomp β) (a α β).bound_nonneg)
    change |inner ℝ ((a α β).map x) y-inner ℝ ((a α β).map p) t| ≤ _
    calc
      _ = |inner ℝ ((a α β).map (x-p)) y+inner ℝ ((a α β).map p) (y-t)| := by
        rw [hsub,inner_sub_left,inner_sub_right]
        congr 1
        ring
      _ ≤ |inner ℝ ((a α β).map (x-p)) y|+|inner ℝ ((a α β).map p) (y-t)| := abs_add_le _ _
      _ ≤ ‖(a α β).map (x-p)‖*‖y‖+‖(a α β).map p‖*‖y-t‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
      _ ≤ ((a α β).bound*K*L)*((K+1)*R)+((a α β).bound*R)*(K*L) :=
        add_le_add (mul_le_mul hA (hweighted α) (norm_nonneg _) (by positivity [(a α β).bound_nonneg]))
          (mul_le_mul hB (hz α) (norm_nonneg _) (mul_nonneg (a α β).bound_nonneg hR))
      _ = _ := by ring
  rw [coefficientJetForm_inverse_pairing a w ξ hinv,coefficientJetForm_apply]
  simp only [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ α, ∑ β, |inner ℝ ((a α β).map (w.map (jetScalarComponent β v))) (ξ.map (jetScalarComponent α z))-
        inner ℝ ((a α β).map (jetScalarComponent β u)) (jetScalarComponent α u)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ α, ∑ β, (a α β).bound*K*(K+2)*L*R :=
      Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hterm α β
    _ = _ := by simp only [Finset.sum_mul]; rfl

variable [IsLocallyFiniteMeasure ν] (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)

include hS hν in
theorem intrinsic_conjugated_component_remainder_bound
    (w outer : BoundedMultiplier ν) (hw : BoundedSmoothOn w.value S)
    (hinv : ∀ᵐ x ∂ν, outer.value x*w.value x=1)
    {q C : ℝ} (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hb : ∀ l : List (Fin d), l.length ≤ n → ∀ᵐ x ∂ν,
      |outer.value x*wordDerivative l w.value x| ≤ C*q^l.length)
    (u v : WeakSobolevJet d n ν S) (hv : WeakSobolevJet.value v=w.map (WeakSobolevJet.value u))
    (α : MultiDerivativeIndex d n) :
    ‖outer.map (jetScalarComponent α v)-jetScalarComponent α u‖ ≤
      (2:ℝ)^n*C*WeakSobolevJet.lowerParameterNorm q u := by
  have hinv' : ∀ᵐ x ∂ν, outer.value x*(intrinsicWordMultiplier hS hν hw []).value x=1 := by
    simpa only [intrinsicWordMultiplier,wordDerivative_nil] using hinv
  have hv' : WeakSobolevJet.value v=(intrinsicWordMultiplier hS hν hw []).map (WeakSobolevJet.value u) := by
    rw [intrinsicWordMultiplier_nil hS hν hw w rfl]
    exact hv
  have hh := WeakSobolevJet.conjugated_word_remainder_bound hS hν
    (intrinsicWordMultiplier hS hν hw) (intrinsicWordMultiplier_smooth hS hν hw)
    (intrinsicWordMultiplier_derivative hS hν hw) outer hinv' hq hC hb u v hv'
    (coordinateVector α.2).toList (by simpa only [List.Vector.toList_length] using Nat.le_of_lt_succ α.1.isLt)
  rw [WeakSobolevJet.wordField_vector v (Nat.le_of_lt_succ α.1.isLt),coordinateVector_represents,
    WeakSobolevJet.wordField_vector u (Nat.le_of_lt_succ α.1.isLt),coordinateVector_represents] at hh
  exact hh

include hS hν in
theorem coefficientJetForm_smooth_conjugation_error
    (a : MultiDerivativeIndex d n → MultiDerivativeIndex d n → BoundedMultiplier ν)
    (w ξ : BoundedMultiplier ν) (hw : BoundedSmoothOn w.value S) (hξ : BoundedSmoothOn ξ.value S)
    (hinv : ∀ᵐ x ∂ν, w.value x*ξ.value x=1)
    {q C : ℝ} (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hbw : ∀ l : List (Fin d), l.length ≤ n → ∀ᵐ x ∂ν,
      |ξ.value x*wordDerivative l w.value x| ≤ C*q^l.length)
    (hbξ : ∀ l : List (Fin d), l.length ≤ n → ∀ᵐ x ∂ν,
      |w.value x*wordDerivative l ξ.value x| ≤ C*q^l.length)
    (u v z : WeakSobolevJet d n ν S)
    (hv : WeakSobolevJet.value v=ξ.map (WeakSobolevJet.value u))
    (hz : WeakSobolevJet.value z=w.map (WeakSobolevJet.value u)) :
    |coefficientJetForm a v z-coefficientJetForm a u u| ≤
      (∑ α, ∑ β, (a α β).bound)*((2:ℝ)^n*C)*((2:ℝ)^n*C+2)*
        WeakSobolevJet.lowerParameterNorm q u*WeakSobolevJet.parameterNorm q BoundedMultiplier.one u := by
  apply coefficientJetForm_error_of_components a w ξ hinv hq (mul_nonneg (by positivity) hC) u v z
  · exact intrinsic_conjugated_component_remainder_bound hS hν ξ w hξ hinv hq hC hbξ u v hv
  · have hi : ∀ᵐ x ∂ν, ξ.value x*w.value x=1 := hinv.mono fun x hx => by rw [mul_comm]; exact hx
    exact intrinsic_conjugated_component_remainder_bound hS hν w ξ hw hi hq hC hbw u z hz

end Carleman
