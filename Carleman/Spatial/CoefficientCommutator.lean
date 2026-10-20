module

public import Carleman.Spatial.CoefficientDifferentialOperator
public import Carleman.Spatial.HigherWeightedCoercivity
/-! Uniform strictly lower-order commutators for the original general
weak coefficient operator and the full allowed exponential weight family. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators
namespace Carleman
variable {d n m : ℕ} {S : Set (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict S)]
theorem list_sum_map_sub {ι E : Type*} [AddCommGroup E] (l : List ι) (f g : ι → E) :
    (l.map (fun x => f x-g x)).sum=(l.map f).sum-(l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    abel

namespace WeakSobolevJet

def coefficientTermBound (a : BoundedWeakCoefficient S n) (l : List (Fin d)) : ℝ :=
  ((derivativeSplits l).map (fun p => (a.derivative p.1).bound)).sum

omit [IsFiniteMeasure (volume.restrict S)] in
theorem coefficientTermBound_nonneg (a : BoundedWeakCoefficient S n) (l : List (Fin d)) :
    0 ≤ coefficientTermBound a l := List.sum_nonneg (by
      intro t ht
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp ht
      exact (a.derivative p.1).bound_nonneg)

set_option maxHeartbeats 1200000 in
omit [IsFiniteMeasure (volume.restrict S)] in
theorem coefficientDifferentialTerm_error_of_words
    (a : BoundedWeakCoefficient S n) (w : BoundedMultiplier (volume.restrict S))
    (u v : WeakSobolevJet d n (volume.restrict S) S)
    (l r : List (Fin d)) (hl : l.length+r.length ≤ n) {E : ℝ}
    (hb : ∀ s : List (Fin d), s.length ≤ n → ‖wordField u s-w.map (wordField v s)‖ ≤ E) :
    ‖coefficientDifferentialTerm a u l r-w.map (coefficientDifferentialTerm a v l r)‖ ≤
      coefficientTermBound a l*E := by
  have he : coefficientDifferentialTerm a u l r-w.map (coefficientDifferentialTerm a v l r)=
      ((derivativeSplits l).map (fun p => (a.derivative p.1).map
        (wordField u (p.2++r)-w.map (wordField v (p.2++r))))).sum := by
    unfold coefficientDifferentialTerm
    change _-w.linearMap ((derivativeSplits l).map _).sum=_
    rw [map_list_sum,List.map_map,←list_sum_map_sub]
    congr 1
    apply List.map_congr_left
    intro p hp
    rw [show (a.derivative p.1).map (wordField u (p.2++r)-w.map (wordField v (p.2++r)))=
      (a.derivative p.1).map (wordField u (p.2++r))-(a.derivative p.1).map (w.map (wordField v (p.2++r))) from
        (a.derivative p.1).linearMap.map_sub _ _]
    exact congrArg (fun x => (a.derivative p.1).map (wordField u (p.2++r))-x)
      (w.map_map_comm (a.derivative p.1) _).symm
  rw [he]
  have hn := norm_list_sum_le (derivativeSplits l) (fun p => (a.derivative p.1).map
    (wordField u (p.2++r)-w.map (wordField v (p.2++r))))
  have ht : ((derivativeSplits l).map (fun p => ‖(a.derivative p.1).map
      (wordField u (p.2++r)-w.map (wordField v (p.2++r)))‖)).sum ≤
      ((derivativeSplits l).map (fun p => (a.derivative p.1).bound*E)).sum :=
    List.sum_le_sum (fun p hp => calc
    ‖(a.derivative p.1).map (wordField u (p.2++r)-w.map (wordField v (p.2++r)))‖ ≤
      (a.derivative p.1).bound*‖wordField u (p.2++r)-w.map (wordField v (p.2++r))‖ :=
        (a.derivative p.1).seminorm_le _
    _ ≤ (a.derivative p.1).bound*E := mul_le_mul_of_nonneg_left (hb _ (by
      have hlen := derivativeSplits_lengths l p hp
      simp only [List.length_append]
      omega)) (a.derivative p.1).bound_nonneg)
  exact (hn.trans ht).trans_eq (by rw [List.sum_map_mul_right]; rfl)
end WeakSobolevJet
omit [IsFiniteMeasure (volume.restrict S)] in
def coefficientOperatorBound
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m)) : ℝ :=
  ∑ α, ∑ β, WeakSobolevJet.coefficientTermBound (a α β) (coordinateVector α.2).toList

omit [IsFiniteMeasure (volume.restrict S)] in
theorem coefficientOperatorBound_nonneg
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m)) :
    0 ≤ coefficientOperatorBound a := Finset.sum_nonneg fun α _ =>
      Finset.sum_nonneg fun β _ => WeakSobolevJet.coefficientTermBound_nonneg (a α β) (coordinateVector α.2).toList

set_option maxHeartbeats 6000000 in
omit [IsFiniteMeasure (volume.restrict S)] in
theorem coefficientDifferentialOperator_error_of_words
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (w : BoundedMultiplier (volume.restrict S))
    (u v : WeakSobolevJet d (2*m) (volume.restrict S) S) {E : ℝ}
    (hb : ∀ l : List (Fin d), l.length ≤ 2*m →
      ‖WeakSobolevJet.wordField u l-w.map (WeakSobolevJet.wordField v l)‖ ≤ E) :
    ‖coefficientDifferentialOperator a u-w.map (coefficientDifferentialOperator a v)‖ ≤
      coefficientOperatorBound a*E := by
  let T := fun α β => WeakSobolevJet.coefficientDifferentialTerm (a α β) u
    (coordinateVector α.2).toList (coordinateVector β.2).toList-
      w.map (WeakSobolevJet.coefficientDifferentialTerm (a α β) v
        (coordinateVector α.2).toList (coordinateVector β.2).toList)
  have he : coefficientDifferentialOperator a u-w.map (coefficientDifferentialOperator a v)=
      ∑ α : MultiDerivativeIndex d m, ∑ β : MultiDerivativeIndex d m, (-1:ℝ)^α.1.val • T α β := by
    unfold coefficientDifferentialOperator
    change _-w.linearMap (∑ α, ∑ β, _)=_
    simp only [map_sum,map_smul,T,smul_sub,Finset.sum_sub_distrib]
    rfl
  rw [he]
  calc
    _ ≤ ∑ α : MultiDerivativeIndex d m, ∑ β : MultiDerivativeIndex d m, ‖T α β‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
      simpa only [norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul] using
        norm_sum_le (Finset.univ : Finset (MultiDerivativeIndex d m)) (fun β => (-1:ℝ)^α.1.val • T α β)
    _ ≤ ∑ α : MultiDerivativeIndex d m, ∑ β : MultiDerivativeIndex d m,
        WeakSobolevJet.coefficientTermBound (a α β) (coordinateVector α.2).toList*E := by
      apply Finset.sum_le_sum
      intro α _
      apply Finset.sum_le_sum
      intro β _
      exact WeakSobolevJet.coefficientDifferentialTerm_error_of_words (a α β) w u v _ _
        (by simp only [List.Vector.toList_length]; omega) hb
    _ = coefficientOperatorBound a*E := by simp only [coefficientOperatorBound,Finset.sum_mul]

set_option maxHeartbeats 6000000 in
omit [IsFiniteMeasure (volume.restrict S)] in
theorem coefficientDifferentialOperator_smooth_commutator (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (w ξ : BoundedMultiplier (volume.restrict S)) (hξ : BoundedSmoothOn ξ.value S)
    (hinv : ∀ᵐ x ∂volume.restrict S, w.value x*ξ.value x=1)
    {q C : ℝ} (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hb : ∀ l : List (Fin d), l.length ≤ 2*m → ∀ᵐ x ∂volume.restrict S,
      |w.value x*wordDerivative l ξ.value x| ≤ C*q^l.length)
    (u v : WeakSobolevJet d (2*m) (volume.restrict S) S)
    (hv : WeakSobolevJet.value v=ξ.map (WeakSobolevJet.value u)) :
    ‖coefficientDifferentialOperator a u-w.map (coefficientDifferentialOperator a v)‖ ≤
      coefficientOperatorBound a*((2:ℝ)^(2*m)*C*WeakSobolevJet.lowerParameterNorm q u) := by
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  have hi : ∀ᵐ x ∂volume.restrict S, w.value x*(intrinsicWordMultiplier hS hν hξ []).value x=1 := by
    simpa only [intrinsicWordMultiplier,wordDerivative_nil] using hinv
  have hv' : WeakSobolevJet.value v=(intrinsicWordMultiplier hS hν hξ []).map (WeakSobolevJet.value u) := by
    rw [intrinsicWordMultiplier_nil hS hν hξ ξ rfl]
    exact hv
  apply coefficientDifferentialOperator_error_of_words a w u v
  intro l hl
  rw [norm_sub_rev]
  exact WeakSobolevJet.conjugated_word_remainder_bound hS hν
    (intrinsicWordMultiplier hS hν hξ) (intrinsicWordMultiplier_smooth hS hν hξ)
    (intrinsicWordMultiplier_derivative hS hν hξ) w hi hq hC hb u v hv' l hl

set_option maxHeartbeats 6000000 in
omit [IsFiniteMeasure (volume.restrict S)] in
theorem coefficientDifferentialOperator_allowed_commutator (hS : IsOpen S)
    {ρ : SpatialCoordinates d → ℝ} (hρ : BoundedSmoothOn ρ S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m)) :
    ∃ C > (0:ℝ), ∀ q : ℝ, 1 ≤ q → ∀ τ eta : ℝ, |eta|=1 →
      ∀ w : BoundedMultiplier (volume.restrict S),
        w.value=(fun x => q^τ*Real.exp (q*(eta*ρ x))) →
      ∀ u v : WeakSobolevJet d (2*m) (volume.restrict S) S,
        WeakSobolevJet.value u=w.map (WeakSobolevJet.value v) →
        ‖coefficientDifferentialOperator a u-w.map (coefficientDifferentialOperator a v)‖ ≤
          C*WeakSobolevJet.lowerParameterNorm q u := by
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  obtain ⟨J,hJ,hweights⟩ := allowedWeight_inverse_relative_uniform hS hν hρ (2*m)
  have hB := coefficientOperatorBound_nonneg a
  refine ⟨(1+coefficientOperatorBound a)*((2:ℝ)^(2*m)*J),by positivity,?_⟩
  intro q hq τ eta heta w hw u v hu
  obtain ⟨_,ξ,hξ,hi,_,hbξ⟩ := hweights q hq τ eta heta w hw
  have hi' : ∀ᵐ x ∂volume.restrict S, ξ.value x*w.value x=1 := hi.mono fun x hx => by rw [mul_comm]; exact hx
  have hv : WeakSobolevJet.value v=ξ.map (WeakSobolevJet.value u) := by
    rw [hu]
    exact (ξ.map_inverse w hi' _).symm
  have hh := coefficientDifferentialOperator_smooth_commutator hS a w ξ hξ hi hq hJ.le hbξ u v hv
  calc
    _ ≤ coefficientOperatorBound a*((2:ℝ)^(2*m)*J*WeakSobolevJet.lowerParameterNorm q u) := hh
    _ ≤ (1+coefficientOperatorBound a)*((2:ℝ)^(2*m)*J*WeakSobolevJet.lowerParameterNorm q u) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by positivity)
        (WeakSobolevJet.lowerParameterNorm_nonneg (zero_le_one.trans hq) u))
    _ = _ := by ring

theorem higherCoefficient_operator_multiplier_preserves (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (hsym : ∀ α β, ((a α β).derivative []).value =ᵐ[volume.restrict S] ((a β α).derivative []).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m (fun α β => (a α β).derivative []) v v)
    (hreg : (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain ≤
      sobolevSubspace d (2*m) (volume.restrict S) S)
    (w : BoundedMultiplier (volume.restrict S)) (hw : BoundedSmoothOn w.value S)
    (z : (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain) :
    w.map (z : Lp ℝ 2 (volume.restrict S)) ∈
      (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain := by
  apply (higherCoefficient_operator_domain_eq hS a hsym hcoer hreg).ge
  exact ⟨boundedSmooth_map_mem_higherDirichlet hS w hw z.val
    ((higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).domain_le z.property),
    boundedSmooth_map_mem_sobolev hS w hw z.val (hreg z.property)⟩

set_option maxHeartbeats 6000000 in
theorem higherCoefficient_allowed_commutator (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
    {ρ : SpatialCoordinates d → ℝ} (hρ : SmoothOnClosure ρ S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedWeakCoefficient S (2*m))
    (hsym : ∀ α β, ((a α β).derivative []).value =ᵐ[volume.restrict S] ((a β α).derivative []).value)
    (hcoer : ∃ c > (0:ℝ), ∀ v : HigherDirichletEnergy S m,
      c*‖v‖*‖v‖ ≤ higherCoefficientForm S m (fun α β => (a α β).derivative []) v v)
    (hreg : (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain ≤
      sobolevSubspace d (2*m) (volume.restrict S) S) :
    ∃ C > (0:ℝ), ∀ q : ℝ, 1 ≤ q → ∀ τ eta : ℝ, |eta|=1 →
      ∀ w : BoundedMultiplier (volume.restrict S),
        w.value=(fun x => q^τ*Real.exp (q*(eta*ρ x))) →
      (∀ z : (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain,
        w.map (z : Lp ℝ 2 (volume.restrict S)) ∈
          (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain) ∧
      ∀ z v : (higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.domain,
        (z : Lp ℝ 2 (volume.restrict S))=w.map (v : Lp ℝ 2 (volume.restrict S)) →
        ‖(higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.operator z-
          w.map ((higherCoefficientOriginalForm hS (fun α β => (a α β).derivative []) hsym hcoer).model.operator v)‖ ≤
          C*WeakSobolevJet.lowerParameterNorm q
            (domainSobolevJet hS (ae_restrict_mem hS.measurableSet) hreg z) := by
  have hρb := hρ.boundedSmoothOn hbounded
  obtain ⟨C,hC,hbound⟩ := coefficientDifferentialOperator_allowed_commutator hS hρb a
  refine ⟨C,hC,?_⟩
  intro q hq τ eta heta w hw
  have hwS : BoundedSmoothOn w.value S := by rw [hw]; exact hρb.allowedWeight hS hq τ eta heta
  refine ⟨higherCoefficient_operator_multiplier_preserves hS a hsym hcoer hreg w hwS,?_⟩
  intro z v hz
  rw [higherCoefficient_operator_canonical hS a hsym hcoer hreg z,
    higherCoefficient_operator_canonical hS a hsym hcoer hreg v]
  apply hbound q hq τ eta heta w hw
  simpa only [domainSobolevJet_value] using hz

end Carleman
