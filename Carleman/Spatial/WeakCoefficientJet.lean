module

public import Carleman.Spatial.WeakCoefficientProduct
public import Carleman.Spatial.HigherWeakProduct
/-! Full finite-order Leibniz multiplication for actual bounded weak
coefficients, with all original weak Sobolev fields constructed internally. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace Carleman

/-- Actual bounded distributional derivatives through the specified finite order.
Entries beyond that order are immaterial and carry no derivative requirement. -/
structure BoundedWeakCoefficient {d : ℕ} (S : Set (SpatialCoordinates d)) (n : ℕ) where
  derivative : List (Fin d) → BoundedMultiplier (volume.restrict S)
  weak_derivative : ∀ l i, l.length < n → IsWeakMultiplierDerivative S
    (EuclideanSpace.basisFun (Fin d) ℝ i) (derivative l) (derivative (i::l))

namespace BoundedWeakCoefficient
variable {d n k : ℕ} {S : Set (SpatialCoordinates d)}

def truncate (hkn : k ≤ n) (a : BoundedWeakCoefficient S n) : BoundedWeakCoefficient S k where
  derivative := a.derivative
  weak_derivative l i hl := a.weak_derivative l i (lt_of_lt_of_le hl hkn)
end BoundedWeakCoefficient

namespace WeakSobolevJet
variable {d n : ℕ} {S : Set (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict S)] (hS : IsOpen S) (a : BoundedWeakCoefficient S n)

include hS in
theorem weakCoefficient_leibnizField_weak
    (u : WeakSobolevJet d n (volume.restrict S) S) (l : List (Fin d)) (i : Fin d) (hl : l.length < n) :
    IsWeakSpatialDerivative (volume.restrict S) S (EuclideanSpace.basisFun (Fin d) ℝ i)
      (leibnizField a.derivative u l) (leibnizField a.derivative u (i::l)) := by
  have hh := IsWeakSpatialDerivative.list_sum (derivativeSplits l)
    (fun p => (a.derivative p.1).map (wordField u p.2))
    (fun p => (a.derivative p.1).map (wordField u (i::p.2)) + (a.derivative (i::p.1)).map (wordField u p.2)) (by
      intro p hp
      have hlen := derivativeSplits_lengths l p hp
      exact (wordField_weak u p.2 i (by omega)).mul_weakCoefficient hS (a.derivative p.1) (a.derivative (i::p.1))
        (a.weak_derivative p.1 i (by omega)))
  change IsWeakSpatialDerivative (volume.restrict S) S _ (leibnizField a.derivative u l) _ at hh
  convert hh using 1
  simp only [leibnizField,derivativeSplits,List.map_append,List.map_map,List.sum_append,List.sum_map_add]
  exact add_comm _ _

include hS in
theorem weakCoefficient_wordField_mul
    (u v : WeakSobolevJet d n (volume.restrict S) S)
    (hv : value v=(a.derivative []).map (value u)) (l : List (Fin d)) (hl : l.length ≤ n) :
    wordField v l=leibnizField a.derivative u l := by
  induction l with
  | nil => simpa only [wordField_nil,leibnizField_nil] using hv
  | cons i l ih =>
    have hlen : l.length < n := by simp only [List.length_cons] at hl; omega
    have he := ih (by omega)
    have hw := wordField_weak v l i hlen
    rw [he] at hw
    exact hw.unique hS (ae_restrict_mem hS.measurableSet)
      (weakCoefficient_leibnizField_weak hS a u l i hlen)

include hS in
theorem weakCoefficient_leibnizField_perm (u : WeakSobolevJet d n (volume.restrict S) S)
    {l r : List (Fin d)} (hp : l.Perm r) (hl : l.length ≤ n) :
    leibnizField a.derivative u l=leibnizField a.derivative u r := by
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  induction hp with
  | nil => rfl
  | @cons i l r hp ih =>
    have hln : l.length < n := by simp only [List.length_cons] at hl; omega
    have hrn : r.length < n := by rw [←hp.length_eq]; exact hln
    have hw := weakCoefficient_leibnizField_weak hS a u l i hln
    rw [ih (by omega)] at hw
    exact hw.unique hS hν (weakCoefficient_leibnizField_weak hS a u r i hrn)
  | swap i j l =>
    have hn : l.length+2 ≤ n := by simpa only [List.length_cons] using hl
    exact (weakCoefficient_leibnizField_weak hS a u l i (by omega)).mixed_commute hS hν
      (weakCoefficient_leibnizField_weak hS a u l j (by omega))
      (weakCoefficient_leibnizField_weak hS a u (i::l) j (by simp only [List.length_cons]; omega))
      (weakCoefficient_leibnizField_weak hS a u (j::l) i (by simp only [List.length_cons]; omega))
  | @trans l r t hp hq ih₁ ih₂ =>
    exact (ih₁ hl).trans (ih₂ (by rw [←hp.length_eq]; exact hl))

def weakCoefficientProductJet (u : WeakSobolevJet d n (volume.restrict S) S) :
    WeakSobolevJet d n (volume.restrict S) S := by
  refine ⟨fun k => derivativeFieldAssembly (fun α : Sym (Fin d) k.val =>
    leibnizField a.derivative u ((α : Multiset (Fin d)).sort (· ≤ ·))),?_⟩
  intro k α i
  dsimp only
  rw [derivativeFieldAssembly_component,derivativeFieldAssembly_component]
  have hp : ((↑(Sym.cons i α) : Multiset (Fin d)).sort (· ≤ ·)).Perm
      (i::(α : Multiset (Fin d)).sort (· ≤ ·)) := by
    apply Multiset.coe_eq_coe.mp
    rw [Multiset.sort_eq]
    change i ::ₘ (α : Multiset (Fin d))=i ::ₘ ((α : Multiset (Fin d)).sort (· ≤ ·) : List (Fin d))
    rw [Multiset.sort_eq]
  have hl : ((α : Multiset (Fin d)).sort (· ≤ ·)).length=k.val := by
    rw [Multiset.length_sort,Sym.card_coe]
  rw [weakCoefficient_leibnizField_perm hS a u hp (by rw [hp.length_eq,List.length_cons,hl]; omega)]
  exact weakCoefficient_leibnizField_weak hS a u _ i (by rw [hl]; exact k.isLt)

theorem weakCoefficientProductJet_value (u : WeakSobolevJet d n (volume.restrict S) S) :
    value (weakCoefficientProductJet hS a u)=(a.derivative []).map (value u) := by
  change derivativeComponent (Sym.nil : Sym (Fin d) 0) (derivativeFieldAssembly
    (fun α : Sym (Fin d) 0 => leibnizField a.derivative u ((α : Multiset (Fin d)).sort (· ≤ ·))))=_
  rw [derivativeFieldAssembly_component]
  change leibnizField a.derivative u ((0 : Multiset (Fin d)).sort (· ≤ ·))=_
  rw [Multiset.sort_zero,leibnizField_nil]

def weakCoefficientProductCLM :
    WeakSobolevJet d n (volume.restrict S) S →L[ℝ] WeakSobolevJet d n (volume.restrict S) S where
  toFun := weakCoefficientProductJet hS a
  map_add' u v := by
    apply value_injective hS (ae_restrict_mem hS.measurableSet)
    simp only [weakCoefficientProductJet_value,map_add,BoundedMultiplier.map_add]
  map_smul' c u := by
    apply value_injective hS (ae_restrict_mem hS.measurableSet)
    simp only [weakCoefficientProductJet_value,map_smul,BoundedMultiplier.map_smul,RingHom.id_apply]
  cont := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro k
    exact derivativeFieldAssembly.continuous.comp (continuous_pi fun α =>
      continuous_leibnizField a.derivative ((α : Multiset (Fin d)).sort (· ≤ ·)))

theorem weakCoefficientProductJet_word (u : WeakSobolevJet d n (volume.restrict S) S)
    (l : List (Fin d)) (hl : l.length ≤ n) :
    wordField (weakCoefficientProductJet hS a u) l=leibnizField a.derivative u l :=
  weakCoefficient_wordField_mul hS a u _ (weakCoefficientProductJet_value hS a u) l hl
end WeakSobolevJet
end Carleman
