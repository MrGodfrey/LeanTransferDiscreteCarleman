module

public import Carleman.Spatial.DerivativeFieldAssembly
public import Carleman.Spatial.WeakLeibniz
public import Carleman.Spatial.WeakMixedDerivative

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
namespace WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  (a : List (Fin d) → BoundedMultiplier ν)
  (ha : ∀ l, ContDiffOn ℝ ∞ (a l).value S)
  (hd : ∀ l i, (a (i::l)).value =ᵐ[ν]
    (fun x => fderiv ℝ (a l).value x (EuclideanSpace.basisFun (Fin d) ℝ i)))

include hS hν ha hd in
theorem leibnizField_perm (u : WeakSobolevJet d n ν S) {l r : List (Fin d)}
    (hp : l.Perm r) (hl : l.length ≤ n) : leibnizField a u l=leibnizField a u r := by
  induction hp with
  | nil => rfl
  | @cons i l r hp ih =>
    have hln : l.length < n := by simp only [List.length_cons] at hl; omega
    have hrn : r.length < n := by rw [← hp.length_eq]; exact hln
    have hw := leibnizField_weak hS hν a ha hd u l i hln
    rw [ih (by omega)] at hw
    exact hw.unique hS hν (leibnizField_weak hS hν a ha hd u r i hrn)
  | swap i j l =>
    have hn : l.length+2 ≤ n := by simpa only [List.length_cons] using hl
    exact (leibnizField_weak hS hν a ha hd u l i (by omega)).mixed_commute hS hν
      (leibnizField_weak hS hν a ha hd u l j (by omega))
      (leibnizField_weak hS hν a ha hd u (i::l) j (by simp only [List.length_cons]; omega))
      (leibnizField_weak hS hν a ha hd u (j::l) i (by simp only [List.length_cons]; omega))
  | @trans l r t hp hq ih₁ ih₂ =>
    exact (ih₁ hl).trans (ih₂ (by rw [← hp.length_eq]; exact hl))

def smoothProductJet (u : WeakSobolevJet d n ν S) : WeakSobolevJet d n ν S := by
  refine ⟨fun k => derivativeFieldAssembly (fun α : Sym (Fin d) k.val =>
    leibnizField a u ((α : Multiset (Fin d)).sort (· ≤ ·))),?_⟩
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
  rw [leibnizField_perm hS hν a ha hd u hp (by rw [hp.length_eq,List.length_cons,hl]; omega)]
  exact leibnizField_weak hS hν a ha hd u _ i (by rw [hl]; exact k.isLt)

theorem smoothProductJet_value (u : WeakSobolevJet d n ν S) :
    value (smoothProductJet hS hν a ha hd u)=(a []).map (value u) := by
  change derivativeComponent (Sym.nil : Sym (Fin d) 0) (derivativeFieldAssembly
    (fun α : Sym (Fin d) 0 => leibnizField a u ((α : Multiset (Fin d)).sort (· ≤ ·))))=_
  rw [derivativeFieldAssembly_component]
  change leibnizField a u ((0 : Multiset (Fin d)).sort (· ≤ ·))=_
  rw [Multiset.sort_zero,leibnizField_nil]

omit [IsLocallyFiniteMeasure ν] in
theorem continuous_wordField (l : List (Fin d)) :
    Continuous (fun u : WeakSobolevJet d n ν S => wordField u l) := by
  by_cases hl : l.length ≤ n
  · simp only [wordField,dite_eq_left hl]
    exact (derivativeComponentCLM (wordIndex l)).continuous.comp (fieldCLM ⟨l.length,by omega⟩).continuous
  · simp only [wordField,dite_eq_right hl]
    exact continuous_const

omit [IsLocallyFiniteMeasure ν] in
theorem continuous_leibnizField (l : List (Fin d)) :
    Continuous (fun u : WeakSobolevJet d n ν S => leibnizField a u l) := by
  unfold leibnizField
  exact continuous_list_sum _ (fun p _ =>
    (a p.1).continuousLinearMap.continuous.comp (continuous_wordField p.2))

def smoothProductCLM : WeakSobolevJet d n ν S →L[ℝ] WeakSobolevJet d n ν S where
  toFun := smoothProductJet hS hν a ha hd
  map_add' u v := by
    apply value_injective hS hν
    simp only [smoothProductJet_value,map_add,BoundedMultiplier.map_add]
  map_smul' c u := by
    apply value_injective hS hν
    simp only [smoothProductJet_value,map_smul,BoundedMultiplier.map_smul,RingHom.id_apply]
  cont := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro k
    exact derivativeFieldAssembly.continuous.comp (continuous_pi fun α =>
      continuous_leibnizField a ((α : Multiset (Fin d)).sort (· ≤ ·)))

end WeakSobolevJet
end Carleman
