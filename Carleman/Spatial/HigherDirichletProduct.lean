module

public import Carleman.Spatial.HigherWeakProduct
public import Carleman.Spatial.HigherDirichletSpace
public import Carleman.Spatial.DirichletWeakProduct

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman

variable {d n : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
  (a : List (Fin d) → BoundedMultiplier (volume.restrict S))
  (ha : ∀ l, ContDiffOn ℝ ∞ (a l).value S)
  (hd : ∀ l i, (a (i::l)).value =ᵐ[volume.restrict S]
    (fun x => fderiv ℝ (a l).value x (EuclideanSpace.basisFun (Fin d) ℝ i)))

theorem smoothProductCLM_test (φ : SpatialTest S) :
    WeakSobolevJet.smoothProductCLM (n := n) hS (ae_restrict_mem hS.measurableSet) a ha hd (φ.allOrderJet n)=
      (φ.mulOn hS (ha [])).allOrderJet n := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  change WeakSobolevJet.value (WeakSobolevJet.smoothProductJet hS (ae_restrict_mem hS.measurableSet) a ha hd _)=_
  rw [WeakSobolevJet.smoothProductJet_value,SpatialTest.allOrderJet_value,
    SpatialTest.allOrderJet_value,SpatialTest.mulOn_toLp]

theorem smoothProductCLM_mem_higherDirichlet
    (u : WeakSobolevJet d n (volume.restrict S) S) (hu : u ∈ higherDirichletJetSpace S n) :
    WeakSobolevJet.smoothProductCLM hS (ae_restrict_mem hS.measurableSet) a ha hd u ∈ higherDirichletJetSpace S n := by
  apply clm_mem_closed_span (WeakSobolevJet.smoothProductCLM hS (ae_restrict_mem hS.measurableSet) a ha hd)
    (Set.range (fun φ : SpatialTest S => φ.allOrderJet n)) _ u hu
  rintro _ ⟨φ,rfl⟩
  rw [smoothProductCLM_test]
  exact Submodule.subset_span (Set.mem_range_self (φ.mulOn hS (ha [])))

include hS in
theorem boundedSmooth_map_mem_sobolev
    (w : BoundedMultiplier (volume.restrict S)) (hw : BoundedSmoothOn w.value S)
    (u : Lp ℝ 2 (volume.restrict S)) (hu : u ∈ sobolevSubspace d n (volume.restrict S) S) :
    w.map u ∈ sobolevSubspace d n (volume.restrict S) S := by
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  let a := intrinsicWordMultiplier hS hν hw
  obtain ⟨v,rfl⟩ := hu
  refine ⟨WeakSobolevJet.smoothProductJet hS hν a (intrinsicWordMultiplier_smooth hS hν hw)
    (intrinsicWordMultiplier_derivative hS hν hw) v,?_⟩
  rw [WeakSobolevJet.smoothProductJet_value]
  exact intrinsicWordMultiplier_nil hS hν hw w rfl _

include hS in
theorem boundedSmooth_map_mem_higherDirichlet
    (w : BoundedMultiplier (volume.restrict S)) (hw : BoundedSmoothOn w.value S)
    (u : Lp ℝ 2 (volume.restrict S)) (hu : u ∈ higherDirichletSubspace S n) :
    w.map u ∈ higherDirichletSubspace S n := by
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  let a := intrinsicWordMultiplier hS hν hw
  obtain ⟨v,hv,rfl⟩ := hu
  refine ⟨WeakSobolevJet.smoothProductCLM hS hν a (intrinsicWordMultiplier_smooth hS hν hw)
    (intrinsicWordMultiplier_derivative hS hν hw) v,
    smoothProductCLM_mem_higherDirichlet hS a (intrinsicWordMultiplier_smooth hS hν hw)
      (intrinsicWordMultiplier_derivative hS hν hw) v hv,?_⟩
  change WeakSobolevJet.value (WeakSobolevJet.smoothProductJet hS hν a (intrinsicWordMultiplier_smooth hS hν hw)
    (intrinsicWordMultiplier_derivative hS hν hw) v)=_
  rw [WeakSobolevJet.smoothProductJet_value]
  exact intrinsicWordMultiplier_nil hS hν hw w rfl _

include hS in
theorem boundedSmooth_map_mem_higherDirichlet_domain (m : ℕ)
    (w : BoundedMultiplier (volume.restrict S)) (hw : BoundedSmoothOn w.value S)
    (u : Lp ℝ 2 (volume.restrict S))
    (hu : u ∈ sobolevSubspace d n (volume.restrict S) S ⊓ higherDirichletSubspace S m) :
    w.map u ∈ sobolevSubspace d n (volume.restrict S) S ⊓ higherDirichletSubspace S m :=
  ⟨boundedSmooth_map_mem_sobolev hS w hw u hu.1,
    boundedSmooth_map_mem_higherDirichlet hS w hw u hu.2⟩

end Carleman
