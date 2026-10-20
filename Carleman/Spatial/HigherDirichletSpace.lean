module

public import Carleman.Spatial.SpatialTestAllOrders
public import Carleman.Spatial.ConformingHilbert

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} (S : Set (SpatialCoordinates d)) (m : ℕ)

def higherDirichletJetSpace : Submodule ℝ (WeakSobolevJet d m (volume.restrict S) S) :=
  (Submodule.span ℝ (Set.range (fun φ : SpatialTest S => φ.allOrderJet m))).topologicalClosure

def higherDirichletSubspace : Submodule ℝ (Lp ℝ 2 (volume.restrict S)) :=
  (higherDirichletJetSpace S m).map WeakSobolevJet.value

theorem higherDirichletSubspace_sobolev :
    higherDirichletSubspace S m ≤ sobolevSubspace d m (volume.restrict S) S := by
  rintro _ ⟨u,_,rfl⟩
  exact ⟨u,rfl⟩

theorem test_mem_higherDirichletJetSpace (φ : SpatialTest S) :
    φ.allOrderJet m ∈ higherDirichletJetSpace S m :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self φ))

theorem test_mem_higherDirichletSubspace (φ : SpatialTest S) :
    φ.toLp (volume.restrict S) ∈ higherDirichletSubspace S m :=
  ⟨φ.allOrderJet m,test_mem_higherDirichletJetSpace S m φ,φ.allOrderJet_value m⟩

theorem higherDirichletJetSpace_eq_closure (hS : IsOpen S) :
    (higherDirichletJetSpace S m : Set (WeakSobolevJet d m (volume.restrict S) S))=
      closure (Set.range (fun φ : SpatialTest S => φ.allOrderJet m)) := by
  change closure (↑(Submodule.span ℝ (Set.range (fun φ : SpatialTest S => φ.allOrderJet m))) : Set (WeakSobolevJet d m (volume.restrict S) S))=_
  congr 1
  ext u
  constructor
  · intro hu
    induction hu using Submodule.span_induction with
    | mem u hu => exact hu
    | zero => exact ⟨SpatialTest.zeroTest,SpatialTest.zeroTest_allOrderJet hS m⟩
    | add u v _ _ hu hv =>
      obtain ⟨φ,rfl⟩ := hu
      obtain ⟨ψ,rfl⟩ := hv
      exact ⟨φ.addTest ψ,φ.addTest_allOrderJet hS ψ m⟩
    | smul c u _ hu =>
      obtain ⟨φ,rfl⟩ := hu
      exact ⟨φ.smulTest c,φ.smulTest_allOrderJet hS c m⟩
  · intro hu
    exact Submodule.subset_span hu

theorem mem_higherDirichletJetSpace_iff (hS : IsOpen S)
    (u : WeakSobolevJet d m (volume.restrict S) S) :
    u ∈ higherDirichletJetSpace S m ↔ WeakSobolevJet.value u ∈ higherDirichletSubspace S m := by
  constructor
  · intro hu
    exact ⟨u,hu,rfl⟩
  · rintro ⟨v,hv,hvu⟩
    have he := WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet) hvu
    rwa [he] at hv

theorem higherDirichletSubspace_closed (hS : IsOpen S) :
    IsClosed {u : WeakSobolevJet d m (volume.restrict S) S | WeakSobolevJet.value u ∈ higherDirichletSubspace S m} := by
  have he : {u : WeakSobolevJet d m (volume.restrict S) S | WeakSobolevJet.value u ∈ higherDirichletSubspace S m}=
      (higherDirichletJetSpace S m : Set (WeakSobolevJet d m (volume.restrict S) S)) := by
    ext u
    exact (mem_higherDirichletJetSpace_iff S m hS u).symm
  rw [he]
  exact Submodule.isClosed_topologicalClosure _

theorem higherDirichletSubspace_dense (hS : IsOpen S) :
    Dense (higherDirichletSubspace S m : Set (Lp ℝ 2 (volume.restrict S))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  apply spatial_eq_zero_of_tests hS (ae_restrict_mem hS.measurableSet)
  intro φ
  exact ((higherDirichletSubspace S m).mem_orthogonal' u).mp hu _ (test_mem_higherDirichletSubspace S m φ)

theorem higherDirichletSubspace_one (hS : IsOpen S) :
    higherDirichletSubspace S 1=dirichletSubspace S := by
  have he : higherDirichletJetSpace S 1=dirichletJetSpace S := by
    unfold higherDirichletJetSpace dirichletJetSpace
    simp only [SpatialTest.allOrderJet_one hS]
  unfold higherDirichletSubspace dirichletSubspace
  rw [he]

theorem higherDirichletEnergy_complete (hS : IsOpen S) :
    CompleteSpace (conformingHilbert (m := m) (S := S) (higherDirichletSubspace S m)) :=
  conformingHilbert_completeSpace _ (higherDirichletSubspace_closed S m hS)

end Carleman
