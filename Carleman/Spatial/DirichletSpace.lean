module

public import Carleman.Spatial.SpatialTestSobolev
public import Carleman.Spatial.SobolevTopology
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! H¹₀ is defined by the closure of genuine compactly supported smooth
functions in the weak H¹ graph norm. Its scalar realization is dense in L²
and closed in H¹; no pointwise boundary characterization is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} (S : Set (SpatialCoordinates d))

def dirichletJetSpace : Submodule ℝ (WeakSobolevJet d 1 (volume.restrict S) S) :=
  (Submodule.span ℝ (Set.range (fun φ : SpatialTest S => φ.sobolevJet))).topologicalClosure

def dirichletSubspace : Submodule ℝ (Lp ℝ 2 (volume.restrict S)) :=
  (dirichletJetSpace S).map WeakSobolevJet.value

theorem dirichletSubspace_sobolev : dirichletSubspace S ≤ sobolevSubspace d 1 (volume.restrict S) S := by
  rintro _ ⟨u,_,rfl⟩
  exact ⟨u,rfl⟩

theorem test_mem_dirichletJetSpace (φ : SpatialTest S) : φ.sobolevJet ∈ dirichletJetSpace S :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self φ))

theorem test_mem_dirichletSubspace (φ : SpatialTest S) : φ.toLp (volume.restrict S) ∈ dirichletSubspace S :=
  ⟨φ.sobolevJet,test_mem_dirichletJetSpace S φ,φ.sobolevJet_value⟩

theorem mem_dirichletJetSpace_iff (hS : IsOpen S) (u : WeakSobolevJet d 1 (volume.restrict S) S) :
    u ∈ dirichletJetSpace S ↔ WeakSobolevJet.value u ∈ dirichletSubspace S := by
  constructor
  · intro hu
    exact ⟨u,hu,rfl⟩
  · rintro ⟨v,hv,hvu⟩
    have he := WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet) hvu
    rwa [he] at hv

theorem dirichletSubspace_closed (hS : IsOpen S) :
    IsClosed {u : WeakSobolevJet d 1 (volume.restrict S) S | WeakSobolevJet.value u ∈ dirichletSubspace S} := by
  have he : {u : WeakSobolevJet d 1 (volume.restrict S) S | WeakSobolevJet.value u ∈ dirichletSubspace S} =
      (dirichletJetSpace S : Set (WeakSobolevJet d 1 (volume.restrict S) S)) := by
    ext u
    exact (mem_dirichletJetSpace_iff S hS u).symm
  rw [he]
  exact Submodule.isClosed_topologicalClosure _

theorem dirichletSubspace_dense (hS : IsOpen S) :
    Dense (dirichletSubspace S : Set (Lp ℝ 2 (volume.restrict S))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  apply spatial_eq_zero_of_tests hS (ae_restrict_mem hS.measurableSet)
  intro φ
  exact ((dirichletSubspace S).mem_orthogonal' u).mp hu _ (test_mem_dirichletSubspace S φ)

end Carleman
