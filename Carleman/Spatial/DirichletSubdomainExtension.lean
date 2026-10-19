module

public import Carleman.Spatial.DirichletExtensionContinuity

/-! Zero extension from a smaller open domain preserves the original
H¹₀ space of a larger domain. This uses the true smooth-test closure. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}
namespace WeakSobolevJet

def extendDirichlet (S : Set (SpatialCoordinates d)) (hT : IsOpen T)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (hu : u ∈ dirichletJetSpace T) :
    WeakSobolevJet d 1 (volume.restrict S) S :=
  restrictDomain S (zeroExtendDirichlet hT u hu)

theorem extendDirichlet_value (hT : IsOpen T)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (hu : u ∈ dirichletJetSpace T) :
    value (extendDirichlet S hT u hu) =
      Physical.restrictRegionLp S (zeroExtendLp hT.measurableSet (value u)) := by
  rw [extendDirichlet,restrictDomain_value,zeroExtendDirichlet_value]

theorem extendDirichlet_field_norm_le (hT : IsOpen T)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (hu : u ∈ dirichletJetSpace T) (k : Fin 2) :
    ‖field k (extendDirichlet S hT u hu)‖ ≤ ‖field k u‖ := by
  exact (Physical.restrictRegionLp_norm_le S _).trans_eq
    (zeroExtendDirichlet_field_norm hT u hu k)

theorem extendDirichlet_test (hS : IsOpen S) (hT : IsOpen T) (hTS : T ⊆ S) (φ : SpatialTest T) :
    extendDirichlet S hT φ.sobolevJet (test_mem_dirichletJetSpace T φ) =
      (⟨φ.value,φ.smooth,φ.compact,φ.support.trans hTS⟩ : SpatialTest S).sobolevJet :=
  restrictedJet_eq_test hS _ _ (φ.zeroExtendDirichlet_value_ae hT)

theorem extendDirichlet_mem (hS : IsOpen S) (hT : IsOpen T) (hTS : T ⊆ S)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (hu : u ∈ dirichletJetSpace T) :
    extendDirichlet S hT u hu ∈ dirichletJetSpace S := by
  obtain ⟨U,hU,ht⟩ := mem_closure_iff_seq_limit.mp hu
  choose φ hφ using fun n => exists_test_of_mem_test_span hT (hU n)
  have hu' (n : ℕ) : U n ∈ dirichletJetSpace T := Submodule.le_topologicalClosure _ (hU n)
  have he := restrictDomain_tendsto (S := S) (zeroExtendDirichlet_tendsto hT U hu' u hu ht)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto he
  apply Eventually.of_forall
  intro n
  change extendDirichlet S hT (U n) (hu' n) ∈ dirichletJetSpace S
  simp only [← hφ n,extendDirichlet_test hS hT hTS]
  exact test_mem_dirichletJetSpace S _

end WeakSobolevJet
end Carleman
