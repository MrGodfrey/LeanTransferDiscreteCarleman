module

public import Carleman.Spatial.OddReflectionPoisson
public import Carleman.Spatial.ReflectionContinuity

/-! Odd reflection preserves the actual H1_0 closure on a containing domain.
Both pieces are approximated by the original smooth compact test sequence. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

def SpatialTest.oddReflectionInto (φ : SpatialTest S) (r : Fin d) (c : ℝ)
    (hST : S ⊆ T) (hRT : (coordinateReflection r c) ⁻¹' S ⊆ T) : SpatialTest T :=
  (φ.monoDomain hST).addTest ((φ.pullbackAffine (coordinateSignFlip r).toContinuousLinearEquiv
    ((2*c) • EuclideanSpace.basisFun (Fin d) ℝ r) hRT).smulTest (-1))

theorem SpatialTest.oddReflectionInto_value (φ : SpatialTest S) (r : Fin d) (c : ℝ)
    (hST : S ⊆ T) (hRT : (coordinateReflection r c) ⁻¹' S ⊆ T) (x : SpatialCoordinates d) :
    (φ.oddReflectionInto r c hST hRT).value x=(φ.oddReflectionTest r c).value x := rfl

theorem SpatialTest.oddExtend_test (hS : IsOpen S) (hT : IsOpen T) (φ : SpatialTest S)
    (r : Fin d) (c : ℝ) (hST : S ⊆ T) (hRT : (coordinateReflection r c) ⁻¹' S ⊆ T) :
    WeakSobolevJet.restrictDomain T
      (WeakSobolevJet.oddExtend hS φ.sobolevJet (test_mem_dirichletJetSpace S φ) r c)=
      (φ.oddReflectionInto r c hST hRT).sobolevJet := by
  rw [WeakSobolevJet.oddExtend,← φ.fullJet_eq_zeroExtend hS,← φ.oddReflectionTest_fullJet]
  exact restrictedJet_eq_test hT _ _ (φ.oddReflectionTest r c).fullJet_value_ae

theorem WeakSobolevJet.oddExtend_tendsto (hS : IsOpen S)
    (U : ℕ → WeakSobolevJet d 1 (volume.restrict S) S) (hU : ∀ n, U n ∈ dirichletJetSpace S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (ht : Tendsto U atTop (𝓝 u)) (r : Fin d) (c : ℝ) :
    Tendsto (fun n => oddExtend hS (U n) (hU n) r c) atTop (𝓝 (oddExtend hS u hu r c)) := by
  have he := zeroExtendDirichlet_tendsto hS U hU u hu ht
  exact he.sub (reflectCoordinate_tendsto r c he)

theorem WeakSobolevJet.oddExtend_mem (hS : IsOpen S) (hT : IsOpen T)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (r : Fin d) (c : ℝ) (hST : S ⊆ T) (hRT : (coordinateReflection r c) ⁻¹' S ⊆ T) :
    restrictDomain T (oddExtend hS u hu r c) ∈ dirichletJetSpace T := by
  obtain ⟨U,hU,ht⟩ := mem_closure_iff_seq_limit.mp hu
  choose φ hφ using fun n => exists_test_of_mem_test_span hS (hU n)
  have hu' (n : ℕ) : U n ∈ dirichletJetSpace S := Submodule.le_topologicalClosure _ (hU n)
  have he := restrictDomain_tendsto (S := T) (oddExtend_tendsto hS U hu' u hu ht r c)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto he
  apply Eventually.of_forall
  intro n
  change restrictDomain T (oddExtend hS (U n) (hu' n) r c) ∈ dirichletJetSpace T
  simp only [← hφ n,SpatialTest.oddExtend_test hS hT _ r c hST hRT]
  exact test_mem_dirichletJetSpace T _

end Carleman
