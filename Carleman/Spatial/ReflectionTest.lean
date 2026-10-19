module

public import Carleman.Spatial.CoordinateReflectionH1
public import Carleman.Spatial.DirichletExtensionContinuity

/-! Actual full-space test jets and their coordinate reflections. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialTest
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def fullJet (φ : SpatialTest S) : WeakSobolevJet d 1 volume univ :=
  WeakSobolevJet.zeroExtendDirichlet isOpen_univ φ.toUniv.sobolevJet
    (test_mem_dirichletJetSpace univ φ.toUniv)

theorem fullJet_value_ae (φ : SpatialTest S) :
    WeakSobolevJet.value φ.fullJet =ᵐ[volume] φ.value :=
  φ.toUniv.zeroExtendDirichlet_value_ae isOpen_univ

theorem fullJet_restrict (hS : IsOpen S) (φ : SpatialTest S) :
    WeakSobolevJet.restrictDomain S φ.fullJet=φ.sobolevJet :=
  restrictedJet_eq_test hS φ φ.fullJet φ.fullJet_value_ae

def reflectCoordinate (φ : SpatialTest S) (r : Fin d) (c : ℝ) :
    SpatialTest (univ : Set (SpatialCoordinates d)) :=
  φ.pullbackAffine (coordinateSignFlip r).toContinuousLinearEquiv
    ((2*c) • EuclideanSpace.basisFun (Fin d) ℝ r) (subset_univ _)

theorem reflectCoordinate_value (φ : SpatialTest S) (r : Fin d) (c : ℝ)
    (x : SpatialCoordinates d) :
    (φ.reflectCoordinate r c).value x=φ.value (coordinateReflection r c x) := rfl

theorem reflectCoordinate_fullJet (φ : SpatialTest S) (r : Fin d) (c : ℝ) :
    (φ.reflectCoordinate r c).fullJet=WeakSobolevJet.reflectCoordinate r c φ.fullJet := by
  apply WeakSobolevJet.value_injective isOpen_univ (Filter.Eventually.of_forall fun _ => mem_univ _)
  rw [WeakSobolevJet.reflectCoordinate_value]
  apply Lp.ext
  filter_upwards [(φ.reflectCoordinate r c).fullJet_value_ae,
    coordinateReflectionLp_ae r c (WeakSobolevJet.value φ.fullJet),
    (coordinateReflection_measurePreserving r c).quasiMeasurePreserving.ae φ.fullJet_value_ae]
    with x h1 h2 h3
  exact h1.trans (h2.trans h3).symm

def oddReflectionTest (φ : SpatialTest S) (r : Fin d) (c : ℝ) :
    SpatialTest (univ : Set (SpatialCoordinates d)) :=
  φ.toUniv.addTest ((φ.reflectCoordinate r c).smulTest (-1))

theorem oddReflectionTest_value (φ : SpatialTest S) (r : Fin d) (c : ℝ)
    (x : SpatialCoordinates d) :
    (φ.oddReflectionTest r c).value x=φ.value x-φ.value (coordinateReflection r c x) := by
  change φ.value x+(-1)*φ.value (coordinateReflection r c x)=_
  ring

theorem oddReflectionTest_fullJet (φ : SpatialTest S) (r : Fin d) (c : ℝ) :
    (φ.oddReflectionTest r c).fullJet=φ.fullJet-WeakSobolevJet.reflectCoordinate r c φ.fullJet := by
  apply WeakSobolevJet.value_injective isOpen_univ (Filter.Eventually.of_forall fun _ => mem_univ _)
  rw [map_sub,WeakSobolevJet.reflectCoordinate_value]
  apply Lp.ext
  filter_upwards [(φ.oddReflectionTest r c).fullJet_value_ae,φ.fullJet_value_ae,
    coordinateReflectionLp_ae r c (WeakSobolevJet.value φ.fullJet),
    (coordinateReflection_measurePreserving r c).quasiMeasurePreserving.ae φ.fullJet_value_ae,
    Lp.coeFn_sub (WeakSobolevJet.value φ.fullJet) (coordinateReflectionLp r c (WeakSobolevJet.value φ.fullJet))]
    with x h1 h2 h3 h4 h5
  rw [h1,h5,Pi.sub_apply,h2,h3,Function.comp_apply,h4,oddReflectionTest_value]

end Carleman.SpatialTest
