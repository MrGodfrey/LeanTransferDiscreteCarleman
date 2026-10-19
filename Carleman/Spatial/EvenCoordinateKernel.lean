module

public import Carleman.Spatial.LocalOddConvolution
public import Carleman.Spatial.ReflectionTest

/-! Explicit coordinate symmetrization of smooth compact kernels, preserving support and mass. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem coordinateSignFlip_commute (r s : Fin d) :
    Function.Commute (coordinateSignFlip r) (coordinateSignFlip s) := by
  by_cases hrs : r=s
  · subst s
    intro x
    rfl
  intro x
  ext j
  by_cases hjr : j=r
  · subst j
    simp [coordinateSignFlip_apply,hrs]
  · by_cases hjs : j=s
    · subst j
      simp [coordinateSignFlip_apply,Ne.symm hrs]
    · simp [coordinateSignFlip_apply,hjr,hjs]

namespace SpatialTest

def evenCoordinate (κ : SpatialTest (univ : Set (SpatialCoordinates d))) (r : Fin d) :
    SpatialTest (univ : Set (SpatialCoordinates d)) :=
  (κ.addTest (κ.reflectCoordinate r 0)).smulTest (1/2)

theorem evenCoordinate_value (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (r : Fin d) (x : SpatialCoordinates d) :
    (κ.evenCoordinate r).value x=(κ.value x+κ.value (coordinateSignFlip r x))/2 := by
  change (1/2)*(κ.value x+κ.value (coordinateReflection r 0 x))=_
  rw [coordinateReflection_zero]
  ring

theorem evenCoordinate_invariant (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (r : Fin d) (x : SpatialCoordinates d) :
    (κ.evenCoordinate r).value (coordinateSignFlip r x)=(κ.evenCoordinate r).value x := by
  rw [evenCoordinate_value,evenCoordinate_value,coordinateSignFlip_involutive]
  ring

theorem evenCoordinate_preserves_invariant (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (r s : Fin d) (hs : ∀ x, κ.value (coordinateSignFlip s x)=κ.value x)
    (x : SpatialCoordinates d) :
    (κ.evenCoordinate r).value (coordinateSignFlip s x)=(κ.evenCoordinate r).value x := by
  rw [evenCoordinate_value,evenCoordinate_value,coordinateSignFlip_commute r s,hs,hs]

theorem evenCoordinate_nonneg (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (r : Fin d) (hκ : ∀ x, 0 ≤ κ.value x) (x : SpatialCoordinates d) :
    0 ≤ (κ.evenCoordinate r).value x := by
  rw [evenCoordinate_value]
  positivity [hκ x,hκ (coordinateSignFlip r x)]

theorem evenCoordinate_integral (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (r : Fin d) : (∫ x, (κ.evenCoordinate r).value x) = ∫ x, κ.value x := by
  have hi : Integrable κ.value volume := κ.smooth.continuous.integrable_of_hasCompactSupport κ.compact
  have hir : Integrable (κ.reflectCoordinate r 0).value volume :=
    (κ.reflectCoordinate r 0).smooth.continuous.integrable_of_hasCompactSupport
    (κ.reflectCoordinate r 0).compact
  change (∫ x, (1/2)*(κ.value x+(κ.reflectCoordinate r 0).value x))=_
  rw [integral_const_mul,integral_add hi hir]
  have he : (∫ x, (κ.reflectCoordinate r 0).value x)=∫ x, κ.value x :=
    (coordinateReflection_measurePreserving r 0).integral_comp
      (coordinateReflection r 0).toMeasurableEquiv.measurableEmbedding _
  rw [he]
  ring

theorem evenCoordinate_support (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (r : Fin d) {δ : ℝ} (hκ : Function.support κ.value ⊆ Metric.ball 0 δ) :
    Function.support (κ.evenCoordinate r).value ⊆ Metric.ball 0 δ := by
  intro x hx
  by_contra hn
  have hz : κ.value x=0 := Function.notMem_support.mp fun h => hn (hκ h)
  have hzr : κ.value (coordinateSignFlip r x)=0 := by
    apply Function.notMem_support.mp
    intro h
    have hh := hκ h
    have he : ‖coordinateSignFlip r x‖=‖x‖ := (coordinateSignFlip r).norm_map x
    apply hn
    simpa only [Metric.mem_ball,dist_zero_right,he] using hh
  exact hx (by rw [evenCoordinate_value,hz,hzr]; ring)

end SpatialTest
end Carleman
