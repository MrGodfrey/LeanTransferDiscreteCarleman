module

public import Carleman.Spatial.EvenCoordinateKernel
public import Carleman.Spatial.FullSpaceInterpolation

/-! A genuine smooth unit-mass mollifier invariant under every coordinate reflection. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution
namespace Carleman
variable {d : ℕ}

namespace SpatialTest

def evenCoordinates (κ : SpatialTest (univ : Set (SpatialCoordinates d))) (rs : List (Fin d)) :
    SpatialTest (univ : Set (SpatialCoordinates d)) :=
  rs.foldr (fun r φ => φ.evenCoordinate r) κ

theorem evenCoordinates_invariant (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (rs : List (Fin d)) (r : Fin d) (hr : r ∈ rs) (x : SpatialCoordinates d) :
    (κ.evenCoordinates rs).value (coordinateSignFlip r x)=(κ.evenCoordinates rs).value x := by
  induction rs generalizing x with
  | nil => simp at hr
  | cons s rs ih =>
    change ((κ.evenCoordinates rs).evenCoordinate s).value (coordinateSignFlip r x)=_
    rcases List.mem_cons.mp hr with he | hmem
    · subst s
      exact evenCoordinate_invariant _ _ _
    · exact evenCoordinate_preserves_invariant _ s r (fun y => ih hmem y) x

theorem evenCoordinates_nonneg (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (rs : List (Fin d)) (hκ : ∀ x, 0 ≤ κ.value x) :
    ∀ x, 0 ≤ (κ.evenCoordinates rs).value x := by
  induction rs with
  | nil => exact hκ
  | cons r rs ih => exact evenCoordinate_nonneg _ r ih

theorem evenCoordinates_integral (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (rs : List (Fin d)) : (∫ x, (κ.evenCoordinates rs).value x)=∫ x, κ.value x := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change (∫ x, ((κ.evenCoordinates rs).evenCoordinate r).value x)=_
    rw [evenCoordinate_integral,ih]

theorem evenCoordinates_support (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (rs : List (Fin d)) {δ : ℝ} (hκ : Function.support κ.value ⊆ Metric.ball 0 δ) :
    Function.support (κ.evenCoordinates rs).value ⊆ Metric.ball 0 δ := by
  induction rs with
  | nil => exact hκ
  | cons r rs ih => exact evenCoordinate_support _ r ih

end SpatialTest

def evenSpatialMollifier (d n : ℕ) : SpatialTest (univ : Set (SpatialCoordinates d)) :=
  (spatialMollifier d n).evenCoordinates Finset.univ.toList

theorem evenSpatialMollifier_invariant (n : ℕ) (r : Fin d) (x : SpatialCoordinates d) :
    (evenSpatialMollifier d n).value (coordinateSignFlip r x)=(evenSpatialMollifier d n).value x :=
  SpatialTest.evenCoordinates_invariant _ _ r (by simp) x

theorem evenSpatialMollifier_nonneg (n : ℕ) (x : SpatialCoordinates d) :
    0 ≤ (evenSpatialMollifier d n).value x :=
  SpatialTest.evenCoordinates_nonneg _ _ (spatialMollifier_nonneg n) x

theorem evenSpatialMollifier_integral (n : ℕ) : (∫ x, (evenSpatialMollifier d n).value x)=1 := by
  rw [evenSpatialMollifier,SpatialTest.evenCoordinates_integral,spatialMollifier_integral]

theorem evenSpatialMollifier_support (n : ℕ) :
    Function.support (evenSpatialMollifier d n).value ⊆ Metric.ball 0 (shrinkingBump d n).rOut := by
  apply SpatialTest.evenCoordinates_support
  exact ((shrinkingBump d n).support_normed_eq (μ := volume)).subset

theorem evenSpatialMollifier_convolution_zero (n : ℕ) (r : Fin d) (c : ℝ)
    {f : SpatialCoordinates d → ℝ} {x : SpatialCoordinates d} (hx : x r=c)
    (hodd : ∀ᵐ y ∂(volume : Measure (SpatialCoordinates d)),
      y ∈ Metric.ball x (shrinkingBump d n).rOut → f (coordinateReflection r c y)= -f y) :
    ((evenSpatialMollifier d n).value ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f) x=0 :=
  convolution_zero_of_local_odd r c _ (evenSpatialMollifier_invariant n r)
    (evenSpatialMollifier_support n) hx hodd

end Carleman
