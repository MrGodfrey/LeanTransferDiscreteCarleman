module

public import Carleman.Spatial.SpatialTestDerivative

/-! Commutation of two genuine L² weak derivatives, deduced from all
original smooth tests, without assuming classical derivatives of the state. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.IsWeakSpatialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ν : Measure E} [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set E} {e f : E} {u ue uf uef ufe : Lp ℝ 2 ν}

theorem mixed_commute (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (he : IsWeakSpatialDerivative ν S e u ue)
    (hf : IsWeakSpatialDerivative ν S f u uf)
    (hef : IsWeakSpatialDerivative ν S f ue uef)
    (hfe : IsWeakSpatialDerivative ν S e uf ufe) : uef=ufe := by
  apply sub_eq_zero.mp
  apply spatial_eq_zero_of_tests hS hν
  intro φ
  have he' := he (φ.derivativeTest f)
  have hf' := hf (φ.derivativeTest e)
  rw [φ.derivativeTest_toLp] at he' hf'
  rw [φ.derivativeTest_derivativeLp_commute f e ν] at he'
  rw [inner_sub_left]
  have h1 := hef φ
  have h2 := hfe φ
  linarith

end Carleman.IsWeakSpatialDerivative
