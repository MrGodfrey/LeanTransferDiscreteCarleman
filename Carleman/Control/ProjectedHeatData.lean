module

public import Carleman.Control.GalerkinTestData
public import Carleman.Control.GalerkinHeatControl

/-! Only original spatial approximation and superapproximation remain in
the numerical data; the genuine projected test and its time bound are built. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := CarlemanExponents.heat.m) hS hν)
  (hD : a.model.domain ≤ sobolevSubspace d (2*CarlemanExponents.heat.m) ν S)
  (ρ : SpatialProfile ν)
  {Z : Fin CarlemanExponents.heat.m → Type*}
  [∀ j, NormedAddCommGroup (Z j)] [∀ j, InnerProductSpace ℝ (Z j)]
  (P : ∀ j : Fin CarlemanExponents.heat.m, DifferentialExpression ν
    (fun k : Fin (CarlemanExponents.heat.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (X : Submodule ℝ (Lp ℝ 2 ν)) [FiniteDimensional ℝ X] (hX : X ≤ a.V)
  (g : TimeGrid) (w : TimeWeight) (c C Ccomm β τStar Csuper Cce mesh : ℝ)
  (errors : ErrorScales)

/-- Original A2/A3 and continuous A4, plus N3 and spatial N4 superapproximation.
The test operator and all of its temporal properties are not inputs. -/
structure ProjectedHeatData where
  allowed : Section3.AllowedFamily hS hν a.sobolev hD a.scalarForm a.model.operator ρ w c C Ccomm τStar
  approximation : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
    Section4.WeightedApproximation hS hν a.sobolev hD a.domain_le
      (conformingReconstruction a.V X hX) g (ρ.signed e) w τ errors.aE errors.a₀
  superapprox : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
    GalerkinSuperapprox hS hν a.sobolev X hX g (ρ.signed e) w τ Csuper mesh
  continuous : ∀ (s : Orientation) (U : PeriodicWeakTrajectory g a.model.domain a.model.operator),
    (conformingHeatGeometry a ρ P obs hobs X w).continuousEnergy g
      ((conformingHeatGeometry a ρ P obs hobs X w).trajectory g a.domain_le U) ≤ Cce *
      (timeSq g w.q 0 (conformingHeatGeometry a ρ P obs hobs X w).space
        (fun t => s.sign • U.derivative t+a.model.operator (U.domainValue t))+
      timeSq g w.q CarlemanExponents.heat.o (conformingHeatGeometry a ρ P obs hobs X w).observation
        (fun t => (U.domainValue t : Lp ℝ 2 ν)))

def ProjectedHeatData.toGalerkin
    (H : ProjectedHeatData a hD ρ P obs hobs X hX g w c C Ccomm τStar Csuper Cce mesh errors)
    (h : TimeWeightRegularity w g β) :
    GalerkinHeatData a hD ρ P obs hobs X hX g w
      c C Ccomm τStar (2*β*(τStar+ρ.bound)) Csuper Cce mesh errors where
  allowed := H.allowed
  approximation := H.approximation
  test e τ hτ := by
    have hh := galerkinWeightedTestData hS hν a.sobolev X hX g (ρ.signed e) w h
      τStar τ Csuper mesh hτ (H.superapprox e τ hτ)
    cases e <;> exact hh
  continuous := H.continuous

end Carleman.Physical
