module

public import Carleman.Control.GalerkinNumericalData
public import Carleman.Control.ConformingHeatControl

/-! The remaining analytic data for actual Galerkin physical control.
All consistent-mass algebraic and norm interfaces are constructed internally. -/
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
  (g : TimeGrid) (w : TimeWeight) (c C Ccomm τStar Ctime Csuper Cce mesh : ℝ)
  (errors : ErrorScales)

/-- Original A2/A3 and continuous A4, together with N3/N4. No stiffness,
mass, lift, observation, discrete CE or physical control assertion is a field. -/
structure GalerkinHeatData where
  allowed : Section3.AllowedFamily hS hν a.sobolev hD a.scalarForm a.model.operator ρ w c C Ccomm τStar
  approximation : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
    Section4.WeightedApproximation hS hν a.sobolev hD a.domain_le
      (conformingReconstruction a.V X hX) g (ρ.signed e) w τ errors.aE errors.a₀
  test : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
    Section4.WeightedTest hS hν a.sobolev (conformingReconstruction a.V X hX)
      g (ρ.signed e) w τ Ctime Csuper mesh
  continuous : ∀ (s : Orientation) (U : PeriodicWeakTrajectory g a.model.domain a.model.operator),
    (conformingHeatGeometry a ρ P obs hobs X w).continuousEnergy g
      ((conformingHeatGeometry a ρ P obs hobs X w).trajectory g a.domain_le U) ≤ Cce *
      (timeSq g w.q 0 (conformingHeatGeometry a ρ P obs hobs X w).space
        (fun t => s.sign • U.derivative t+a.model.operator (U.domainValue t))+
      timeSq g w.q CarlemanExponents.heat.o (conformingHeatGeometry a ρ P obs hobs X w).observation
        (fun t => (U.domainValue t : Lp ℝ 2 ν)))

def GalerkinHeatData.toConforming
    (H : GalerkinHeatData a hD ρ P obs hobs X hX g w c C Ccomm τStar Ctime Csuper Cce mesh errors) :
    ConformingHeatData a hD ρ P obs hobs X hX (galerkinStiffness a X hX) 0 g w
      c C Ccomm τStar Ctime Csuper 1 Cce mesh errors where
  allowed := H.allowed
  numerical := galerkinNumericalData a hD X hX ρ obs hobs g w τStar Ctime Csuper mesh errors
    H.approximation H.test
  continuous := H.continuous

end Carleman.Physical
