module

public import Carleman.Control.HeatInterpolationData

/-! The original numerical data from weighted local interpolation estimates.
N3/N4 are now conclusions; concrete mesh estimates remain explicit premises. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical

def heatInterpolationErrors (CI Cp CE C0 mesh : ℝ)
    (hCI : 0 ≤ CI) (hCp : 0 ≤ Cp) (hCE : 0 ≤ CE) (hC0 : 0 ≤ C0) (hh : 0 ≤ mesh) : ErrorScales where
  aE := (CE+(1+CI)*Cp*CE)*mesh
  a₀ := (1+Cp)*C0*mesh^2
  ηA := 0
  aE_nonneg := by positivity
  a₀_nonneg := by positivity
  ηA_nonneg := le_rfl

/-- A single approximation constant, chosen before the mesh and weight. -/
theorem heatInterpolationErrors_orders (CI Cp CE C0 mesh : ℝ)
    (hCI : 0 ≤ CI) (hCp : 0 ≤ Cp) (hCE : 0 ≤ CE) (hC0 : 0 ≤ C0) (hh : 0 ≤ mesh) :
    let Cap := max (CE+(1+CI)*Cp*CE) ((1+Cp)*C0)
    let errors := heatInterpolationErrors CI Cp CE C0 mesh hCI hCp hCE hC0 hh
    0 ≤ Cap ∧ errors.aE ≤ Cap*mesh ∧ errors.a₀+errors.ηA ≤ Cap*mesh^2 := by
  dsimp [heatInterpolationErrors]
  refine ⟨le_trans (by positivity) (le_max_left _ _),
    mul_le_mul_of_nonneg_right (le_max_left _ _) hh,?_⟩
  simpa only [add_zero] using mul_le_mul_of_nonneg_right
    (le_max_right (CE+(1+CI)*Cp*CE) ((1+Cp)*C0)) (sq_nonneg mesh)

variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := 1) hS hν)
  (hD : a.model.domain ≤ sobolevSubspace d 2 ν S)
  (X : Submodule ℝ (Lp ℝ 2 ν)) [FiniteDimensional ℝ X] (hX : X ≤ a.V)
  (ρ : SpatialProfile ν) (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (g : TimeGrid) (w : TimeWeight) (β τStar CI Cp CE C0 CS mesh : ℝ)

/-- Uniform local estimates on both signs and all allowed τ supply the full
original N1–N5 data with the actual stiffness, projector and weighted test. -/
def interpolatedHeatNumericalData
    (hCI : 0 ≤ CI) (hCp : 0 ≤ Cp) (hCE : 0 ≤ CE) (hC0 : 0 ≤ C0) (hh : 0 ≤ mesh)
    (hw : TimeWeightRegularity w g β)
    (I : a.model.domain → X) (J : a.V → X)
    (ζ ξ : Bool → ℝ → ℝ → BoundedMultiplier ν)
    (ha : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
      HeatInterpolationData hS hν a.sobolev hD a.domain_le X hX g (ρ.signed e) w τ
        I (ζ e τ) CI Cp CE C0 mesh)
    (hs : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
      HeatSuperapproxData hS hν a.sobolev X hX g (ρ.signed e) w τ
        J (ξ e τ) CI Cp CS mesh) :
    Section5.NumericalData a hD (conformingReconstruction a.V X hX)
      (galerkinStiffness a X hX).toLinearMap 0 (conformingLoad a.V X hX)
      (conformingAmbientControl X obs hobs).adjoint.toLinearMap g w ρ obs hobs
      (conformingWeightedState X ρ w) (fun t => (ρ.multiplier w 0 t).seminorm)
      (fun t => (ρ.multiplier w 0 t).seminorm)
      τStar (2*β*(τStar+ρ.bound)) (CS+(1+CI)*Cp*CS) 1 mesh
      (heatInterpolationErrors CI Cp CE C0 mesh hCI hCp hCE hC0 hh) :=
  galerkinNumericalData a hD X hX ρ obs hobs g w τStar (2*β*(τStar+ρ.bound))
    (CS+(1+CI)*Cp*CS) mesh (heatInterpolationErrors CI Cp CE C0 mesh hCI hCp hCE hC0 hh)
    (fun e τ hτ => (ha e τ hτ).approximation hS hν a.sobolev hD a.domain_le X hX g
      (ρ.signed e) w τ hCI hCp)
    (fun e τ hτ => by
      have ht := galerkinWeightedTestData hS hν a.sobolev X hX g (ρ.signed e) w hw
        τStar τ (CS+(1+CI)*Cp*CS) mesh hτ
        ((hs e τ hτ).superapprox hS hν a.sobolev X hX g (ρ.signed e) w τ hCI hCp)
      cases e <;> exact ht)

end Carleman.Physical
