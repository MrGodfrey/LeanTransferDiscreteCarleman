module

public import Carleman.Control.GalerkinNumericalData
public import Carleman.Control.ConformingRegionControl
public import Carleman.Spatial.CellwiseInverseWeight

/-! Actual L²(omega) controls with their actual restricted weights. This
retains the original smaller observation set and all consistent-mass data. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω}

theorem restrictRegion_weighted_sq (σ : BoundedMultiplier ν) (ω : Set Ω)
    (u : Lp E 2 ν) :
    ((σ.restrictMeasure Measure.restrict_le_self).seminorm (restrictRegionLp ω u))^2 =
      ∫ x in ω, |σ.value x|^2*‖u x‖^2 ∂ν := by
  rw [BoundedMultiplier.seminorm_sq_integral]
  apply integral_congr_ae
  filter_upwards [restrictRegionLp_ae ω u] with x hx
  rw [hx]
  rfl

theorem conforming_region_weighted_observation [CompleteSpace E]
    (X : Submodule ℝ (Lp E 2 ν)) [CompleteSpace X]
    (σ : BoundedMultiplier ν) (ω₀ ω : Set Ω) (hω₀ : MeasurableSet ω₀) (hinc : ω₀ ⊆ ω) (u : X) :
    (σ.observation ω₀ hω₀ (u : Lp E 2 ν))^2 ≤
      ((σ.restrictMeasure Measure.restrict_le_self).seminorm ((conformingRegionControl X ω).adjoint u))^2 := by
  rw [σ.observation_sq_integral,conformingRegionControl_adjoint_apply,restrictRegion_weighted_sq]
  exact setIntegral_mono_set (σ.integrable_density (u : Lp E 2 ν)).integrableOn
    (Filter.Eventually.of_forall fun _ => by positivity) (Filter.Eventually.of_forall hinc)

variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := m) hS hν)
  (hD : a.model.domain ≤ sobolevSubspace d (2*m) ν S)
  (X : Submodule ℝ (Lp ℝ 2 ν)) [FiniteDimensional ℝ X] (hX : X ≤ a.V)
  (ρ : SpatialProfile ν) (ω₀ ω : Set (SpatialCoordinates d)) (hω₀ : MeasurableSet ω₀)
  (hinc : ω₀ ⊆ ω) (g : TimeGrid) (w : TimeWeight)
  (τStar Ctime Csuper mesh : ℝ) (errors : ErrorScales)

def galerkinRegionNumericalData
    (approximation : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
      Section4.WeightedApproximation hS hν a.sobolev hD a.domain_le
        (conformingReconstruction a.V X hX) g (ρ.signed e) w τ errors.aE errors.a₀)
    (test : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
      Section4.WeightedTest hS hν a.sobolev (conformingReconstruction a.V X hX)
        g (ρ.signed e) w τ Ctime Csuper mesh) :
    Section5.NumericalData a hD (conformingReconstruction a.V X hX)
      (galerkinStiffness a X hX).toLinearMap 0 (conformingLoad a.V X hX)
      (conformingRegionControl X ω).adjoint.toLinearMap g w ρ ω₀ hω₀
      (conformingWeightedState X ρ w) (fun t => (ρ.multiplier w 0 t).seminorm)
      (fun t => ((ρ.multiplier w 0 t).restrictMeasure Measure.restrict_le_self).seminorm)
      τStar Ctime Csuper 1 mesh errors where
  stiffness := galerkinStiffness_defect_zero a X hX
  approximation := approximation
  test := test
  defect e τ _ i z v := by
    simp only [LinearMap.zero_apply,abs_zero]
    exact mul_nonneg (mul_nonneg errors.ηA_nonneg
      (conformingWeightedNorm_nonneg hS hν a.sobolev _ _ _))
      (conformingWeightedNorm_nonneg hS hν a.sobolev _ _ _)
  reconstruction_upper _ _ := by simp only [one_mul]; exact le_rfl
  reconstruction_lower _ _ := by simp only [one_mul]; exact le_rfl
  lift_bound _ _ := by simp only [one_mul]; exact le_rfl
  observation_bound i v := by
    simp only [one_mul]
    exact conforming_region_weighted_observation X (ρ.multiplier w 0 (g.nodeTime i)) ω₀ ω hω₀ hinc v

end Carleman.Physical
