module

public import Carleman.Control.GalerkinStiffness

/-! The actual Galerkin construction discharges N1/N2/N5 and the stiffness
defect. Only the original weighted approximation and test estimates remain. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω}
  (V X : Submodule ℝ (Lp E 2 ν)) [CompleteSpace X] (hX : X ≤ V)

theorem conformingReconstruction_injective :
    Function.Injective (conformingReconstruction V X hX).R :=
  Submodule.inclusion_injective hX

theorem conformingReconstruction_G : (conformingReconstruction V X hX).G = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change X.orthogonalProjectionOnto (x : Lp E 2 ν) = x
  exact X.orthogonalProjectionOnto_mem_subspace_eq_self x

theorem conformingReconstruction_QH :
    (conformingReconstruction V X hX).QH =
      (X.subtypeL.comp X.orthogonalProjectionOnto).toLinearMap := rfl

omit V hX in
theorem conforming_weighted_observation [CompleteSpace E]
    (σ : BoundedMultiplier ν) (obs : Set Ω) (hobs : MeasurableSet obs) (x : X) :
    σ.observation obs hobs (x : Lp E 2 ν) =
      σ.seminorm ((conformingAmbientControl X obs hobs).adjoint x) := by
  rw [conformingAmbientControl_adjoint]
  rfl

end Carleman.Physical

@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := m) hS hν)
  (hD : a.model.domain ≤ sobolevSubspace d (2*m) ν S)
  (X : Submodule ℝ (Lp ℝ 2 ν)) [FiniteDimensional ℝ X] (hX : X ≤ a.V)
  (ρ : SpatialProfile ν) (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (g : TimeGrid) (w : TimeWeight) (τStar Ctime Csuper mesh : ℝ) (errors : ErrorScales)

/-- Actual consistent-mass N1/N2/N5 constants are one. N3 and N4 are the
remaining finite-element analytic obligations, explicitly supplied here. -/
def galerkinNumericalData
    (approximation : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
      Section4.WeightedApproximation hS hν a.sobolev hD a.domain_le
        (conformingReconstruction a.V X hX) g (ρ.signed e) w τ errors.aE errors.a₀)
    (test : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
      Section4.WeightedTest hS hν a.sobolev (conformingReconstruction a.V X hX)
        g (ρ.signed e) w τ Ctime Csuper mesh) :
    Section5.NumericalData a hD (conformingReconstruction a.V X hX)
      (galerkinStiffness a X hX).toLinearMap 0 (conformingLoad a.V X hX)
      (conformingAmbientControl X obs hobs).adjoint.toLinearMap g w ρ obs hobs
      (conformingWeightedState X ρ w) (fun t => (ρ.multiplier w 0 t).seminorm)
      (fun t => (ρ.multiplier w 0 t).seminorm) τStar Ctime Csuper 1 mesh errors where
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
    change ((ρ.multiplier w 0 (g.nodeTime i)).observation obs hobs (v : Lp ℝ 2 ν))^2 ≤ _
    rw [conforming_weighted_observation]
    exact le_rfl

end Carleman.Physical
