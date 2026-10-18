module

public import Carleman.Transfer.CompleteBridges

/-! Only original numerical assumptions. Bounds are squared with a common
constant; unused positivity, finite-dimensionality and stronger norm relations
from N1/N4 are not required by the estimate. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Section5
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} {hS : IsOpen S} {hν : ∀ᵐ x ∂ν, x ∈ S}
  (a : OriginalForm (m := m) hS hν)
  (hD : a.model.domain ≤ sobolevSubspace d (2*m) ν S)
  {X F Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup Y] [Module ℝ Y]
  (r : Reconstruction a.V X) (A : X →ₗ[ℝ] X) (b : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
  (l : LoadInterface r F) (Bstar : X →ₗ[ℝ] Y)
  (g : TimeGrid) (w : TimeWeight) (ρ : SpatialProfile ν)
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)
  (state : ℝ → Seminorm ℝ X) (load : ℝ → Seminorm ℝ F) (control : ℝ → Seminorm ℝ Y)
  (τStar Ctime Csuper Cnum mesh : ℝ) (errors : ErrorScales)

/-- A local instance of N1--N5 at the allowed grid and weight. The constant
Cnum is fixed before the numerical spaces; no error estimate is a field. -/
structure NumericalData where
  stiffness : ∀ z v, inner ℝ (A z) v = a.scalarForm (r.R z) (r.R v)+b z v
  approximation : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
    Section4.WeightedApproximation hS hν a.sobolev hD a.domain_le r g (ρ.signed e) w τ errors.aE errors.a₀
  test : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar →
    Section4.WeightedTest hS hν a.sobolev r g (ρ.signed e) w τ Ctime Csuper mesh
  defect : ∀ (e : Bool) (τ : ℝ), |τ| ≤ τStar → ∀ i z v, |b z v| ≤
    errors.ηA*conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i))
      ((ρ.signed e).multiplier w τ (g.nodeTime i)) (r.R z)*
      conformingWeightedNorm hS hν a.sobolev (w.q (g.nodeTime i))
        ((ρ.signed e).neg.multiplier w (-τ) (g.nodeTime i)) (r.R v)
  reconstruction_upper : ∀ i v, ((ρ.multiplier w 0 (g.nodeTime i)).seminorm (r.RH v))^2 ≤
    Cnum*(state (g.nodeTime i) v)^2
  reconstruction_lower : ∀ i v, (state (g.nodeTime i) v)^2 ≤
    Cnum*((ρ.multiplier w 0 (g.nodeTime i)).seminorm (r.RH v))^2
  lift_bound : ∀ i v, ((ρ.multiplier w 0 (g.nodeTime i)).seminorm (l.lift v))^2 ≤
    Cnum*(load (g.nodeTime i) v)^2
  observation_bound : ∀ i v, ((ρ.multiplier w 0 (g.nodeTime i)).observation obs hobs (r.RH v))^2 ≤
    Cnum*(control (g.nodeTime i) (Bstar v))^2

end Carleman.Section5
