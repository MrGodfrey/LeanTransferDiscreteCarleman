module

public import Carleman.Spatial.CartesianPhysicalControlIsometry
public import Carleman.Spatial.PhysicalFiniteWeights

/-! Exact counting-L² images of the original Cartesian state and control weights. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

def cartesianCountLpEquiv (δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ) :
    CartesianPhysicalState δ hδ N ≃ₗᵢ[ℝ] Lp ℝ 2 (Measure.count : Measure (CartesianInteriorIndex N)) :=
  PhysicalFiniteSpace.countLpEquiv

def cartesianCountObservation (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) :
    CartesianPhysicalState δ hδ N →ₗ[ℝ] Lp ℝ 2 (Measure.count : Measure (CartesianInteriorIndex N)) :=
  (cartesianCountLpEquiv δ hδ N).toLinearMap.comp
    ((cartesianPhysicalControlExtension o δ hδ N ω).toLinearMap.comp
      (cartesianPhysicalControlExtension o δ hδ N ω).adjoint.toLinearMap)

theorem cartesianCountObservation_norm (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (f : CartesianPhysicalState δ hδ N) :
    ‖cartesianCountObservation o δ hδ N ω f‖ =
      ‖(cartesianPhysicalControlExtension o δ hδ N ω).adjoint f‖ := by
  change ‖cartesianCountLpEquiv δ hδ N (cartesianPhysicalControlExtension o δ hδ N ω
    ((cartesianPhysicalControlExtension o δ hδ N ω).adjoint f))‖ = _
  rw [LinearIsometryEquiv.norm_map,cartesianPhysicalControlExtension_norm]

def cartesianCountProfile (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (r : SpatialCoordinates d → ℝ) (R : ℝ) (hR : 0 ≤ R) (hr : ∀ x, |r x| ≤ R) :
    SpatialProfile (Measure.count : Measure (CartesianInteriorIndex N)) :=
  SpatialProfile.ofFinite (fun a => r (cartesianInteriorPoint o δ N a)) R hR
    (fun a => hr (cartesianInteriorPoint o δ N a))

theorem cartesianCountProfile_seminorm (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (r : SpatialCoordinates d → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ x, |r x| ≤ R) (w : TimeWeight) (τ t : ℝ) (f : CartesianPhysicalState δ hδ N) :
    ((cartesianCountProfile o δ N r R hR hr).multiplier w τ t).seminorm
      (cartesianCountLpEquiv δ hδ N f) =
    cartesianStateSeminorm o δ hδ N (fun x => w.q t ^ τ * Real.exp (r x*w.q t)) f := by
  exact PhysicalFiniteSpace.countLpEquiv_weighted_norm _ f

theorem cartesianCountProfile_observation (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (r : SpatialCoordinates d → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hr : ∀ x, |r x| ≤ R) (w : TimeWeight) (τ t : ℝ)
    (f : CartesianPhysicalState δ hδ N) :
    ((cartesianCountProfile o δ N r R hR hr).multiplier w τ t).seminorm
      (cartesianCountObservation o δ hδ N ω f) =
    cartesianControlSeminorm o δ hδ N ω (fun x => w.q t ^ τ * Real.exp (r x*w.q t))
      ((cartesianPhysicalControlExtension o δ hδ N ω).adjoint f) := by
  change ((cartesianCountProfile o δ N r R hR hr).multiplier w τ t).seminorm
    (cartesianCountLpEquiv δ hδ N (cartesianPhysicalControlExtension o δ hδ N ω
      ((cartesianPhysicalControlExtension o δ hδ N ω).adjoint f))) = _
  rw [cartesianCountProfile_seminorm,cartesianPhysicalControlExtension_seminorm]

end Carleman
