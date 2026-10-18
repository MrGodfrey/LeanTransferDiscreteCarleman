module

public import Carleman.Control.ConformingTransferData

/-! Original Corollary 2.3 supplies the physical periodic load estimate,
with thresholds independent of the time horizon and all discrete data. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set
namespace Carleman.Physical
variable {d : ℕ} {S : Set (SpatialCoordinates d)}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (hΩ : IsBoundedLipschitzDomain S E)
  (a : OriginalForm (m := CarlemanExponents.heat.m) (ν := volume.restrict S)
    hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet))
  (hD : a.model.domain ≤ sobolevSubspace d (2*CarlemanExponents.heat.m) (volume.restrict S) S)
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)
  {Z : Fin CarlemanExponents.heat.m → Type*}
  [∀ j, NormedAddCommGroup (Z j)] [∀ j, InnerProductSpace ℝ (Z j)]
  (P : ∀ j : Fin CarlemanExponents.heat.m, DifferentialExpression (volume.restrict S)
    (fun k : Fin (CarlemanExponents.heat.m+1) => DerivativeFiber d k.val) (Z j) (j.val+1))
  (obs : Set (SpatialCoordinates d)) (hobs : MeasurableSet obs)

include hρ in
theorem conforming_heat_load_uniform (Cap Creg c C Ccomm β τStar Ctime Csuper δnum Cnum Cce : ℝ)
    (hCap : 0 ≤ Cap) (hc : 0 < c) (hC : 0 ≤ C) (hCc : 0 ≤ Ccomm) (hβ : 0 < β) (hτ : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδ : 0 < δnum) (hCn : 0 ≤ Cnum) (hCce : 0 ≤ Cce)
    (hcover : max (CarlemanExponents.heat.dStar/2) (CarlemanExponents.heat.bStar/2) ≤ τStar)
    (hell : ∀ v : a.model.domain,
      ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖a.model.operator v‖) :
    ∃ κ h0 Δ0 CCE : ℝ,
      0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧ 0 < Δ0 ∧ Δ0 ≤ 1 ∧ 0 < CCE ∧
      ∀ (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [CompleteSpace X]
        (hX : X ≤ a.V) (A : X →L[ℝ] X) (defect : X →ₗ[ℝ] X →ₗ[ℝ] ℝ)
        (g : TimeGrid) (w : TimeWeight), TimeWeightRegularity w g β →
        ∀ (mesh : ℝ) (errors : ErrorScales), 0 < mesh → mesh ≤ h0 → g.dt ≤ Δ0 →
        w.max ≤ κ*min (mesh^(-(4/5:ℝ))) (g.dt^(-(2/5:ℝ))) →
        errors.aE ≤ Cap*mesh → errors.a₀+errors.ηA ≤ Cap*mesh^2 →
        ConformingHeatData a hD ρ P obs hobs X hX A defect g w
          c C Ccomm τStar Ctime Csuper Cnum Cce mesh errors →
        PhysicalLoadCarleman ρ w g A X.subtype
          (conformingAmbientControl X obs hobs).adjoint.toLinearMap
          X.orthogonalProjectionOnto.toLinearMap CCE := by
  obtain ⟨κ,h0,Δ0,CCE,hκ,hh0,hh01,hΔ0,hΔ01,hCCE,ht⟩ :=
    a.heat_scale_uniform hΩ hD ρ hρ P obs hobs Cap Creg c C Ccomm β τStar Ctime Csuper δnum Cnum Cce
      hCap hc hC hCc hβ hτ hCt hCs hδ hCn hCce hcover hell
  refine ⟨κ,h0,Δ0,CCE,hκ,hh0,hh01,hΔ0,hΔ01,hCCE,?_⟩
  intro X _ hX A defect g w hw mesh errors hx hx0 hdt hscale haE ha0 N
  let r := conformingReconstruction a.V X hX
  let l := conformingLoad a.V X hX
  let p := conformingHeatGeometry a ρ P obs hobs X w
  have he := ht X (Lp ℝ 2 (volume.restrict S)) (Lp ℝ 2 (volume.restrict S))
    r A.toLinearMap defect l (conformingAmbientControl X obs hobs).adjoint.toLinearMap
    (conformingWeightedState X ρ w) (fun t => (ρ.multiplier w 0 t).seminorm)
    (fun t => (ρ.multiplier w 0 t).seminorm) (conformingWeightedState_definite X ρ w)
    (fun t f => (ρ.seminorm_definite w 0 t f).mp)
    (fun t f => (ρ.seminorm_definite w 0 t f).mp)
    g w hw N.allowed mesh errors hx hx0 hdt hscale
    (by simpa only [CarlemanExponents.heat,pow_one] using haE)
    (by simpa only [CarlemanExponents.heat,Nat.mul_one] using ha0) N.numerical N.continuous
  exact physical_load_carleman_of_transfer ρ w g p rfl r A X.subtype
    (conformingAmbientControl X obs hobs).adjoint.toLinearMap
    (conformingAmbientControl X obs hobs).adjoint.toLinearMap
    X.orthogonalProjectionOnto.toLinearMap CCE (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) he.1

end Carleman.Physical
