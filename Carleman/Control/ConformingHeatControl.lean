module

public import Carleman.Control.ConformingHeatTransfer

/-! From original analytic/numerical hypotheses to physical observation and
real L2(omega) HUM control, at the original heat mesh scale. Concrete P1
verification and the continuous heat CE remain explicit, not asserted here. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.Physical

def physicalMeshScale (κ mesh dt : ℝ) : ℝ :=
  κ*min (mesh^(-(4/5:ℝ))) (dt^(-(2/5:ℝ)))

theorem physicalMeshScale_pos (κ mesh dt : ℝ) (hκ : 0 < κ) (hx : 0 < mesh) (hdt : 0 < dt) :
    0 < physicalMeshScale κ mesh dt :=
  mul_pos hκ (lt_min (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hdt _))

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
/-- The periodic discrete CE is derived internally from original Corollary 2.3.
All numerical spaces and data follow the uniform constants. -/
theorem conforming_heat_observation_control_uniform
    (Cap Creg c C Ccomm β τStar Ctime Csuper δnum Cnum Cce qc rstar : ℝ)
    (hCap : 0 ≤ Cap) (hc : 0 < c) (hC : 0 ≤ C) (hCc : 0 ≤ Ccomm) (hβ : 0 < β) (hτ : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδ : 0 < δnum) (hCn : 0 ≤ Cnum) (hCce : 0 ≤ Cce)
    (hcover : max (CarlemanExponents.heat.dStar/2) (CarlemanExponents.heat.bStar/2) ≤ τStar)
    (hell : ∀ v : a.model.domain,
      ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖a.model.operator v‖)
    (hqc : 1 ≤ qc) (hrstar : 0 < rstar)
    (hneg : ∀ᵐ x ∂(volume.restrict S), ρ.value x ≤ -rstar) :
    ∃ κ h0 Δ0 Cb d0 : ℝ,
      0 < κ ∧ 0 < h0 ∧ h0 ≤ 1 ∧ 0 < Δ0 ∧ Δ0 ≤ 1 ∧ 0 < Cb ∧ 0 < d0 ∧
      ∀ (T M : ℝ), 0 < T → 0 ≤ M → ∃ Cphys : ℝ, 0 < Cphys ∧
      ∀ (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
        (hX : X ≤ a.V) (g : TimeGrid), g.period = T →
        ∀ mesh : ℝ, 0 < mesh → mesh ≤ h0 → g.dt ≤ Δ0 →
        let Smax := physicalMeshScale κ mesh g.dt
        16*physicalBaseAmplitude Cb qc T M ≤ Smax →
        Smax ≤ physicalBaseAmplitude Cb qc T M*T/(4*g.dt) →
        g.dt*M ≤ 1/2 → g.dt ≤ T/12 →
        ∀ (A : X →L[ℝ] X), A.IsSymmetric → (∀ x, 0 ≤ inner ℝ (A x) x) →
        ∀ (defect : X →ₗ[ℝ] X →ₗ[ℝ] ℝ) (errors : ErrorScales),
        errors.aE ≤ Cap*mesh → errors.a₀+errors.ηA ≤ Cap*mesh^2 →
        (∀ w : TimeWeight, PhysicalQClass w g.period β qc → w.max ≤ Smax →
          ConformingHeatData a hD ρ P obs hobs X hX A defect g w
            c C Ccomm τStar Ctime Csuper Cnum Cce mesh errors) →
        ∀ (b : Fin g.steps → BoundedMultiplier (volume.restrict S)), (∀ i, (b i).bound ≤ M) →
        (∀ p : Fin (g.steps+1) → X,
          AdjointEquation g.dt (fun i => A+conformingPotential X (b i)) p →
          ‖p 0‖^2 ≤ Cphys*((g.dt*∑ i : Fin g.steps,
            ‖(conformingRegionControl X obs).adjoint (p i.castSucc)‖^2)+
            Real.exp (-2*d0*Smax)*‖p (Fin.last g.steps)‖^2)) ∧
        (∀ y0 : X, ∃ u : Fin g.steps → Lp ℝ 2 ((volume.restrict S).restrict obs),
          ∃ y : Fin (g.steps+1) → X, y 0 = y0 ∧
            ForwardEquation g.dt (fun i => A+conformingPotential X (b i))
              (conformingRegionControl X obs) u y ∧
            controlNorm g.dt u ≤ Real.sqrt Cphys*‖y0‖ ∧
            ‖y (Fin.last g.steps)‖ ≤ Real.sqrt Cphys*Real.exp (-d0*Smax)*‖y0‖) := by
  obtain ⟨κ,h0,Δ0,CCE,hκ,hh0,hh01,hΔ0,hΔ01,hCCE,ht⟩ :=
    conforming_heat_load_uniform hΩ a hD ρ hρ P obs hobs
      Cap Creg c C Ccomm β τStar Ctime Csuper δnum Cnum Cce
      hCap hc hC hCc hβ hτ hCt hCs hδ hCn hCce hcover hell
  obtain ⟨Cb,d0,hCb,hd0,hphysical⟩ := conforming_observation_control_uniform (E := ℝ)
    ρ obs hobs β qc CCE rstar hβ hqc hCCE.le hrstar hneg
  refine ⟨κ,h0,Δ0,Cb,d0,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,?_⟩
  intro T M hT hM
  obtain ⟨Cphys,hCphys,hdata⟩ := hphysical T M hT hM
  refine ⟨Cphys,hCphys,?_⟩
  intro X _ hX g hg mesh hx hx0 hdt Smax hS hmesh hsmall hdtT A hAs hA defect errors haE ha0 N b hb
  apply hdata X g hg Smax hS hmesh hsmall hdtT A hAs hA b hb
  intro w hw hmax
  exact ht X hX A defect g w hw.toRegularity mesh errors hx hx0 hdt hmax haE ha0 (N w hw hmax)

end Carleman.Physical
