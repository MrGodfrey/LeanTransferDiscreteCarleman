module

public import Carleman.Control.GalerkinHeatData

/-! Physical observation and real regional HUM for the actual Galerkin
stiffness, from the remaining original analytic approximation/test data. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set
open scoped BigOperators
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
/-- The periodic discrete CE is derived internally from original Corollary 2.3.
All numerical spaces and data follow the uniform constants. -/
theorem galerkin_heat_observation_control_uniform
    (Cap Creg c C Ccomm β τStar Ctime Csuper δnum Cce qc rstar : ℝ)
    (hCap : 0 ≤ Cap) (hc : 0 < c) (hC : 0 ≤ C) (hCc : 0 ≤ Ccomm) (hβ : 0 < β) (hτ : 0 ≤ τStar)
    (hCt : 0 ≤ Ctime) (hCs : 0 ≤ Csuper) (hδ : 0 < δnum) (hCce : 0 ≤ Cce)
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
        ∀ errors : ErrorScales,
        errors.aE ≤ Cap*mesh → errors.a₀+errors.ηA ≤ Cap*mesh^2 →
        (∀ w : TimeWeight, PhysicalQClass w g.period β qc → w.max ≤ Smax →
          GalerkinHeatData a hD ρ P obs hobs X hX g w
            c C Ccomm τStar Ctime Csuper Cce mesh errors) →
        ∀ (b : Fin g.steps → BoundedMultiplier (volume.restrict S)), (∀ i, (b i).bound ≤ M) →
        (∀ p : Fin (g.steps+1) → X,
          AdjointEquation g.dt (fun i => galerkinStiffness a X hX+conformingPotential X (b i)) p →
          ‖p 0‖^2 ≤ Cphys*((g.dt*∑ i : Fin g.steps,
            ‖(conformingRegionControl X obs).adjoint (p i.castSucc)‖^2)+
            Real.exp (-2*d0*Smax)*‖p (Fin.last g.steps)‖^2)) ∧
        (∀ y0 : X, ∃ u : Fin g.steps → Lp ℝ 2 ((volume.restrict S).restrict obs),
          ∃ y : Fin (g.steps+1) → X, y 0 = y0 ∧
            ForwardEquation g.dt (fun i => galerkinStiffness a X hX+conformingPotential X (b i))
              (conformingRegionControl X obs) u y ∧
            controlNorm g.dt u ≤ Real.sqrt Cphys*‖y0‖ ∧
            ‖y (Fin.last g.steps)‖ ≤ Real.sqrt Cphys*Real.exp (-d0*Smax)*‖y0‖) := by
  obtain ⟨κ,h0,Δ0,Cb,d0,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,ht⟩ :=
    conforming_heat_observation_control_uniform hΩ a hD ρ hρ P obs hobs
      Cap Creg c C Ccomm β τStar Ctime Csuper δnum 1 Cce qc rstar
      hCap hc hC hCc hβ hτ hCt hCs hδ (by norm_num) hCce hcover hell hqc hrstar hneg
  refine ⟨κ,h0,Δ0,Cb,d0,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,?_⟩
  intro T M hT hM
  obtain ⟨Cphys,hCphys,hdata⟩ := ht T M hT hM
  refine ⟨Cphys,hCphys,?_⟩
  intro X _ hX g hg mesh hx hx0 hdt Smax hS hmesh hsmall hdtT errors haE ha0 N b hb
  exact hdata X hX g hg mesh hx hx0 hdt hS hmesh hsmall hdtT
    (galerkinStiffness a X hX) (galerkinStiffness_symmetric a X hX)
    (galerkinStiffness_nonneg a X hX) 0 errors haE ha0
    (fun w hw hmax => (N w hw hmax).toConforming a hD ρ P obs hobs X hX g w
      c C Ccomm τStar Ctime Csuper Cce mesh errors) b hb

end Carleman.Physical
