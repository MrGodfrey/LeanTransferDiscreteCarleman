module

public import Carleman.Control.ConformingPhysicalObservation
public import Carleman.Control.ConformingRegionControl
public import Carleman.Control.RelaxedControl

/-! Actual L2(omega) observation and HUM controls on finite conforming subspaces,
conditional only on the stated periodic load Carleman supply. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}

theorem conforming_observation_control_uniform (ρ : SpatialProfile ν)
    (ω : Set Ω) (hω : MeasurableSet ω) (β qc CCE rstar : ℝ)
    (hβ : 0 < β) (hqc : 1 ≤ qc) (hCCE : 0 ≤ CCE) (hrstar : 0 < rstar)
    (hneg : ∀ᵐ x ∂ν, ρ.value x ≤ -rstar) :
    ∃ Cb d0 : ℝ, 0 < Cb ∧ 0 < d0 ∧ ∀ (T M : ℝ), 0 < T → 0 ≤ M →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : Submodule ℝ (Lp E 2 ν)) [FiniteDimensional ℝ X]
        (g : TimeGrid), g.period = T → ∀ S : ℝ,
        16*physicalBaseAmplitude Cb qc T M ≤ S →
        S ≤ physicalBaseAmplitude Cb qc T M*T/(4*g.dt) →
        g.dt*M ≤ 1/2 → g.dt ≤ T/12 →
        ∀ (A : X →L[ℝ] X), A.IsSymmetric → (∀ x, 0 ≤ inner ℝ (A x) x) →
        ∀ (b : Fin g.steps → BoundedMultiplier ν), (∀ i, (b i).bound ≤ M) →
        (∀ w : TimeWeight, PhysicalQClass w g.period β qc → w.max ≤ S →
          PhysicalLoadCarleman ρ w g A X.subtype
            (conformingAmbientControl X ω hω).adjoint.toLinearMap
            X.orthogonalProjectionOnto.toLinearMap CCE) →
        (∀ p : Fin (g.steps+1) → X,
          AdjointEquation g.dt (fun i => A+conformingPotential X (b i)) p →
          ‖p 0‖^2 ≤ C*((g.dt*∑ i : Fin g.steps,
            ‖(conformingRegionControl X ω).adjoint (p i.castSucc)‖^2)+
            Real.exp (-2*d0*S)*‖p (Fin.last g.steps)‖^2)) ∧
        (∀ y0 : X, ∃ u : Fin g.steps → Lp E 2 (ν.restrict ω),
          ∃ y : Fin (g.steps+1) → X, y 0 = y0 ∧
            ForwardEquation g.dt (fun i => A+conformingPotential X (b i))
              (conformingRegionControl X ω) u y ∧
            controlNorm g.dt u ≤ Real.sqrt C*‖y0‖ ∧
            ‖y (Fin.last g.steps)‖ ≤ Real.sqrt C*Real.exp (-d0*S)*‖y0‖) := by
  obtain ⟨Cb,d0,hCb,hd0,huniform⟩ := conforming_physical_observation_uniform (E := E) ρ ω hω β qc CCE rstar
    hβ hqc hCCE hrstar hneg
  refine ⟨Cb,d0,hCb,hd0,?_⟩
  intro T M hT hM
  obtain ⟨C,hC,hdata⟩ := huniform T M hT hM
  refine ⟨C,hC,?_⟩
  intro X _ g hg S hS hmesh hsmall hdt A hAs hA b hb hce
  have hobs (p : Fin (g.steps+1) → X)
      (hp : AdjointEquation g.dt (fun i => A+conformingPotential X (b i)) p) :
      ‖p 0‖^2 ≤ C*((g.dt*∑ i : Fin g.steps,
        ‖(conformingRegionControl X ω).adjoint (p i.castSucc)‖^2)+
        Real.exp (-2*d0*S)*‖p (Fin.last g.steps)‖^2) := by
    simpa only [conforming_region_observation_norm X ω hω] using
      hdata X g hg S hS hmesh hsmall hdt A hAs hA b hb hce p hp
  refine ⟨hobs,?_⟩
  exact relaxed_control_of_observation g M d0 S C hsmall hC.le A hAs hA
    (fun i => conformingPotential X (b i)) (fun i => conformingPotential_symmetric X (b i))
    (fun i => (conformingPotential_norm X (b i)).trans (hb i))
    (conformingRegionControl X ω) hobs

end Carleman.Physical
