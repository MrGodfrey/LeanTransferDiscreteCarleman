module

public import Carleman.Control.ConformingPhysicalOperators

/-! Orthogonal L2 realizations discharge the mass, load, potential and actual
control-adjoint interfaces of the physical observation bridge. CE remains explicit. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}

theorem conforming_physical_observation_uniform (ρ : SpatialProfile ν)
    (ω : Set Ω) (hω : MeasurableSet ω) (β qc CCE rstar : ℝ)
    (hβ : 0 < β) (hqc : 1 ≤ qc) (hCCE : 0 ≤ CCE) (hrstar : 0 < rstar)
    (hneg : ∀ᵐ x ∂ν, ρ.value x ≤ -rstar) :
    ∃ Cb d0 : ℝ, 0 < Cb ∧ 0 < d0 ∧ ∀ (T M : ℝ), 0 < T → 0 ≤ M →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : Submodule ℝ (Lp E 2 ν)) [CompleteSpace X]
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
        ∀ p : Fin (g.steps+1) → X,
          AdjointEquation g.dt (fun i => A+conformingPotential X (b i)) p →
          ‖p 0‖^2 ≤ C*((g.dt*∑ i : Fin g.steps,
            ‖(conformingAmbientControl X ω hω).adjoint (p i.castSucc)‖^2)+
            Real.exp (-2*d0*S)*‖p (Fin.last g.steps)‖^2) := by
  obtain ⟨Cb,d0,hCb,hd0,huniform⟩ := physical_observation_uniform_of_load_carleman
    (E := E) ρ β qc 1 CCE 1 rstar hβ hqc (by norm_num) hCCE (by norm_num) hrstar hneg
  refine ⟨Cb,d0,hCb,hd0,?_⟩
  intro T M hT hM
  obtain ⟨C,hC,hdata⟩ := huniform T M hT hM
  refine ⟨C,hC,?_⟩
  intro X _ g hg S hS hmesh hsmall hdt A hAs hA b hb hce p hp
  exact hdata X g hg S hS hmesh hsmall hdt A hAs hA
    (fun i => conformingPotential X (b i))
    (fun i => conformingPotential_symmetric X (b i))
    (fun i => (conformingPotential_norm X (b i)).trans (hb i))
    X.subtype X.subtype (conformingAmbientControl X ω hω).adjoint.toLinearMap
    X.orthogonalProjectionOnto.toLinearMap b hb (fun _ _ => rfl)
    (conforming_load_right_inverse X) (fun _ => by simp) (fun _ => by simp)
    (fun w hw hmax => ⟨fun _ _ => by simp,hce w hw hmax⟩) p hp

end Carleman.Physical
