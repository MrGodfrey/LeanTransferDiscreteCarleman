module

public import Carleman.Control.PhysicalObservationUniform

/-! Observation constants chosen before all varying spatial measures and profiles. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
universe u v x
namespace Carleman.Physical
theorem physical_observation_uniform_profiles (Rbound β qc CI CCE Cmass rstar : ℝ) (hβ : 0 < β) (hqc : 1 ≤ qc)
    (hCI : 0 ≤ CI) (hCCE : 0 ≤ CCE) (hC : 0 < Cmass) (hrstar : 0 < rstar) :
    ∃ Cb d0 : ℝ, 0 < Cb ∧ 0 < d0 ∧ ∀ (T M : ℝ), 0 < T → 0 ≤ M →
      ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) (E : Type v)
        [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : SpatialProfile ν),
        ρ.bound = Rbound → (∀ᵐ y ∂ν, ρ.value y ≤ -rstar) →
      ∀ (X : Type x) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
        (g : TimeGrid), g.period = T → ∀ S : ℝ,
        16*physicalBaseAmplitude Cb qc T M ≤ S →
        S ≤ physicalBaseAmplitude Cb qc T M*T/(4*g.dt) →
        g.dt*M ≤ 1/2 → g.dt ≤ T/12 →
        ∀ (A : X →L[ℝ] X), A.IsSymmetric → (∀ x, 0 ≤ inner ℝ (A x) x) →
        ∀ (V : Fin g.steps → X →L[ℝ] X),
        (∀ i, (V i).IsSymmetric) → (∀ i, ‖V i‖ ≤ M) →
        ∀ (R I Bstar : X →ₗ[ℝ] Lp E 2 ν) (Γ : Lp E 2 ν →ₗ[ℝ] X)
          (b : Fin g.steps → BoundedMultiplier ν),
        (∀ i, (b i).bound ≤ M) → (∀ i x, Γ ((b i).map (R x)) = V i x) →
        (∀ x, Γ (I x) = x) → (∀ x, ‖R x‖^2 ≤ Cmass*‖x‖^2) →
        (∀ x, ‖x‖^2 ≤ Cmass*‖R x‖^2) →
        (∀ w : TimeWeight, PhysicalQClass w g.period β qc → w.max ≤ S →
          (∀ i x, (ρ.multiplier w 0 (g.nodeTime i)).seminorm (I x) ≤
            CI*(ρ.multiplier w 0 (g.nodeTime i)).seminorm (R x)) ∧
          PhysicalLoadCarleman ρ w g A R Bstar Γ CCE) →
        ∀ p : Fin (g.steps+1) → X, AdjointEquation g.dt (fun i => A+V i) p →
          ‖p 0‖^2 ≤ C*((g.dt*∑ i : Fin g.steps, ‖Bstar (p i.castSucc)‖^2)+
            Real.exp (-2*d0*S)*‖p (Fin.last g.steps)‖^2) := by
  obtain ⟨Cb,hCb,hCmin,hweights⟩ := physical_qclass_uniform β qc (max 2 (32*CCE)) hβ hqc
  have hc2 : 2 ≤ Cb := (le_max_left _ _).trans hCmin
  have hcCE : 32*CCE ≤ Cb := (le_max_right _ _).trans hCmin
  let d0 := physicalEndpointRate rstar/4
  have hd0 : 0 < d0 := div_pos (physicalEndpointRate_pos rstar hrstar) (by norm_num)
  refine ⟨Cb,d0,hCb,hd0,?_⟩
  intro T M hT hM
  let qb := physicalBaseAmplitude Cb qc T M
  have hq2 := (physicalBaseAmplitude_ge_two Cb qc T M hc2 hqc hT hM).1
  refine ⟨physicalObservationConstant Rbound T M qb Cmass CI CCE rstar,
    physicalObservationConstant_pos Rbound T M qb Cmass CI CCE rstar hT
      (by linarith only [hq2]) hC hCCE hrstar,?_⟩
  intro Ω _ ν E _ _ ρ hR hneg X _ _ _ g hg S hS hmesh hsmall hdt A hAs hA V hVs hV R I Bstar Γ b hb hpot hI hRu hRl hce p hp
  subst T
  obtain ⟨w,hw,hwmax,hwclass,_⟩ := hweights g M S hM hS hmesh
  obtain ⟨hIw,hCE⟩ := hce w hwclass hwmax.le
  obtain ⟨hδ,hδs,_⟩ := physical_delta_conditions g qb S hq2 hS hmesh
  have habs (i : Fin g.steps) : 2*CCE*M^2 ≤ w.q (g.nodeTime i)^3/2 := by
    rw [hw]
    exact physical_potential_budget Cb qc g.period M (qb/S) CCE (g.nodeTime i)
      (by linarith only [hc2]) hcCE hqc g.period_pos hM hδ hδs
  have hSym (i : Fin g.steps) : (A+V i).IsSymmetric := hAs.add (hVs i)
  have hL (i : Fin g.steps) (x : X) : -M*‖x‖^2 ≤ inner ℝ ((A+V i) x) x :=
    stiffness_potential_lower A.toLinearMap (V i).toLinearMap M hA
      (fun z => ((V i).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hV i) (norm_nonneg z))) x
  have hh := physical_observation_of_load_carleman ρ w g qb S M CI CCE Cmass rstar
    hq2 hS hmesh hM hsmall hdt hCI hCCE hC hrstar hneg hw habs
    A V hSym hL R I Bstar Γ b hb hpot hI hIw hRu hRl hCE p hp
  have hd : -2*d0*S = -(physicalEndpointRate rstar/2)*S := by dsimp only [d0]; ring
  simpa only [hd,hR] using hh

end Carleman.Physical
