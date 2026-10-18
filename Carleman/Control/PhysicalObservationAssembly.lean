module

public import Carleman.Control.PhysicalLoadCarleman

/-! Physical relaxed observation from an explicit actual periodic load estimate.
The constant is independent of the grid once T, M and qb are fixed. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman.Physical

def physicalEndpointRate (rstar : ℝ) : ℝ := 2*rstar/Real.sqrt (1+9*Real.pi^2)

theorem physicalEndpointRate_pos (rstar : ℝ) (hrstar : 0 < rstar) : 0 < physicalEndpointRate rstar :=
  div_pos (mul_pos (by norm_num) hrstar) (Real.sqrt_pos.mpr (by positivity))

def physicalInitialFactor (R T M qb : ℝ) : ℝ := Real.exp (-4*R*qb)*(T/6)*Real.exp (-4*M*T)

theorem physicalInitialFactor_pos (R T M qb : ℝ) (hT : 0 < T) :
    0 < physicalInitialFactor R T M qb := by
  exact mul_pos (mul_pos (Real.exp_pos _) (div_pos hT (by norm_num))) (Real.exp_pos _)

def physicalRemainderFactor (T M qb Cmass rstar : ℝ) : ℝ :=
  (10*Cmass/(physicalEndpointRate rstar*qb*T))*Real.exp (4*M*T)

def physicalObservationConstant (R T M qb Cmass CI CCE rstar : ℝ) : ℝ :=
  (Cmass/physicalInitialFactor R T M qb)*
    (4*CCE*CI^2*physicalRemainderFactor T M qb Cmass rstar+2*CCE*(6/rstar^3)+1)

theorem physicalObservationConstant_pos (R T M qb Cmass CI CCE rstar : ℝ)
    (hT : 0 < T) (hqb : 0 < qb) (hC : 0 < Cmass) (hCE : 0 ≤ CCE) (hrstar : 0 < rstar) :
    0 < physicalObservationConstant R T M qb Cmass CI CCE rstar := by
  have hr : 0 ≤ physicalRemainderFactor T M qb Cmass rstar :=
    mul_nonneg (div_nonneg (by positivity)
      (mul_pos (mul_pos (physicalEndpointRate_pos rstar hrstar) hqb) hT).le) (Real.exp_pos _).le
  unfold physicalObservationConstant
  apply mul_pos (div_pos hC (physicalInitialFactor_pos R T M qb hT))
  have h1 : 0 ≤ 4*CCE*CI^2*physicalRemainderFactor T M qb Cmass rstar := by positivity
  have h2 : 0 ≤ 2*CCE*(6/rstar^3) := by positivity
  linarith only [h1,h2]

variable {Ω E X : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {ν : Measure Ω}

theorem physical_observation_of_load_carleman (ρ : SpatialProfile ν) (w : TimeWeight) (g : TimeGrid)
    (qb S M CI CCE Cmass rstar : ℝ) (hqb : 2 ≤ qb) (hS : 16*qb ≤ S)
    (hmesh : S ≤ qb*g.period/(4*g.dt)) (hM : 0 ≤ M) (hsmall : g.dt*M ≤ 1/2)
    (hdt : g.dt ≤ g.period/12) (hCI : 0 ≤ CI) (hCCE : 0 ≤ CCE) (hC : 0 < Cmass)
    (hrstar : 0 < rstar) (hneg : ∀ᵐ x ∂ν, ρ.value x ≤ -rstar)
    (hw : w.q = physicalWeight qb (qb/S) g.period)
    (habs : ∀ i : Fin g.steps, 2*CCE*M^2 ≤ w.q (g.nodeTime i)^3/2)
    (A : X →L[ℝ] X) (V : Fin g.steps → X →L[ℝ] X) (hSym : ∀ i, (A+V i).IsSymmetric)
    (hL : ∀ i x, -M*‖x‖^2 ≤ inner ℝ ((A+V i) x) x)
    (R I Bstar : X →ₗ[ℝ] Lp E 2 ν) (Γ : Lp E 2 ν →ₗ[ℝ] X)
    (b : Fin g.steps → BoundedMultiplier ν) (hb : ∀ i, (b i).bound ≤ M)
    (hpot : ∀ i x, Γ ((b i).map (R x)) = V i x) (hI : ∀ x, Γ (I x) = x)
    (hIw : ∀ i x, (ρ.multiplier w 0 (g.nodeTime i)).seminorm (I x) ≤
      CI*(ρ.multiplier w 0 (g.nodeTime i)).seminorm (R x))
    (hRu : ∀ x, ‖R x‖^2 ≤ Cmass*‖x‖^2) (hRl : ∀ x, ‖x‖^2 ≤ Cmass*‖R x‖^2)
    (hce : PhysicalLoadCarleman ρ w g A R Bstar Γ CCE)
    (p : Fin (g.steps+1) → X) (hp : AdjointEquation g.dt (fun i => A+V i) p) :
    ‖p 0‖^2 ≤ physicalObservationConstant ρ.bound g.period M qb Cmass CI CCE rstar*
      ((g.dt*∑ i : Fin g.steps, ‖Bstar (p i.castSucc)‖^2)+
        Real.exp (-(physicalEndpointRate rstar/2)*S)*‖p (Fin.last g.steps)‖^2) := by
  obtain ⟨hδ,hδs,_,_,ha,_,_⟩ := physical_delta_conditions g qb S hqb hS hmesh
  have hp' := (adjoint_equation_iff (ne_of_gt g.dt_pos) (fun i => A+V i) hSym p).mp hp
  have he := cutoff_carleman_absorb ρ w g ((qb/S)*g.period) M CI CCE ha hM hCI hCCE habs
    A V hSym R I Bstar Γ b hb hpot hI hIw hce p hp
  have hr := physical_weighted_remainder_decay ρ w g M hM hsmall
    (fun i => (A+V i).toLinearMap) hL p hp' qb S rstar Cmass hqb hS hmesh hrstar hneg hw hC.le R hRu
  have hi := physical_weighted_initial_recovery ρ w g M hM hsmall
    (fun i => (A+V i).toLinearMap) hL p hp' qb (qb/S) Cmass
    (by linarith only [hqb]) hδ hδs hdt hw hC.le R hRl
  have ho := cutoff_observation_budget ρ w g ((qb/S)*g.period) rstar hrstar hneg Bstar p
  let energy := physicalWeightedCubeSq ρ w g
    (fun i => R (cutoffState g (cutoffNodes g ((qb/S)*g.period)) p i))
  let obs := g.dt*∑ i : Fin g.steps, ‖Bstar (p i.castSucc)‖^2
  let tail := Real.exp (-(physicalEndpointRate rstar/2)*S)*‖p (Fin.last g.steps)‖^2
  let K := physicalInitialFactor ρ.bound g.period M qb
  let a := 4*CCE*CI^2*physicalRemainderFactor g.period M qb Cmass rstar
  let bcoef := 2*CCE*(6/rstar^3)
  have hK : 0 < K := physicalInitialFactor_pos ρ.bound g.period M qb g.period_pos
  have hobs : 0 ≤ obs := mul_nonneg g.dt_pos.le (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have htail : 0 ≤ tail := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have ha0 : 0 ≤ a := by
    have hq : 0 < qb := by linarith only [hqb]
    have hr0 : 0 ≤ physicalRemainderFactor g.period M qb Cmass rstar :=
      mul_nonneg (div_nonneg (by positivity)
        (mul_pos (mul_pos (physicalEndpointRate_pos rstar hrstar) hq) g.period_pos).le) (Real.exp_pos _).le
    dsimp only [a]
    positivity
  have hb0 : 0 ≤ bcoef := by dsimp only [bcoef]; positivity
  have henergy : energy ≤ a*tail+bcoef*obs := by
    have hrr := mul_le_mul_of_nonneg_left hr
      (show 0 ≤ 4*CCE*CI^2 by positivity)
    have hoo := mul_le_mul_of_nonneg_left ho (show 0 ≤ 2*CCE by positivity)
    have hall := he.trans (add_le_add hrr hoo)
    simpa only [energy,a,bcoef,tail,obs,physicalWeightedSq,physicalRemainderFactor,
      physicalEndpointRate,mul_assoc] using hall
  have hinit : K*‖p 0‖^2 ≤ Cmass*energy := by
    simpa only [K,energy,physicalInitialFactor,physicalWeightedCubeSq,mul_assoc] using hi
  have hn : ‖p 0‖^2 ≤ (Cmass/K)*energy := by
    have hh : ‖p 0‖^2 ≤ (Cmass*energy)/K :=
      (le_div_iff₀ hK).mpr (by simpa only [mul_comm] using hinit)
    simpa only [div_mul_eq_mul_div] using hh
  have hsum : a*tail+bcoef*obs ≤ (a+bcoef+1)*(obs+tail) := by
    nlinarith only [mul_nonneg ha0 hobs,mul_nonneg hb0 htail,hobs,htail]
  have hfinal := hn.trans (mul_le_mul_of_nonneg_left (henergy.trans hsum) (div_pos hC hK).le)
  simpa only [physicalObservationConstant,K,a,bcoef,obs,tail,mul_assoc] using hfinal

end Carleman.Physical
