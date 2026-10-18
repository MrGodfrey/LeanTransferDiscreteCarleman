module

public import Carleman.Control.PhysicalExponentialBudgets

/-! Genuine spatial L2 weights applied to the physical adjoint and cutoff.
Reconstruction mass comparisons are explicit; no observation estimate is assumed. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman.Physical
variable {Ω E X : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {ν : Measure Ω} (ρ : SpatialProfile ν) (w : TimeWeight)
  (g : TimeGrid) (M : ℝ) (hM : 0 ≤ M) (hsmall : g.dt*M ≤ 1/2)
  (L : Fin g.steps → X →ₗ[ℝ] X) (hL : ∀ i x, -M*‖x‖^2 ≤ inner ℝ (L i x) x)
  (p : Fin (g.steps+1) → X) (hp : Adjoint g.dt L p)

include hM hsmall hL hp

theorem physical_weighted_remainder_energy (qb S rstar Cmass : ℝ)
    (hqb : 2 ≤ qb) (hS : 16*qb ≤ S) (hmesh : S ≤ qb*g.period/(4*g.dt))
    (hrstar : 0 < rstar) (hneg : ∀ᵐ x ∂ν, ρ.value x ≤ -rstar)
    (hw : w.q = physicalWeight qb (qb/S) g.period) (hC : 0 ≤ Cmass)
    (R : X →ₗ[ℝ] Lp E 2 ν) (hR : ∀ x, ‖R x‖^2 ≤ Cmass*‖x‖^2) :
    g.dt*(∑ i : Fin g.steps, ((ρ.multiplier w 0 (g.nodeTime i)).seminorm
      (R (cutoffRemainder g (cutoffNodes g ((qb/S)*g.period)) p i)))^2) ≤
      (Cmass*Real.exp (-(2*rstar/Real.sqrt (1+9*Real.pi^2))*S))*
        ((5/((qb/S)*g.period))*Real.exp (4*M*g.period)*‖p (Fin.last g.steps)‖^2) := by
  obtain ⟨_,_,_,_,ha,_,hdt⟩ := physical_delta_conditions g qb S hqb hS hmesh
  have hi (i : Fin g.steps) :
      ((ρ.multiplier w 0 (g.nodeTime i)).seminorm
        (R (cutoffRemainder g (cutoffNodes g ((qb/S)*g.period)) p i)))^2 ≤
      (Cmass*Real.exp (-(2*rstar/Real.sqrt (1+9*Real.pi^2))*S))*
        ‖cutoffRemainder g (cutoffNodes g ((qb/S)*g.period)) p i‖^2 := by
    by_cases hit : i ∈ transitionNodes g ((qb/S)*g.period)
    · have hh := physical_spatial_endpoint ρ w g qb S rstar hqb hS hmesh hrstar hneg hw i hit
        (R (cutoffRemainder g (cutoffNodes g ((qb/S)*g.period)) p i))
      have hrr := mul_le_mul_of_nonneg_left (hR (cutoffRemainder g
        (cutoffNodes g ((qb/S)*g.period)) p i))
        (Real.exp_pos (-(2*rstar/Real.sqrt (1+9*Real.pi^2))*S)).le
      exact hh.trans (by simpa only [mul_left_comm,mul_assoc] using hrr)
    · rw [cutoff_remainder_zero g ((qb/S)*g.period) p i hit,map_zero]
      simp
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)) g.dt_pos.le
  rw [← Finset.mul_sum,mul_left_comm] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    (physical_cutoff_remainder_energy g M hM hsmall L hL p hp ((qb/S)*g.period) ha hdt)
    (mul_nonneg hC (Real.exp_pos _).le))

theorem physical_weighted_remainder_decay (qb S rstar Cmass : ℝ)
    (hqb : 2 ≤ qb) (hS : 16*qb ≤ S) (hmesh : S ≤ qb*g.period/(4*g.dt))
    (hrstar : 0 < rstar) (hneg : ∀ᵐ x ∂ν, ρ.value x ≤ -rstar)
    (hw : w.q = physicalWeight qb (qb/S) g.period) (hC : 0 ≤ Cmass)
    (R : X →ₗ[ℝ] Lp E 2 ν) (hR : ∀ x, ‖R x‖^2 ≤ Cmass*‖x‖^2) :
    let c := 2*rstar/Real.sqrt (1+9*Real.pi^2)
    g.dt*(∑ i : Fin g.steps, ((ρ.multiplier w 0 (g.nodeTime i)).seminorm
      (R (cutoffRemainder g (cutoffNodes g ((qb/S)*g.period)) p i)))^2) ≤
      (10*Cmass/(c*qb*g.period))*Real.exp (4*M*g.period)*
        Real.exp (-(c/2)*S)*‖p (Fin.last g.steps)‖^2 := by
  intro c
  have hc : 0 < c := div_pos (mul_pos (by norm_num) hrstar) (Real.sqrt_pos.mpr (by positivity))
  have hq : 0 < qb := by linarith only [hqb]
  have hs : 0 < S := by linarith only [hS,hqb]
  have hrem := physical_weighted_remainder_energy ρ w g M hM hsmall L hL p hp
    qb S rstar Cmass hqb hS hmesh hrstar hneg hw hC R hR
  have hcoef : 0 ≤ (5*Cmass/(qb*g.period))*Real.exp (4*M*g.period)*‖p (Fin.last g.steps)‖^2 := by
    exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hC)
      (mul_nonneg hq.le g.period_pos.le)) (Real.exp_pos _).le) (sq_nonneg _)
  calc
    _ ≤ (Cmass*Real.exp (-c*S))*
        ((5/((qb/S)*g.period))*Real.exp (4*M*g.period)*‖p (Fin.last g.steps)‖^2) := hrem
    _ = ((5*Cmass/(qb*g.period))*Real.exp (4*M*g.period)*‖p (Fin.last g.steps)‖^2)*
        (S*Real.exp (-c*S)) := by
      field_simp
    _ ≤ ((5*Cmass/(qb*g.period))*Real.exp (4*M*g.period)*‖p (Fin.last g.steps)‖^2)*
        ((2/c)*Real.exp (-(c/2)*S)) :=
      mul_le_mul_of_nonneg_left (linear_exponential_decay c S hc hs.le) hcoef
    _ = _ := by ring

theorem physical_weighted_initial_recovery (qb δ Cmass : ℝ)
    (hqb : 0 ≤ qb) (hδ : 0 < δ) (hδsmall : δ ≤ 1/16) (hdt : g.dt ≤ g.period/12)
    (hw : w.q = physicalWeight qb δ g.period) (hC : 0 ≤ Cmass)
    (R : X →ₗ[ℝ] Lp E 2 ν) (hR : ∀ x, ‖x‖^2 ≤ Cmass*‖R x‖^2) :
    Real.exp (-4*ρ.bound*qb)*((g.period/6)*Real.exp (-4*M*g.period)*‖p 0‖^2) ≤
      Cmass*(g.dt*(∑ i : Fin g.steps, w.q (g.nodeTime i)^3*
        ((ρ.multiplier w 0 (g.nodeTime i)).seminorm
          (R (cutoffState g (cutoffNodes g (δ*g.period)) p i)))^2)) := by
  have ha : 0 < δ*g.period := mul_pos hδ g.period_pos
  have haT : δ*g.period ≤ g.period/16 := by
    have hh := mul_le_mul_of_nonneg_right hδsmall g.period_pos.le
    linarith only [hh]
  have hi (i : Fin g.steps) (hit : i ∈ middleNodes g) :
      Real.exp (-4*ρ.bound*qb)*‖p i.castSucc‖^2 ≤
      Cmass*(w.q (g.nodeTime i)^3*((ρ.multiplier w 0 (g.nodeTime i)).seminorm
        (R (cutoffState g (cutoffNodes g (δ*g.period)) p i)))^2) := by
    have he : cutoffState g (cutoffNodes g (δ*g.period)) p i = p i.castSucc := by
      rw [cutoffState,cutoffNodes_one_middle g (δ*g.period) ha haT i hit,one_smul]
    rw [he]
    have hh := physical_spatial_middle ρ w g qb δ hqb hδ hw i hit (R (p i.castSucc))
    have hr := mul_le_mul_of_nonneg_left (hR (p i.castSucc)) (Real.exp_pos (-4*ρ.bound*qb)).le
    have hc := mul_le_mul_of_nonneg_left hh hC
    have hq : 1 ≤ w.q (g.nodeTime i)^3 := one_le_pow₀ (w.lower _)
    have hpow := mul_le_mul_of_nonneg_right hq
      (sq_nonneg ((ρ.multiplier w 0 (g.nodeTime i)).seminorm (R (p i.castSucc))))
    have hpw := mul_le_mul_of_nonneg_left hpow hC
    nlinarith only [hr,hc,hpw]
  have hmid := mul_le_mul_of_nonneg_left
    (physical_middle_energy g M hM hsmall L hL p hp hdt) (Real.exp_pos (-4*ρ.bound*qb)).le
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hit => hi i hit)) g.dt_pos.le
  rw [← Finset.mul_sum,← Finset.mul_sum] at hsum
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (middleNodes g))
    (fun i _ _ => mul_nonneg (pow_nonneg (w.nonneg (g.nodeTime i)) 3) (sq_nonneg
      ((ρ.multiplier w 0 (g.nodeTime i)).seminorm
        (R (cutoffState g (cutoffNodes g (δ*g.period)) p i)))))
  have hall := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub g.dt_pos.le) hC
  exact hmid.trans (le_trans (by simpa only [mul_left_comm] using hsum) hall)

end Carleman.Physical
