module

public import Carleman.Control.PhysicalWeightLocalization
public import Carleman.Control.PhysicalCutoffEnergy

/-! The original delta=qb/S choice and its genuine mesh consequences. -/
@[expose] public noncomputable section
namespace Carleman.Physical

theorem physical_delta_conditions (g : TimeGrid) (qb S : ℝ) (hqb : 2 ≤ qb)
    (hS : 16*qb ≤ S) (hmesh : S ≤ qb*g.period/(4*g.dt)) :
    0 < qb/S ∧ qb/S ≤ 1/16 ∧ qb/(qb/S) = S ∧
    Real.sqrt (1+(qb/S)^2) ≤ qb ∧ 0 < (qb/S)*g.period ∧
    (qb/S)*g.period ≤ g.period/16 ∧ g.dt ≤ ((qb/S)*g.period)/4 := by
  have hq : 0 < qb := by linarith only [hqb]
  have hs : 0 < S := by linarith only [hq,hS]
  have hd : 0 < qb/S := div_pos hq hs
  have hdu : qb/S ≤ 1/16 := (div_le_iff₀ hs).mpr (by linarith only [hS])
  have hid : qb/(qb/S) = S := by field_simp
  have hroot : Real.sqrt (1+(qb/S)^2) ≤ qb := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hq.le).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith only [hd,hdu,hqb]
  have harea := mul_le_mul_of_nonneg_right hdu g.period_pos.le
  have hstep : g.dt ≤ ((qb/S)*g.period)/4 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 4) g.dt_pos)).mp hmesh
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hs).mpr
    nlinarith only [hh]
  refine ⟨hd,hdu,hid,hroot,mul_pos hd g.period_pos,?_,hstep⟩
  nlinarith only [harea]

theorem physical_transition_weight (g : TimeGrid) (qb S : ℝ) (hqb : 2 ≤ qb)
    (hS : 16*qb ≤ S) (hmesh : S ≤ qb*g.period/(4*g.dt)) (i : Fin g.steps)
    (hi : i ∈ transitionNodes g ((qb/S)*g.period)) :
    S/Real.sqrt (1+9*Real.pi^2) ≤ physicalWeight qb (qb/S) g.period ((i.val:ℝ)*g.dt) := by
  obtain ⟨hd,_,hid,_,ha,_,hdt⟩ := physical_delta_conditions g qb S hqb hS hmesh
  have hloc := cutoffNodes_transition_location g ((qb/S)*g.period) ha i (Finset.mem_filter.mp hi).2
  have hn : endpointDistance g.period ((i.val:ℝ)*g.dt) ≤ 3*(qb/S)*g.period := by
    rcases hloc with hl | hr
    · have hh := min_le_left ((i.val:ℝ)*g.dt) (g.period-(i.val:ℝ)*g.dt)
      dsimp only [endpointDistance]
      nlinarith only [hl,hh,hdt,ha]
    · have hh := min_le_right ((i.val:ℝ)*g.dt) (g.period-(i.val:ℝ)*g.dt)
      dsimp only [endpointDistance]
      nlinarith only [hr,hh,hdt,ha]
  have hh := physicalWeight_near_endpoint qb (qb/S) g.period ((i.val:ℝ)*g.dt)
    (by linarith only [hqb]) hd g.period_pos (g.nodeTime_nonneg i) (g.nodeTime_lt_period i).le hn
  simpa only [hid] using hh

theorem physical_weight_endpoint_decay (g : TimeGrid) (qb S r rstar : ℝ) (hqb : 2 ≤ qb)
    (hS : 16*qb ≤ S) (hmesh : S ≤ qb*g.period/(4*g.dt)) (hrstar : 0 < rstar) (hr : r ≤ -rstar)
    (i : Fin g.steps) (hi : i ∈ transitionNodes g ((qb/S)*g.period)) :
    Real.exp (physicalWeight qb (qb/S) g.period ((i.val:ℝ)*g.dt)*r)^2 ≤
      Real.exp (-(2*rstar/Real.sqrt (1+9*Real.pi^2))*S) := by
  have hq := physical_transition_weight g qb S hqb hS hmesh i hi
  have hC : 0 < Real.sqrt (1+9*Real.pi^2) := Real.sqrt_pos.mpr (by positivity)
  have hs : 0 ≤ S := by linarith only [hS,hqb]
  have hqp : 0 ≤ physicalWeight qb (qb/S) g.period ((i.val:ℝ)*g.dt) :=
    (div_nonneg hs hC.le).trans hq
  rw [pow_two,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left hr hqp
  have h2 := mul_le_mul_of_nonneg_right hq hrstar.le
  have he : (2*rstar/Real.sqrt (1+9*Real.pi^2))*S = 2*(S/Real.sqrt (1+9*Real.pi^2))*rstar := by ring
  rw [neg_mul,he]
  nlinarith only [h1,h2]

end Carleman.Physical
