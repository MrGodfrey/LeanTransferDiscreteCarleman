module

public import Carleman.Continuous.WeakTimeFTC
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Absolute continuity and the energy identity for all original H¹ weak
trajectories, not only Fourier coefficients or classical approximants. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace Carleman

theorem absolutelyContinuous_of_dist_le {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {u : ℝ → E} {v : ℝ → F} {a b : ℝ} (hv : AbsolutelyContinuousOnInterval v a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (u x) (u y) ≤ dist (v x) (v y)) :
    AbsolutelyContinuousOnInterval u a b := by
  apply squeeze_zero' ?_ ?_ hv
  · exact .of_forall fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)
  rw [eventually_inf_principal]
  filter_upwards with p hp
  exact Finset.sum_le_sum fun i hi => h _ (hp.1 i hi).1 _ (hp.1 i hi).2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Absolute continuity follows from the actual Bochner integral formula. -/
theorem HasWeakTimeDerivative.absolutelyContinuous {g : TimeGrid} {u du : ℝ → H}
    (hw : HasWeakTimeDerivative g u du) (hu : ContinuousOn u (Icc 0 g.period))
    (hd : MemLp du 2 g.timeMeasure) : AbsolutelyContinuousOnInterval u 0 g.period := by
  have hi := TimeGrid.intervalIntegrable_of_memLp hd
  let N : ℝ → ℝ := fun t => ∫ x in 0..t, ‖du x‖
  apply absolutelyContinuous_of_dist_le
    (hi.norm.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc)
  intro a ha b hb
  have ha' : a ∈ Icc 0 g.period := by simpa only [uIcc_of_le g.period_pos.le] using ha
  have hb' : b ∈ Icc 0 g.period := by simpa only [uIcc_of_le g.period_pos.le] using hb
  have hia := hi.norm.mono_set (uIcc_subset_uIcc left_mem_uIcc ha)
  have hib := hi.norm.mono_set (uIcc_subset_uIcc left_mem_uIcc hb)
  rw [dist_eq_norm, Real.dist_eq, ← hw.integral_eq_sub hu hd hb' ha',
    intervalIntegral.integral_interval_sub_left hia hib]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- The weak derivative is the a.e. strong H derivative on the open period. -/
theorem HasWeakTimeDerivative.ae_hasDerivAt {g : TimeGrid} {u du : ℝ → H}
    (hw : HasWeakTimeDerivative g u du) (hu : ContinuousOn u (Icc 0 g.period))
    (hd : MemLp du 2 g.timeMeasure) :
    ∀ᵐ t ∂g.timeMeasure, HasDerivAt u (du t) t := by
  have he := (TimeGrid.intervalIntegrable_of_memLp hd).ae_hasDerivAt_integral
  filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  have hder := (ht (by simpa only [uIcc_of_le g.period_pos.le] using
    (show t ∈ Icc 0 g.period from ⟨hmem.1.le, hmem.2.le⟩)) 0 left_mem_uIcc).const_add (u 0)
  apply hder.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with x hx
  have h := hw.integral_eq hu hd x ⟨hx.1.le, hx.2.le⟩
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- The energy chain rule is valid at the actual endpoint traces. -/
theorem HasWeakTimeDerivative.energy_identity {g : TimeGrid} {u du : ℝ → H}
    (hw : HasWeakTimeDerivative g u du) (hu : ContinuousOn u (Icc 0 g.period))
    (hd : MemLp du 2 g.timeMeasure) :
    2 * (∫ t, inner ℝ (u t) (du t) ∂g.timeMeasure) = ‖u g.period‖^2 - ‖u 0‖^2 := by
  have hAC := hw.absolutelyContinuous hu hd
  have hnAC : AbsolutelyContinuousOnInterval (fun t => ‖u t‖) 0 g.period :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hAC
  have hsqAC : AbsolutelyContinuousOnInterval (fun t => ‖u t‖^2) 0 g.period := by
    simpa only [pow_two] using hnAC.fun_mul hnAC
  have he := hsqAC.integral_deriv_eq_sub
  rw [← g.timeIntegral_eq_intervalIntegral] at he
  have hder : (fun t => deriv (fun x => ‖u x‖^2) t) =ᵐ[g.timeMeasure]
      (fun t => 2 * inner ℝ (u t) (du t)) := by
    filter_upwards [hw.ae_hasDerivAt hu hd] with t ht
    exact ht.norm_sq.deriv
  rw [integral_congr_ae hder, integral_const_mul] at he
  exact he

theorem PeriodicWeakTrajectory.time_energy_zero {g : TimeGrid} {D : Submodule ℝ H}
    {A : D →ₗ[ℝ] H} (u : PeriodicWeakTrajectory g D A) :
    (∫ t, inner ℝ (u.value t) (u.derivative t) ∂g.timeMeasure) = 0 := by
  have he := u.weak_derivative.energy_identity u.continuous u.derivative_L2
  rw [u.periodic_trace, sub_self] at he
  linarith

end Carleman
