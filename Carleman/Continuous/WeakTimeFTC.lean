module

public import Carleman.Continuous.WeakTimePrimitive

/-! The fundamental theorem for the original continuous H-valued weak
trajectory, including both endpoint traces. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Weak H¹ trajectories satisfy the Bochner integral formula everywhere on [0,T]. -/
theorem HasWeakTimeDerivative.integral_eq {g : TimeGrid} {u du : ℝ → H}
    (hw : HasWeakTimeDerivative g u du) (hu : ContinuousOn u (Icc 0 g.period))
    (hd : MemLp du 2 g.timeMeasure) (t : ℝ) (ht : t ∈ Icc 0 g.period) :
    u t - u 0 = ∫ x in 0..t, du x := by
  let F : ℝ → H := fun t => ∫ x in 0..t, du x
  have hFc : ContinuousOn F (Icc 0 g.period) := TimeGrid.primitive_continuousOn hd
  have hFw : HasWeakTimeDerivative g F du := HasWeakTimeDerivative.primitive hd
  have hz : HasWeakTimeDerivative g (fun t => u t - F t) (fun _ => 0) := by
    intro φ hφ hcφ hsφ
    have hφLp := g.memLp_of_continuousOn (hφ.continuous_deriv (by simp)).continuousOn
    have hui : Integrable (fun t => deriv φ t • u t) g.timeMeasure :=
      memLp_one_iff_integrable.mp (hφLp.smul (g.memLp_of_continuousOn hu))
    have hFi : Integrable (fun t => deriv φ t • F t) g.timeMeasure :=
      memLp_one_iff_integrable.mp (hφLp.smul (g.memLp_of_continuousOn hFc))
    simp_rw [smul_sub]
    rw [integral_sub hui hFi, hw φ hφ hcφ hsφ, hFw φ hφ hcφ hsφ]
    simp
  have he := hz.const_of_zero (hu.sub hFc) t ht
  change u t - F t = u 0 - F 0 at he
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  rw [hF0, sub_zero] at he
  exact (sub_eq_iff_eq_add.mp he ▸ add_sub_cancel_left (u 0) (F t))

/-- Integrals between any two trace points recover their actual difference. -/
theorem HasWeakTimeDerivative.integral_eq_sub {g : TimeGrid} {u du : ℝ → H}
    (hw : HasWeakTimeDerivative g u du) (hu : ContinuousOn u (Icc 0 g.period))
    (hd : MemLp du 2 g.timeMeasure) {a b : ℝ}
    (ha : a ∈ Icc 0 g.period) (hb : b ∈ Icc 0 g.period) :
    (∫ x in a..b, du x) = u b - u a := by
  have hi := TimeGrid.intervalIntegrable_of_memLp hd
  have hia : IntervalIntegrable du volume 0 a := hi.mono_set (by
    rw [uIcc_of_le g.period_pos.le, uIcc_of_le ha.1]
    exact Icc_subset_Icc le_rfl ha.2)
  have hib : IntervalIntegrable du volume 0 b := hi.mono_set (by
    rw [uIcc_of_le g.period_pos.le, uIcc_of_le hb.1]
    exact Icc_subset_Icc le_rfl hb.2)
  have he := intervalIntegral.integral_add_adjacent_intervals hia (hia.symm.trans hib)
  rw [← hw.integral_eq hu hd a ha, ← hw.integral_eq hu hd b hb] at he
  calc
    _ = (u b - u 0) - (u a - u 0) := eq_sub_of_add_eq' he
    _ = u b - u a := by abel

end Carleman
