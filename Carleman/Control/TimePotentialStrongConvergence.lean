module

public import Carleman.Control.TimePotentialSlices
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Original finite-element time averages converge strongly without spatial refinement. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]

theorem timeAveragedPotential_strong_convergence (T : ℝ) (hTpos : 0 ≤ T)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν)) :
    Tendsto (fun n => (fixedTimePotential T (g n) (hT n) b).toL2) atTop (𝓝 b.toL2) := by
  let μ := volume.restrict (Ioc 0 T)
  let β n := fixedTimePotential T (g n) (hT n) b
  let F (n : ℕ) (x : Ω) := ∫ t, ((β n).value (t,x)-b.value (t,x))^2 ∂μ
  have hvol : μ.real univ=T := by
    simp only [μ,Measure.real,Measure.restrict_apply_univ]
    rw [← Measure.real,Real.volume_real_Ioc_of_le hTpos,sub_zero]
  have hmeas n : AEStronglyMeasurable (F n) ν :=
    (((β n).measurable.sub b.measurable).pow 2).prod_swap.integral_prod_right'
  have hpoint n : ∀ᵐ z ∂μ.prod ν, |(β n).value z-b.value z| ≤ 2*b.bound := by
    filter_upwards [(β n).bounded,b.bounded] with z hn hb
    rw [show (β n).bound=b.bound from fixedTimePotential_bound T (g n) (hT n) b] at hn
    exact (abs_sub _ _).trans (by linarith)
  have hbound n : ∀ᵐ x ∂ν, ‖F n x‖ ≤ (2*b.bound)^2*T := by
    have hp := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae (hpoint n))
    filter_upwards [hp] with x hx
    have he : ∀ᵐ t ∂μ, ‖((β n).value (t,x)-b.value (t,x))^2‖ ≤ (2*b.bound)^2 := by
      filter_upwards [hx] with t ht
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs,Prod.swap] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) b.bound_nonneg)).mpr ht
    simpa only [hvol] using norm_integral_le_of_norm_le_const he
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 0) :=
    fixedTimePotential_slice_error_tendsto T hTpos g hT htlim b
  have hint := tendsto_integral_of_dominated_convergence (f := fun _ => (0:ℝ))
    (fun _ : Ω => (2*b.bound)^2*T) hmeas (integrable_const _) hbound hlim
  have hid n : ‖(β n).toL2-b.toL2‖^2=∫ x, F n x ∂ν := by
    rw [BoundedMultiplier.toL2_sub_norm_sq]
    exact integral_prod_symm _ ((β n).sub_sq_integrable b)
  have hsq : Tendsto (fun n => ‖(β n).toL2-b.toL2‖^2) atTop (𝓝 0) := by
    simp_rw [hid]
    simpa only [integral_zero] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun n => Real.sqrt (‖(β n).toL2-b.toL2‖^2)) atTop (𝓝 (Real.sqrt 0)) at hh
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

end Carleman
