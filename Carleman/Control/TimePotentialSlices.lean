module

public import Carleman.Control.FixedTimeCellStrongConvergence
public import Carleman.Control.TimePotentialReconstruction
public import Carleman.Control.AveragedPotentialStrongConvergence

/-! Actual time-averaged potential slices and their strong temporal consistency. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace Carleman
namespace BoundedMultiplier
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]

theorem sub_sq_integrable (b c : BoundedMultiplier ν) :
    Integrable (fun x => (b.value x-c.value x)^2) ν := by
  apply (integrable_const ((b.bound+c.bound)^2)).mono' ((b.measurable.sub c.measurable).pow 2)
  filter_upwards [b.bounded,c.bounded] with x hb hc
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  change (b.value x-c.value x)^2 ≤ (b.bound+c.bound)^2
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (add_nonneg b.bound_nonneg c.bound_nonneg)).mpr
      ((abs_sub (b.value x) (c.value x)).trans (add_le_add hb hc))

theorem toL2_sub_norm_sq (b c : BoundedMultiplier ν) :
    ‖b.toL2-c.toL2‖^2=∫ x, (b.value x-c.value x)^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub b.toL2 c.toL2,b.toL2_ae,c.toL2_ae] with x hsub hb hc
  simp only [hsub,Pi.sub_apply,hb,hc,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

end BoundedMultiplier
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]

theorem fixedTimePotential_slice_error (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν)) (x : Ω)
    (u : Lp ℝ 2 (volume.restrict (Ioc 0 T)))
    (hu : u =ᵐ[volume.restrict (Ioc 0 T)] fun t => b.value (t,x)) :
    (∫ t in Ioc 0 T, ((fixedTimePotential T g hT b).value (t,x)-b.value (t,x))^2)=
      ‖fixedTimeCellIsometry T g hT ((fixedTimeCellIsometry T g hT).toContinuousLinearMap.adjoint u)-u‖^2 := by
  let E := fixedTimeCellIsometry T g hT
  have hcoeff i : (E.toContinuousLinearMap.adjoint u) i=
      g.dt⁻¹*∫ t in g.physicalTimeCell i, b.value (t,x) := by
    rw [fixedTimeCellIsometry_adjoint_average]
    apply congrArg (g.dt⁻¹ * ·)
    exact integral_congr_ae (ae_mono (by rw [← hT]; exact g.physicalTimeCell_restrict_le i) hu)
  have hE : (E (E.toContinuousLinearMap.adjoint u) : ℝ → ℝ)=ᵐ[volume.restrict (Ioc 0 T)]
      fun t => (fixedTimePotential T g hT b).value (t,x) := by
    filter_upwards [finiteCellLinear_ae (ν := volume.restrict (Ioc 0 T))
      g.physicalTimeCell (fun _ => measurableSet_Ioc) g.dt_pos (E.toContinuousLinearMap.adjoint u)] with t ht
    change (finiteCellLinear g.physicalTimeCell (fun _ => measurableSet_Ioc) g.dt_pos
      (E.toContinuousLinearMap.adjoint u)) t=_
    rw [ht,fixedTimePotential_value]
    simp only [finiteCellFunction,hcoeff]
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (E (E.toContinuousLinearMap.adjoint u)) u,hE,hu] with t hs he ht
  change _=inner ℝ (((E (E.toContinuousLinearMap.adjoint u)-u : Lp ℝ 2 (volume.restrict (Ioc 0 T))) : ℝ → ℝ) t)
    (((E (E.toContinuousLinearMap.adjoint u)-u : Lp ℝ 2 (volume.restrict (Ioc 0 T))) : ℝ → ℝ) t)
  simp only [hs,Pi.sub_apply,he,ht,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

theorem fixedTimePotential_slice_error_tendsto (T : ℝ) (hTpos : 0 ≤ T)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν)) :
    ∀ᵐ x ∂ν, Tendsto (fun n => ∫ t in Ioc 0 T,
      ((fixedTimePotential T (g n) (hT n) b).value (t,x)-b.value (t,x))^2) atTop (𝓝 0) := by
  have hb := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae b.bounded)
  filter_upwards [b.measurable.prodMk_right,hb] with x hmeas hbound
  have hm : MemLp (fun t => b.value (t,x)) 2 (volume.restrict (Ioc 0 T)) :=
    MemLp.of_bound hmeas b.bound (by simpa only [Real.norm_eq_abs,Prod.swap] using hbound)
  let u := hm.toLp (fun t => b.value (t,x))
  have he n := fixedTimePotential_slice_error T (g n) (hT n) b x u (MemLp.coeFn_toLp hm)
  simp_rw [he]
  have hh := (tendsto_iff_norm_sub_tendsto_zero.mp
    (fixedTimeCell_average_strong_convergence T hTpos g hT htlim u)).pow 2
  simpa only [zero_pow (by decide : 2≠0)] using hh

end Carleman
