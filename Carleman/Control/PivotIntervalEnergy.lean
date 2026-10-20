module

public import Carleman.Control.PivotTimeTrace
public import Carleman.Control.ObservedRegionLp

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem HasWeakTimeDerivative.pivot_energy_identity_to
    {g : TimeGrid} {u du : ℝ → V} (hw : HasWeakTimeDerivative g u du)
    (hu : ContinuousOn u (Icc 0 g.period)) (hd : MemLp du 2 g.timeMeasure)
    (E : V →L[ℝ] H) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    2*(∫ s in 0..t, inner ℝ (u s) (E.adjoint (E (du s)))) = ‖E (u t)‖^2-‖E (u 0)‖^2 := by
  have hac : AbsolutelyContinuousOnInterval (fun s => E (u s)) 0 g.period :=
    E.lipschitzWith.comp_absolutelyContinuousOnInterval (hw.absolutelyContinuous hu hd)
  have hn := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hac
  have hs : AbsolutelyContinuousOnInterval (fun s => ‖E (u s)‖^2) 0 g.period := by
    simpa only [pow_two,Function.comp_def] using hn.fun_mul hn
  have hst : AbsolutelyContinuousOnInterval (fun s => ‖E (u s)‖^2) 0 t := hs.mono (by
    rw [uIcc_of_le g.period_pos.le,uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2)
  have he := hst.integral_deriv_eq_sub
  have hder : deriv (fun s => ‖E (u s)‖^2) =ᵐ[volume.restrict (Ioc 0 t)]
      (fun s => 2*inner ℝ (u s) (E.adjoint (E (du s)))) := by
    have hh : ∀ᵐ s ∂g.timeMeasure, deriv (fun s => ‖E (u s)‖^2) s =
        2*inner ℝ (u s) (E.adjoint (E (du s))) := by
      filter_upwards [hw.ae_hasDerivAt hu hd] with s hs
      have hx := (E.hasFDerivAt.comp_hasDerivAt s hs).norm_sq.deriv
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact hx
    change _ =ᵐ[volume.restrict (Ioo 0 g.period)] _ at hh
    rw [restrict_Ioo_eq_restrict_Ioc] at hh
    exact hh.filter_mono (ae_mono (Measure.restrict_mono
      (Ioc_subset_Ioc le_rfl ht.2) le_rfl))
  rw [intervalIntegral.integral_of_le ht.1,integral_congr_ae hder,integral_const_mul] at he
  rw [intervalIntegral.integral_of_le ht.1]
  exact he

omit [CompleteSpace V] in
theorem time_restrict_inner_integral {g : TimeGrid} (Y D : Lp V 2 g.timeMeasure)
    {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    inner ℝ (Physical.restrictRegionCLM (Ioc 0 t) Y) (Physical.restrictRegionCLM (Ioc 0 t) D)=
      ∫ s in 0..t, inner ℝ (Y s) (D s) := by
  rw [L2.inner_def,intervalIntegral.integral_of_le ht.1]
  have hμ : g.timeMeasure.restrict (Ioc 0 t)=volume.restrict (Ioc 0 t) := by
    change (volume.restrict (Ioo 0 g.period)).restrict (Ioc 0 t)=_
    rw [restrict_Ioo_eq_restrict_Ioc,Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc le_rfl ht.2)]
  have he := Physical.restrictRegionLp_ae (Ioc 0 t) Y
  have hd := Physical.restrictRegionLp_ae (Ioc 0 t) D
  change (∫ s, inner ℝ (Physical.restrictRegionLp (Ioc 0 t) Y s)
    (Physical.restrictRegionLp (Ioc 0 t) D s) ∂g.timeMeasure.restrict (Ioc 0 t))=_
  rw [← hμ]
  apply integral_congr_ae
  filter_upwards [he,hd] with s hs ht
  rw [hs,ht]


end Carleman
