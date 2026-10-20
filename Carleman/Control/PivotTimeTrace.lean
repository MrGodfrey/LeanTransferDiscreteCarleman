module

public import Carleman.Continuous.WeakTimeEnergy
public import Carleman.Continuous.TimeTraceBound

/-! The full closed-interval H trace is bounded by the actual value and mass-weighted derivative L2 norms. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman

theorem ac_time_norm_sub_bound {g : TimeGrid} {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 g.period) {a b : ℝ}
    (ha : a ∈ Icc 0 g.period) (hb : b ∈ Icc 0 g.period) :
    ‖f b-f a‖ ≤ ∫ t, ‖deriv f t‖ ∂g.timeMeasure := by
  have hfab : AbsolutelyContinuousOnInterval f a b := hf.mono (by
    rw [uIcc_of_le g.period_pos.le]
    exact uIcc_subset_Icc ha hb)
  have hsub := hfab.integral_deriv_eq_sub
  rw [← hsub]
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  have hi : IntegrableOn (fun t => ‖deriv f t‖) (Icc 0 g.period) volume :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le g.period_pos.le).mp hf.intervalIntegrable_deriv).norm
  change _ ≤ ∫ t in Ioo 0 g.period, ‖deriv f t‖
  rw [restrict_Ioo_eq_restrict_Icc]
  apply setIntegral_mono_set hi (Eventually.of_forall fun t => norm_nonneg _)
  exact Eventually.of_forall fun t ht => (uIcc_subset_Icc ha hb) (uIoc_subset_uIcc ht)

theorem integral_norm_mul_le_l2 {α H F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [NormedAddCommGroup F] {μ : Measure α}
    {u : α → H} {v : α → F} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    (∫ t, ‖u t‖*‖v t‖ ∂μ) ≤ ‖hu.toLp u‖*‖hv.toLp v‖ := by
  let U : Lp ℝ 2 μ := hu.norm.toLp (fun t => ‖u t‖)
  let V : Lp ℝ 2 μ := hv.norm.toLp (fun t => ‖v t‖)
  have he : inner ℝ U V=∫ t, ‖u t‖*‖v t‖ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.norm.coeFn_toLp,hv.norm.coeFn_toLp] with t ht hs
    change U t=‖u t‖ at ht
    change V t=‖v t‖ at hs
    simp [ht,hs,mul_comm]
  have hU : ‖U‖=‖hu.toLp u‖ := by rw [Lp.norm_toLp,Lp.norm_toLp,eLpNorm_norm _ hu.aestronglyMeasurable]
  have hV : ‖V‖=‖hv.toLp v‖ := by rw [Lp.norm_toLp,Lp.norm_toLp,eLpNorm_norm _ hv.aestronglyMeasurable]
  rw [← he,← hU,← hV]
  exact real_inner_le_norm U V

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem HasWeakTimeDerivative.pivot_energy_variation
    {g : TimeGrid} {u du : ℝ → V} (hw : HasWeakTimeDerivative g u du)
    (hu : ContinuousOn u (Icc 0 g.period)) (hd : MemLp du 2 g.timeMeasure)
    (E : V →L[ℝ] H) {a b : ℝ} (ha : a ∈ Icc 0 g.period) (hb : b ∈ Icc 0 g.period) :
    let D := fun t => E.adjoint (E (du t));
    let hD := (hd.continuousLinearMap_comp E).continuousLinearMap_comp E.adjoint;
    ‖E (u b)‖^2 ≤ ‖E (u a)‖^2+2*‖(g.memLp_of_continuousOn hu).toLp u‖*‖hD.toLp D‖ := by
  intro D hD
  have hac : AbsolutelyContinuousOnInterval (fun t => E (u t)) 0 g.period :=
    E.lipschitzWith.comp_absolutelyContinuousOnInterval (hw.absolutelyContinuous hu hd)
  have hnorm := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hac
  have hsq : AbsolutelyContinuousOnInterval (fun t => ‖E (u t)‖^2) 0 g.period := by
    simpa only [pow_two,Function.comp_def] using hnorm.fun_mul hnorm
  have hder : deriv (fun t => ‖E (u t)‖^2) =ᵐ[g.timeMeasure] (fun t => 2*inner ℝ (u t) (D t)) := by
    filter_upwards [hw.ae_hasDerivAt hu hd] with t ht
    have hh := (E.hasFDerivAt.comp_hasDerivAt t ht).norm_sq.deriv
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact hh
  have hbound := ac_time_norm_sub_bound hsq ha hb
  have hi : Integrable (fun t => ‖u t‖*‖D t‖) g.timeMeasure :=
    memLp_one_iff_integrable.mp ((g.memLp_of_continuousOn hu).norm.mul hD.norm)
  have hvar : (∫ t, ‖deriv (fun t => ‖E (u t)‖^2) t‖ ∂g.timeMeasure) ≤
      2*(∫ t, ‖u t‖*‖D t‖ ∂g.timeMeasure) := by
    have hdi := (intervalIntegrable_iff_integrableOn_Ioo_of_le g.period_pos.le).mp hsq.intervalIntegrable_deriv
    have hi₂ := hi.const_mul 2
    rw [← integral_const_mul]
    apply integral_mono_ae hdi.norm hi₂
    filter_upwards [hder] with t ht
    rw [ht,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm (u t) (D t)) (by norm_num)
  have hc := integral_norm_mul_le_l2 (g.memLp_of_continuousOn hu) hD
  have he : ‖E (u b)‖^2-‖E (u a)‖^2 ≤ ‖‖E (u b)‖^2-‖E (u a)‖^2‖ := Real.le_norm_self _
  linarith


theorem HasWeakTimeDerivative.pivot_trace_bound
    {g : TimeGrid} {u du : ℝ → V} (hw : HasWeakTimeDerivative g u du)
    (hu : ContinuousOn u (Icc 0 g.period)) (hd : MemLp du 2 g.timeMeasure)
    (E : V →L[ℝ] H) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    let D := fun t => E.adjoint (E (du t));
    let hD := (hd.continuousLinearMap_comp E).continuousLinearMap_comp E.adjoint;
    let hE := (g.memLp_of_continuousOn hu).continuousLinearMap_comp E;
    ‖E (u t)‖^2 ≤ ‖hE.toLp (fun t => E (u t))‖^2/g.period+
      2*‖(g.memLp_of_continuousOn hu).toLp u‖*‖hD.toLp D‖ := by
  intro D hD hE
  let C := 2*‖(g.memLp_of_continuousOn hu).toLp u‖*‖hD.toLp D‖
  have hp : ∀ᵐ a ∂g.timeMeasure, ‖E (u t)‖^2 ≤ ‖E (u a)‖^2+C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    exact hw.pivot_energy_variation hu hd E ⟨ha.1.le,ha.2.le⟩ ht
  have hi : Integrable (fun a => ‖E (u a)‖^2) g.timeMeasure :=
    (memLp_two_iff_integrable_sq_norm hE.aestronglyMeasurable).mp hE
  have he : (∫ a, ‖E (u a)‖^2 ∂g.timeMeasure)=‖hE.toLp (fun t => E (u t))‖^2 := by
    symm
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hE.coeFn_toLp] with a ha
    rw [ha,real_inner_self_eq_norm_sq]
  have hint := integral_mono_ae (integrable_const (‖E (u t)‖^2)) (hi.fun_add (integrable_const C)) hp
  rw [integral_const,integral_add hi (integrable_const C),integral_const,
    g.timeMeasure_real_univ,smul_eq_mul,smul_eq_mul,he] at hint
  have heq : g.period*(‖hE.toLp (fun t => E (u t))‖^2/g.period+C)=
      ‖hE.toLp (fun t => E (u t))‖^2+g.period*C := by
    field_simp [g.period_pos.ne']
  change ‖E (u t)‖^2 ≤ ‖hE.toLp (fun t => E (u t))‖^2/g.period+C
  nlinarith [g.period_pos]

end Carleman
