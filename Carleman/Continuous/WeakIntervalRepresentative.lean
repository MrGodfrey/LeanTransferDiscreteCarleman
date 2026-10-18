module

public import Carleman.Continuous.TimeTraceBound
public import Carleman.Continuous.WeakTimeSpace

/-! Every actual Hilbert-valued weak H¹ class on a positive interval has a
unique continuous representative, including both endpoints. Continuity is
proved from the weak identity, not assumed for the original L² state. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem HasWeakTimeDerivative.congr_value {g : TimeGrid} {u v du : ℝ → H}
    (hw : HasWeakTimeDerivative g u du) (he : u =ᵐ[g.timeMeasure] v) :
    HasWeakTimeDerivative g v du := by
  intro φ hs hc hsup
  rw [← hw φ hs hc hsup]
  apply integral_congr_ae
  filter_upwards [he] with t ht
  rw [ht]

theorem HasWeakTimeDerivative.exists_continuous_representative {g : TimeGrid} {u du : ℝ → H}
    (hw : HasWeakTimeDerivative g u du) (hu : MemLp u 2 g.timeMeasure)
    (hd : MemLp du 2 g.timeMeasure) :
    ∃ U : ℝ → H, ContinuousOn U (Icc 0 g.period) ∧
      u =ᵐ[g.timeMeasure] U ∧ HasWeakTimeDerivative g U du := by
  let F : ℝ → H := fun t => ∫ x in 0..t, du x
  have hFc : ContinuousOn F (Icc 0 g.period) := TimeGrid.primitive_continuousOn hd
  have hFm := g.memLp_of_continuousOn hFc
  have hFw : HasWeakTimeDerivative g F du := HasWeakTimeDerivative.primitive hd
  have hz : HasWeakTimeDerivative g (fun t => u t-F t) (fun _ => 0) := by
    intro φ hs hc hsup
    have hp := g.memLp_of_continuousOn (hs.continuous_deriv (by simp)).continuousOn
    have hiu : Integrable (fun t => deriv φ t • u t) g.timeMeasure :=
      memLp_one_iff_integrable.mp (hp.smul hu)
    have hiF : Integrable (fun t => deriv φ t • F t) g.timeMeasure :=
      memLp_one_iff_integrable.mp (hp.smul hFm)
    simp_rw [smul_sub]
    rw [integral_sub hiu hiF,hw φ hs hc hsup,hFw φ hs hc hsup]
    simp
  obtain ⟨c,hc⟩ := hz.ae_const_of_zero (hu.sub hFm)
  have he : u =ᵐ[g.timeMeasure] (fun t => c+F t) := by
    filter_upwards [hc] with t ht
    exact sub_eq_iff_eq_add.mp ht
  exact ⟨fun t => c+F t,continuousOn_const.add hFc,he,hw.congr_value he⟩

namespace TimeGrid
variable (g : TimeGrid)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem continuous_representative_unique {u v : ℝ → H}
    (hu : ContinuousOn u (Icc 0 g.period)) (hv : ContinuousOn v (Icc 0 g.period))
    (he : u =ᵐ[g.timeMeasure] v) : EqOn u v (Icc 0 g.period) := by
  apply Measure.eqOn_Icc_of_ae_eq volume g.period_pos.ne _ hu hv
  simpa only [timeMeasure,restrict_Ioo_eq_restrict_Icc] using he

omit [CompleteSpace H] in
theorem pathL2_injective : Function.Injective (g.pathL2 (H := H)) := by
  intro u v he
  have heae : (g.pathL2 u : ℝ → H) =ᵐ[g.timeMeasure] g.pathL2 v := by rw [he]
  have ha : (g.clampPath u : ℝ → H) =ᵐ[g.timeMeasure] (g.clampPath v : ℝ → H) :=
    (g.pathL2_ae u).symm.trans (heae.trans (g.pathL2_ae v))
  have hpoint := g.continuous_representative_unique (g.clampPath u).continuous.continuousOn
    (g.clampPath v).continuous.continuousOn ha
  ext t
  simpa only [g.clampPath_on u t t.property,g.clampPath_on v t t.property] using hpoint t.property

theorem exists_tracePath (z : weakTimeSubmodule (H := H) g) :
    ∃ p : g.TracePath (H := H), g.pathL2 p=z.val.1 := by
  obtain ⟨U,hU,hUae,_⟩ := (IsWeakTimeClass.iff_weakDerivative.mp z.property).exists_continuous_representative
    (Lp.memLp z.val.1) (Lp.memLp z.val.2)
  let p : g.TracePath (H := H) := ⟨(Icc 0 g.period).domRestrict U,
    continuousOn_iff_continuous_domRestrict.mp hU⟩
  refine ⟨p,?_⟩
  apply Lp.ext
  filter_upwards [g.pathL2_ae p,hUae,ae_restrict_mem measurableSet_Ioo] with t hp ht hmem
  rw [hp,g.clampPath_on p t ⟨hmem.1.le,hmem.2.le⟩,ht]
  rfl

end TimeGrid
end Carleman
