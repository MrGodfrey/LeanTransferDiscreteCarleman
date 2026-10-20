module
public import Carleman.Spatial.SublevelHeatIdentity
public import Carleman.Spatial.HeatTimeReflection
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-! Actual inner-domain estimates with constants chosen on the fixed outer domain. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace Carleman
variable {d : ℕ}

theorem domainTimeIntegral_const_mul (S : Set (SpatialCoordinates d)) (T C : ℝ)
    (f : (ℝ × SpatialCoordinates d) → ℝ) :
    domainTimeIntegral S T (fun x => C*f x)=C*domainTimeIntegral S T f :=
  integral_const_mul C f

theorem domainTimeIntegral_mono_on (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S)
    (hb : Bornology.IsBounded S) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t ∈ Icc 0 T, ∀ x ∈ S, f (t,x) ≤ g (t,x)) :
    domainTimeIntegral S T f ≤ domainTimeIntegral S T g := by
  have hfi := continuous_domain_time_integrable S hb T hf
  have hgi := continuous_domain_time_integrable S hb T hg
  unfold domainTimeIntegral
  rw [Measure.prod_restrict] at hfi hgi ⊢
  exact setIntegral_mono_on hfi hgi
    (measurableSet_Icc.prod hS)
    (fun tx hx => hfg tx.1 hx.1 tx.2 hx.2)

theorem continuous_domain_observation_integrable (S : Set (SpatialCoordinates d))
    (hb : Bornology.IsBounded S) (T : ℝ)
    {W : Set (SpatialCoordinates d)} (hW : MeasurableSet W)
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) :
    Integrable ((Prod.snd ⁻¹' W).indicator f)
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (S))) :=
  (continuous_domain_time_integrable S hb T hf).indicator (hW.preimage measurable_snd)

theorem domainTimeIntegral_observation (S : Set (SpatialCoordinates d)) (T : ℝ)
    {W : Set (SpatialCoordinates d)} (hW : MeasurableSet W)
    (f : (ℝ × SpatialCoordinates d) → ℝ) :
    domainTimeIntegral S T ((Prod.snd ⁻¹' W).indicator f)=
      ∫ tx, f tx ∂((volume.restrict (Icc 0 T)).prod
        (volume.restrict (S ∩ W))) := by
  unfold domainTimeIntegral
  rw [integral_indicator (hW.preimage measurable_snd),Measure.prod_restrict,
    Measure.restrict_restrict (hW.preimage measurable_snd),Measure.prod_restrict]
  congr 2
  ext tx
  simp only [mem_inter_iff,mem_preimage,mem_prod]
  tauto

theorem domainTimeIntegral_mono_on_integrable (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ}
    (hf : Integrable f ((volume.restrict (Icc 0 T)).prod (volume.restrict (S))))
    (hg : Integrable g ((volume.restrict (Icc 0 T)).prod (volume.restrict (S))))
    (hfg : ∀ t ∈ Icc 0 T, ∀ x ∈ S, f (t,x) ≤ g (t,x)) :
    domainTimeIntegral S T f ≤ domainTimeIntegral S T g := by
  unfold domainTimeIntegral
  rw [Measure.prod_restrict] at hf hg ⊢
  exact setIntegral_mono_on hf hg
    (measurableSet_Icc.prod hS)
    (fun tx hx => hfg tx.1 hx.1 tx.2 hx.2)

theorem domainTimeIntegral_add_integrable (S : Set (SpatialCoordinates d)) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ}
    (hf : Integrable f ((volume.restrict (Icc 0 T)).prod (volume.restrict (S))))
    (hg : Integrable g ((volume.restrict (Icc 0 T)).prod (volume.restrict (S)))) :
    domainTimeIntegral S T (fun tx => f tx+g tx)=domainTimeIntegral S T f+domainTimeIntegral S T g :=
  integral_add hf hg

theorem domainTimeIntegral_nonneg_on (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (T : ℝ)
    {f : (ℝ × SpatialCoordinates d) → ℝ}
    (hf : ∀ t ∈ Icc 0 T, ∀ x ∈ S, 0 ≤ f (t,x)) :
    0 ≤ domainTimeIntegral S T f := by
  unfold domainTimeIntegral
  rw [Measure.prod_restrict]
  exact setIntegral_nonneg (measurableSet_Icc.prod hS)
    (fun tx hx => hf tx.1 hx.1 tx.2 hx.2)

theorem domainHeatTimeReflection_measurePreserving (S : Set (SpatialCoordinates d)) (T : ℝ) :
    MeasurePreserving (heatTimeReflection T)
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (S)))
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (S))) :=
  (time_reflection_measurePreserving T).prod (MeasurePreserving.id _)

theorem domainTimeIntegral_reflection (S : Set (SpatialCoordinates d)) (T : ℝ)
    (f : (ℝ × SpatialCoordinates d) → ℝ) :
    domainTimeIntegral S T (fun tx => f (heatTimeReflection T tx))=domainTimeIntegral S T f := by
  let e := MeasurableEquiv.ofInvolutive (heatTimeReflection (d := d) T)
    (heatTimeReflection_involutive T) (heatTimeReflection_contDiff T).continuous.measurable
  exact (domainHeatTimeReflection_measurePreserving S T).integral_comp e.measurableEmbedding f

theorem domainTimeIntegral_tendsto_parameter (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S) (T : ℝ)
    {qs : ℕ → ℝ → ℝ} {q : ℝ → ℝ} {B : ℝ}
    (hqs : ∀ n, Continuous (qs n)) (hb : ∀ n t, qs n t ∈ Icc 0 B)
    (ht : ∀ t, Tendsto (fun n => qs n t) atTop (𝓝 (q t)))
    {F : ℝ × (ℝ × SpatialCoordinates d) → ℝ} (hF : Continuous F) :
    Tendsto (fun n => domainTimeIntegral S T (fun tx => F (qs n tx.1,tx))) atTop
      (𝓝 (domainTimeIntegral S T (fun tx => F (q tx.1,tx)))) := by
  have hk : IsCompact ((Icc (0:ℝ) B) ×ˢ ((Icc (0:ℝ) T) ×ˢ closure (S))) :=
    isCompact_Icc.prod (isCompact_Icc.prod hbounded.isCompact_closure)
  obtain ⟨D,hD⟩ := hk.exists_bound_of_continuousOn hF.continuousOn
  unfold domainTimeIntegral
  apply tendsto_integral_of_dominated_convergence (fun _ => |D|)
  · intro n
    exact (hF.comp ((hqs n).comp continuous_fst |>.prodMk continuous_id)).aestronglyMeasurable
  · exact continuous_domain_time_integrable S hbounded T continuous_const
  · intro n
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod hS)] with tx htx
    exact (hD _ ⟨hb n tx.1,htx.1,subset_closure htx.2⟩).trans (le_abs_self D)
  · filter_upwards with tx
    exact hF.continuousAt.tendsto.comp ((ht tx.1).prodMk_nhds tendsto_const_nhds)

theorem domainTimeIntegral_observation_tendsto_parameter (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S) (T : ℝ)
    {W : Set (SpatialCoordinates d)} (hW : MeasurableSet W)
    {qs : ℕ → ℝ → ℝ} {q : ℝ → ℝ} {B : ℝ}
    (hqs : ∀ n, Continuous (qs n)) (hb : ∀ n t, qs n t ∈ Icc 0 B)
    (ht : ∀ t, Tendsto (fun n => qs n t) atTop (𝓝 (q t)))
    {F : ℝ × (ℝ × SpatialCoordinates d) → ℝ} (hF : Continuous F) :
    Tendsto (fun n => domainTimeIntegral S T ((Prod.snd ⁻¹' W).indicator (fun tx => F (qs n tx.1,tx)))) atTop
      (𝓝 (domainTimeIntegral S T ((Prod.snd ⁻¹' W).indicator (fun tx => F (q tx.1,tx))))) := by
  have hk : IsCompact ((Icc (0:ℝ) B) ×ˢ ((Icc (0:ℝ) T) ×ˢ closure (S))) :=
    isCompact_Icc.prod (isCompact_Icc.prod hbounded.isCompact_closure)
  obtain ⟨D,hD⟩ := hk.exists_bound_of_continuousOn hF.continuousOn
  unfold domainTimeIntegral
  apply tendsto_integral_of_dominated_convergence (fun _ => |D|)
  · intro n
    exact ((hF.comp ((hqs n).comp continuous_fst |>.prodMk continuous_id)).aestronglyMeasurable).indicator
      (hW.preimage measurable_snd)
  · exact continuous_domain_time_integrable S hbounded T continuous_const
  · intro n
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod hS)] with tx htx
    by_cases hx : tx ∈ Prod.snd ⁻¹' W
    · rw [indicator_of_mem hx]
      exact (hD _ ⟨hb n tx.1,htx.1,subset_closure htx.2⟩).trans (le_abs_self D)
    · rw [indicator_of_notMem hx,norm_zero]
      exact abs_nonneg D
  · filter_upwards with tx
    by_cases hx : tx ∈ Prod.snd ⁻¹' W
    · simp only [indicator_of_mem hx]
      exact hF.continuousAt.tendsto.comp ((ht tx.1).prodMk_nhds tendsto_const_nhds)
    · simp only [indicator_of_notMem hx]
      exact tendsto_const_nhds

theorem domainTimeIntegral_congr_on (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ}
    (he : ∀ t ∈ Icc 0 T, ∀ x ∈ S, f (t,x)=g (t,x)) :
    domainTimeIntegral S T f=domainTimeIntegral S T g := by
  unfold domainTimeIntegral
  rw [Measure.prod_restrict]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod hS)] with tx htx
  exact he tx.1 htx.1 tx.2 htx.2

end Carleman
