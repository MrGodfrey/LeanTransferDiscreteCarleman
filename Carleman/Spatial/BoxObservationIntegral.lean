module

public import Carleman.Spatial.BoxTimeIntegralOrder

/-! The actual observation-cylinder integral, including integrability of its indicator. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem continuous_box_observation_integrable (a b : Fin d → ℝ) (T : ℝ)
    {W : Set (SpatialCoordinates d)} (hW : MeasurableSet W)
    {f : (ℝ × SpatialCoordinates d) → ℝ} (hf : Continuous f) :
    Integrable ((Prod.snd ⁻¹' W).indicator f)
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b))) :=
  (continuous_box_time_integrable a b T hf).indicator (hW.preimage measurable_snd)

theorem boxTimeIntegral_observation (a b : Fin d → ℝ) (T : ℝ)
    {W : Set (SpatialCoordinates d)} (hW : MeasurableSet W)
    (f : (ℝ × SpatialCoordinates d) → ℝ) :
    boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator f)=
      ∫ tx, f tx ∂((volume.restrict (Icc 0 T)).prod
        (volume.restrict (openCoordinateBox a b ∩ W))) := by
  unfold boxTimeIntegral
  rw [integral_indicator (hW.preimage measurable_snd),Measure.prod_restrict,
    Measure.restrict_restrict (hW.preimage measurable_snd),Measure.prod_restrict]
  congr 2
  ext tx
  simp only [mem_inter_iff,mem_preimage,mem_prod]
  tauto

theorem boxTimeIntegral_mono_on_integrable (a b : Fin d → ℝ) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ}
    (hf : Integrable f ((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b))))
    (hg : Integrable g ((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b))))
    (hfg : ∀ t ∈ Icc 0 T, ∀ x ∈ openCoordinateBox a b, f (t,x) ≤ g (t,x)) :
    boxTimeIntegral a b T f ≤ boxTimeIntegral a b T g := by
  unfold boxTimeIntegral
  rw [Measure.prod_restrict] at hf hg ⊢
  exact setIntegral_mono_on hf hg
    (measurableSet_Icc.prod (openCoordinateBox_isOpen a b).measurableSet)
    (fun tx hx => hfg tx.1 hx.1 tx.2 hx.2)

theorem boxTimeIntegral_add_integrable (a b : Fin d → ℝ) (T : ℝ)
    {f g : (ℝ × SpatialCoordinates d) → ℝ}
    (hf : Integrable f ((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b))))
    (hg : Integrable g ((volume.restrict (Icc 0 T)).prod (volume.restrict (openCoordinateBox a b)))) :
    boxTimeIntegral a b T (fun tx => f tx+g tx)=boxTimeIntegral a b T f+boxTimeIntegral a b T g :=
  integral_add hf hg

theorem boxTimeIntegral_nonneg_on (a b : Fin d → ℝ) (T : ℝ)
    {f : (ℝ × SpatialCoordinates d) → ℝ}
    (hf : ∀ t ∈ Icc 0 T, ∀ x ∈ openCoordinateBox a b, 0 ≤ f (t,x)) :
    0 ≤ boxTimeIntegral a b T f := by
  unfold boxTimeIntegral
  rw [Measure.prod_restrict]
  exact setIntegral_nonneg (measurableSet_Icc.prod (openCoordinateBox_isOpen a b).measurableSet)
    (fun tx hx => hf tx.1 hx.1 tx.2 hx.2)

end Carleman
