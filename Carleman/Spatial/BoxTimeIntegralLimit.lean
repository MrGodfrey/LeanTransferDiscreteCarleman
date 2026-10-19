module

public import Carleman.Spatial.BoxObservationIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Dominated limits of continuous parameter families on the actual finite box cylinder. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ}

theorem boxTimeIntegral_tendsto_parameter (a b : Fin d → ℝ) (T : ℝ)
    {qs : ℕ → ℝ → ℝ} {q : ℝ → ℝ} {B : ℝ}
    (hqs : ∀ n, Continuous (qs n)) (hb : ∀ n t, qs n t ∈ Icc 0 B)
    (ht : ∀ t, Tendsto (fun n => qs n t) atTop (𝓝 (q t)))
    {F : ℝ × (ℝ × SpatialCoordinates d) → ℝ} (hF : Continuous F) :
    Tendsto (fun n => boxTimeIntegral a b T (fun tx => F (qs n tx.1,tx))) atTop
      (𝓝 (boxTimeIntegral a b T (fun tx => F (q tx.1,tx)))) := by
  have hk : IsCompact ((Icc (0:ℝ) B) ×ˢ ((Icc (0:ℝ) T) ×ˢ closure (openCoordinateBox a b))) :=
    isCompact_Icc.prod (isCompact_Icc.prod (openCoordinateBox_isBounded a b).isCompact_closure)
  obtain ⟨D,hD⟩ := hk.exists_bound_of_continuousOn hF.continuousOn
  unfold boxTimeIntegral
  apply tendsto_integral_of_dominated_convergence (fun _ => |D|)
  · intro n
    exact (hF.comp ((hqs n).comp continuous_fst |>.prodMk continuous_id)).aestronglyMeasurable
  · exact continuous_box_time_integrable a b T continuous_const
  · intro n
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod (openCoordinateBox_isOpen a b).measurableSet)] with tx htx
    exact (hD _ ⟨hb n tx.1,htx.1,subset_closure htx.2⟩).trans (le_abs_self D)
  · filter_upwards with tx
    exact hF.continuousAt.tendsto.comp ((ht tx.1).prodMk_nhds tendsto_const_nhds)

theorem boxTimeIntegral_observation_tendsto_parameter (a b : Fin d → ℝ) (T : ℝ)
    {W : Set (SpatialCoordinates d)} (hW : MeasurableSet W)
    {qs : ℕ → ℝ → ℝ} {q : ℝ → ℝ} {B : ℝ}
    (hqs : ∀ n, Continuous (qs n)) (hb : ∀ n t, qs n t ∈ Icc 0 B)
    (ht : ∀ t, Tendsto (fun n => qs n t) atTop (𝓝 (q t)))
    {F : ℝ × (ℝ × SpatialCoordinates d) → ℝ} (hF : Continuous F) :
    Tendsto (fun n => boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator (fun tx => F (qs n tx.1,tx)))) atTop
      (𝓝 (boxTimeIntegral a b T ((Prod.snd ⁻¹' W).indicator (fun tx => F (q tx.1,tx))))) := by
  have hk : IsCompact ((Icc (0:ℝ) B) ×ˢ ((Icc (0:ℝ) T) ×ˢ closure (openCoordinateBox a b))) :=
    isCompact_Icc.prod (isCompact_Icc.prod (openCoordinateBox_isBounded a b).isCompact_closure)
  obtain ⟨D,hD⟩ := hk.exists_bound_of_continuousOn hF.continuousOn
  unfold boxTimeIntegral
  apply tendsto_integral_of_dominated_convergence (fun _ => |D|)
  · intro n
    exact ((hF.comp ((hqs n).comp continuous_fst |>.prodMk continuous_id)).aestronglyMeasurable).indicator
      (hW.preimage measurable_snd)
  · exact continuous_box_time_integrable a b T continuous_const
  · intro n
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod (openCoordinateBox_isOpen a b).measurableSet)] with tx htx
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

end Carleman
