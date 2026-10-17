module

public import Carleman.Periodic.AffineReconstruction

/-! The affine cell identity controls every real seminorm at the same time.
This allows varying spatial weights without differentiating the step state. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Orientation
variable (s : Orientation) (g : TimeGrid) {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The exact vector defect is a scalar multiple of the actual signed difference. -/
theorem affine_defect_scalar_ae (u : g.Sequence H) :
    ∀ᵐ t ∂g.timeMeasure, ∃ c : ℝ, |c| ≤ g.dt ∧
      g.affineReconstruction u t - s.extension g u t =
        c • s.extension g (s.difference g u) t := by
  filter_upwards [g.ae_open_cell] with t ht
  obtain ⟨n, _, hn⟩ := ht
  have hd := s.signed_difference_on_open_cell g u n hn
  rw [g.affineReconstruction_cell u n ⟨hn.1.le,hn.2.le⟩]
  cases s
  · refine ⟨t-g.cellTime n-g.dt, ?_, ?_⟩
    · exact abs_le.mpr ⟨by linarith [g.cellTime_succ_sub n, hn.1],
        by linarith [g.cellTime_succ_sub n, hn.2, g.dt_pos]⟩
    · simp only [sign, one_smul] at hd
      rw [hd, extension, g.extensionPlus_on_open_cell u n hn, g.forwardSlope_step u n]
      module
  · refine ⟨-(t-g.cellTime n), ?_, ?_⟩
    · rw [abs_neg, abs_of_pos (sub_pos.mpr hn.1)]
      linarith [g.cellTime_succ_sub n, hn.2]
    · simp only [sign, neg_one_smul] at hd
      rw [neg_smul, ← smul_neg, hd, extension, g.extensionMinus_on_open_cell u n hn]
      module

/-- No regularity of p is required for this pointwise, same-time comparison. -/
theorem affine_defect_seminorm_ae (p : ℝ → Seminorm ℝ H) (u : g.Sequence H) :
    ∀ᵐ t ∂g.timeMeasure,
      p t (g.affineReconstruction u t - s.extension g u t) ≤
        g.dt * p t (s.extension g (s.difference g u) t) := by
  filter_upwards [s.affine_defect_scalar_ae g u] with t ht
  obtain ⟨c,hc,he⟩ := ht
  rw [he, map_smul_eq_mul]
  exact mul_le_mul_of_nonneg_right hc (apply_nonneg _ _)

end Carleman.Orientation
