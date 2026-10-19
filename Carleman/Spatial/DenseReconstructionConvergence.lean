module

public import Carleman.Spatial.IsometricReconstructionProjection

/-! Strong convergence of genuine orthogonal reconstruction projections from dense data. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace Carleman
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {X : ℕ → Type*} [∀ n, NormedAddCommGroup (X n)] [∀ n, InnerProductSpace ℝ (X n)]
  [∀ n, CompleteSpace (X n)] (E : ∀ n, X n →ₗᵢ[ℝ] H)

theorem isometric_reconstruction_residual_bound (n : ℕ) (u : H) :
    ‖u-E n ((E n).toContinuousLinearMap.adjoint u)‖ ≤ ‖u‖ := by
  simpa only [map_zero,sub_zero] using reconstruction_best_approximation (E n) u 0

theorem isometric_reconstruction_tendsto_of_denseRange {D : Type*} (f : D → H)
    (hd : DenseRange f)
    (hf : ∀ v, Tendsto (fun n => ‖f v-E n ((E n).toContinuousLinearMap.adjoint (f v))‖)
      atTop (𝓝 0)) (u : H) :
    Tendsto (fun n => E n ((E n).toContinuousLinearMap.adjoint u)) atTop (𝓝 u) := by
  have hn : Tendsto (fun n => ‖u-E n ((E n).toContinuousLinearMap.adjoint u)‖) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨v,hv⟩ := hd.exists_dist_lt u (half_pos hε)
    have hsmall := (hf v).eventually (gt_mem_nhds (half_pos hε))
    filter_upwards [hsmall] with n hn
    let R : H →L[ℝ] H := ContinuousLinearMap.id ℝ H-
      (E n).toContinuousLinearMap.comp (E n).toContinuousLinearMap.adjoint
    have hr z : R z = z-E n ((E n).toContinuousLinearMap.adjoint z) := rfl
    have he : R u = R (u-f v)+R (f v) := by rw [map_sub]; abel
    have hbound : ‖R u‖ ≤ ‖u-f v‖+‖R (f v)‖ := by
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add (isometric_reconstruction_residual_bound E n (u-f v)) le_rfl)
    rw [dist_eq_norm] at hv
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
    change ‖R u‖ < ε
    rw [hr]
    rw [hr] at hbound
    rw [hr] at hbound
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_sub_rev] using hn

end Carleman
