module

public import Carleman.Weights.TimeL2Multiplier
public import Carleman.Spatial.CellComparison
public import Carleman.Periodic.AffineSeminorm
public import Carleman.Continuous.AffineTimeClass

/-! Genuine allowed-weight order-dt affine defects, for both orientations and
all states. The threshold precedes the period, grid, weight and state. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω} [SFinite ν] (ρ : SpatialProfile ν)
  {g : TimeGrid} {w : TimeWeight} {β : ℝ} (h : TimeWeightRegularity w g β)

omit [SFinite ν] in
/-- The weighted time class agrees exactly with the actual spatial norm density. -/
theorem timeMap_extension_norm_sq (s : Orientation) (τ : ℝ) (u : g.Sequence (Lp E 2 ν)) :
    ‖ρ.timeMap g w τ h.aestronglyMeasurable (s.extensionLp g u)‖^2 =
      ∫ t, ((ρ.multiplier w τ t).seminorm (s.extension g u t))^2 ∂g.timeMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ρ.timeMap_ae g w τ h.aestronglyMeasurable (s.extensionLp g u),
    s.extensionLp_ae g u] with t h1 h2
  rw [h1,h2,real_inner_self_eq_norm_sq]
  rfl

/-- Both norm comparisons, with the cell constant 3 and the real grid norm. -/
theorem timeMap_extension_norm_comparison (s : Orientation) (τ τStar : ℝ)
    (hτStar : 0 ≤ τStar) (hτ : |τ| ≤ τStar)
    (hmesh : g.dt*w.max^2 ≤ cellThreshold β τStar ρ.bound)
    (u : g.Sequence (Lp E 2 ν)) :
    let N := g.weightedNorm (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) u
    ‖ρ.timeMap g w τ h.aestronglyMeasurable (s.extensionLp g u)‖ ≤ 3*N ∧
      N ≤ 3*‖ρ.timeMap g w τ h.aestronglyMeasurable (s.extensionLp g u)‖ := by
  have hb := h.mesh_bounds τStar ρ.bound hτStar ρ.bound_nonneg hmesh
  have hc := ρ.extended_sq_integral_comparison h s τ τStar hτ hb.1 hb.2 u
  dsimp only at hc
  rw [← ρ.timeMap_extension_norm_sq h s τ u] at hc
  have hn := g.weightedNorm_sq (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) u
  have hp : 0 ≤ g.weightedNorm (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) u := Real.sqrt_nonneg _
  constructor <;> nlinarith [norm_nonneg (ρ.timeMap g w τ h.aestronglyMeasurable (s.extensionLp g u))]

variable [CompleteSpace E]

omit [SFinite ν] in
/-- The weighted defect is bounded by the weighted continuous extension of Du. -/
theorem timeMap_affine_defect_le (s : Orientation) (τ : ℝ) (u : g.Sequence (Lp E 2 ν)) :
    ‖ρ.timeMap g w τ h.aestronglyMeasurable (g.affineLp u - s.extensionLp g u)‖ ≤
      g.dt * ‖ρ.timeMap g w τ h.aestronglyMeasurable (s.extensionLp g (s.difference g u))‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ρ.timeMap_ae g w τ h.aestronglyMeasurable (g.affineLp u - s.extensionLp g u),
    ρ.timeMap_ae g w τ h.aestronglyMeasurable (s.extensionLp g (s.difference g u)),
    Lp.coeFn_sub (g.affineLp u) (s.extensionLp g u), g.affineLp_ae u,
    s.extensionLp_ae g u, s.extensionLp_ae g (s.difference g u),
    s.affine_defect_seminorm_ae g (fun t => (ρ.multiplier w τ t).seminorm) u]
    with t h1 h2 h3 h4 h5 h6 ht
  simp only [Pi.sub_apply] at h3
  rw [h1,h2,h3,h4,h5,h6]
  exact ht

include h in
/-- An actual weighted Bochner function norm, with its MemLp obligation discharged. -/
theorem weighted_affine_bochner_defect (s : Orientation) (τ τStar : ℝ)
    (hτStar : 0 ≤ τStar) (hτ : |τ| ≤ τStar)
    (hmesh : g.dt*w.max^2 ≤ cellThreshold β τStar ρ.bound)
    (u : g.Sequence (Lp E 2 ν)) :
    let defect := fun t => (ρ.multiplier w τ t).map
      (g.affineReconstruction u t - s.extension g u t)
    MemLp defect 2 g.timeMeasure ∧ bochnerL2Norm g.timeMeasure defect ≤
      3*g.dt*g.weightedNorm (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) (s.difference g u) := by
  have hd := (g.affine_bochner_defect_le s u).1
  have hm := ρ.memLp_map w τ h.aestronglyMeasurable hd
  refine ⟨hm, ?_⟩
  rw [bochnerL2Norm_eq _ hm, ← ρ.timeMap_toLp g w τ h.aestronglyMeasurable hd]
  have he : hd.toLp (fun t => g.affineReconstruction u t - s.extension g u t) =
      g.affineLp u - s.extensionLp g u := by
    apply Lp.ext
    filter_upwards [hd.coeFn_toLp, Lp.coeFn_sub (g.affineLp u) (s.extensionLp g u),
      g.affineLp_ae u, s.extensionLp_ae g u] with t ht hs ha hu
    simp only [Pi.sub_apply] at hs
    rw [ht,hs,ha,hu]
  rw [he]
  exact (ρ.timeMap_affine_defect_le h s τ u).trans
    ((mul_le_mul_of_nonneg_left (ρ.timeMap_extension_norm_comparison h s τ τStar
      hτStar hτ hmesh (s.difference g u)).1 g.dt_pos.le).trans_eq (by ring))

/-- The constant 3 and the threshold are independent of T, qmax, grid, sign and state. -/
theorem weighted_affine_defect_uniform (β τStar : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ δ > 0, ∀ (g : TimeGrid) (w : TimeWeight) (h : TimeWeightRegularity w g β),
      g.dt*w.max^2 ≤ δ → ∀ (s : Orientation) (τ : ℝ), |τ| ≤ τStar →
      ∀ u : g.Sequence (Lp E 2 ν),
        ‖ρ.timeMap g w τ h.aestronglyMeasurable (g.affineLp u - s.extensionLp g u)‖ ≤
          3*g.dt*g.weightedNorm (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) (s.difference g u) := by
  refine ⟨cellThreshold β τStar ρ.bound, cellThreshold_pos hβ hτStar ρ.bound_nonneg, ?_⟩
  intro g w h hm s τ hτ u
  exact (ρ.timeMap_affine_defect_le h s τ u).trans
    ((mul_le_mul_of_nonneg_left (ρ.timeMap_extension_norm_comparison h s τ τStar
      hτStar hτ hm (s.difference g u)).1 g.dt_pos.le).trans_eq (by ring))

end Carleman.SpatialProfile
