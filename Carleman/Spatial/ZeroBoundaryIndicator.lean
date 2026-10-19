module

public import Carleman.Spatial.PiecewiseSmoothContraction
public import Mathlib.Analysis.Convex.Measure

/-! The true zero extension of a smooth boundary-zero function is Lipschitz
and C1 away from the actual boundary, which is null on a convex domain. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Topology NNReal
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem zeroBoundary_indicator_lipschitz {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}
    (hC : LipschitzWith C f) (hzero : ∀ x ∈ frontier S, f x=0) :
    LipschitzWith C (S.indicator f) := by
  classical
  have hc (x y : SpatialCoordinates d) (hx : x ∈ S) (hy : y ∉ S) :
      dist (f x) 0 ≤ C*dist x y := by
    obtain ⟨z,hz,hd⟩ := exists_mem_frontier_infDist_compl_eq_dist hx
      (by intro he; exact hy (he ▸ mem_univ y))
    calc
      _ = dist (f x) (f z) := by rw [hzero z hz]
      _ ≤ C*dist x z := hC.dist_le_mul x z
      _ ≤ C*dist x y := mul_le_mul_of_nonneg_left
        (hd ▸ Metric.infDist_le_dist_of_mem hy) C.coe_nonneg
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simpa only [indicator_of_mem hx,indicator_of_mem hy] using hC.dist_le_mul x y
  · simpa only [indicator_of_mem hx,indicator_of_notMem hy] using hc x y hx hy
  · simpa only [indicator_of_notMem hx,indicator_of_mem hy,dist_comm] using hc y x hy hx
  · simp only [indicator_of_notMem hx,indicator_of_notMem hy,dist_self]
    exact mul_nonneg C.coe_nonneg dist_nonneg

theorem indicator_tsupport_subset_closure (f : SpatialCoordinates d → ℝ) :
    tsupport (S.indicator f) ⊆ closure S := by
  apply closure_mono
  exact Set.support_indicator_subset

theorem indicator_hasCompactSupport {f : SpatialCoordinates d → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (S.indicator f) := by
  apply hf.mono
  intro x hx
  by_cases hs : x ∈ S
  · simpa only [Function.mem_support,indicator_of_mem hs] using hx
  · exact False.elim (hx (indicator_of_notMem hs f))

theorem indicator_contDiffAt_off_frontier (hS : IsOpen S) {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ 1 f) {x : SpatialCoordinates d} (hx : x ∉ frontier S) :
    ContDiffAt ℝ 1 (S.indicator f) x := by
  classical
  by_cases hs : x ∈ S
  · apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [hS.mem_nhds hs] with y hy
    exact indicator_of_mem hy f
  · have hn : x ∉ closure S := by
      intro hc
      exact hx ⟨hc,by simpa only [hS.interior_eq] using hs⟩
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with y hy
    exact indicator_of_notMem (fun h => hy (subset_closure h)) f

theorem indicator_contDiffAt_ae (hS : IsOpen S) (hconv : Convex ℝ S)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ 1 f) :
    ∀ᵐ x ∂volume, ContDiffAt ℝ 1 (S.indicator f) x := by
  have hn : ∀ᵐ x ∂volume, x ∉ frontier S := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using hconv.addHaar_frontier (volume : Measure (SpatialCoordinates d))
  exact hn.mono fun _ hx => indicator_contDiffAt_off_frontier hS hf hx

end Carleman
