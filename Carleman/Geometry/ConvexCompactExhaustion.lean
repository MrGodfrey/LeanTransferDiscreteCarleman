module

public import Carleman.Spatial.ContractionSequence

/-! A concrete compact convex exhaustion lying strictly inside a bounded
open convex set. Every original interior point belongs eventually, and no
boundary trace or extension theorem is used. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def convexInnerCompact (S : Set (SpatialCoordinates d)) (a : SpatialCoordinates d) (n : ℕ) :
    Set (SpatialCoordinates d) :=
  centeredDilation a (inwardRatio n) (inwardRatio_pos n).ne' '' closure S

theorem convexInnerCompact_compact (hb : Bornology.IsBounded S) (a : SpatialCoordinates d) (n : ℕ) :
    IsCompact (convexInnerCompact S a n) :=
  (isCompact_of_isClosed_isBounded isClosed_closure hb.closure).image
    (centeredDilation a (inwardRatio n) (inwardRatio_pos n).ne').continuous

theorem convexInnerCompact_convex (hc : Convex ℝ S) (a : SpatialCoordinates d) (n : ℕ) :
    Convex ℝ (convexInnerCompact S a n) := by
  change Convex ℝ ((fun x => a+inwardRatio n • (x-a)) '' closure S)
  have he : (fun x : SpatialCoordinates d => a+inwardRatio n • (x-a))=
      (fun x => (a-inwardRatio n • a)+inwardRatio n • x) := by
    funext x
    module
  rw [he]
  exact hc.closure.affinity _ _

theorem convexInnerCompact_subset (hS : IsOpen S) (hc : Convex ℝ S)
    {a : SpatialCoordinates d} (ha : a ∈ S) (n : ℕ) : convexInnerCompact S a n ⊆ S := by
  rintro _ ⟨x,hx,rfl⟩
  exact centeredDilation_mem hS hc ha (inwardRatio_pos n) (inwardRatio_lt_one n) hx

theorem convexInnerCompact_eventually_mem (hS : IsOpen S) (a : SpatialCoordinates d)
    {x : SpatialCoordinates d} (hx : x ∈ S) : ∀ᶠ n in atTop, x ∈ convexInnerCompact S a n := by
  filter_upwards [(inverse_inward_tendsto a x).eventually (hS.mem_nhds hx)] with n hn
  exact ⟨(centeredDilation a (inwardRatio n) (inwardRatio_pos n).ne').symm x,
    subset_closure hn,(centeredDilation a (inwardRatio n) (inwardRatio_pos n).ne').apply_symm_apply x⟩

end Carleman
