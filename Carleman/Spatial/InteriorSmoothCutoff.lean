module

public import Carleman.Spatial.SpatialTestDerivative
public import Carleman.Spatial.SobolevJet
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Thickening

/-! A genuine compactly supported smooth cutoff inside an arbitrary open
Euclidean domain, equal to one on a prescribed compact subset. -/
@[expose] public noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff
namespace Carleman
variable {d : ℕ} {S K : Set (SpatialCoordinates d)}

theorem exists_spatialTest_eq_one_on_compact (hS : IsOpen S) (hK : IsCompact K)
    (hKS : K ⊆ S) : ∃ η : SpatialTest S, ∀ x ∈ K, η.value x = 1 := by
  obtain ⟨δ,hδ,hd⟩ := hK.exists_cthickening_subset_open hS hKS
  obtain ⟨f,hf,_,hsupp,h1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_thickening : IsOpen (thickening δ K)) hK.isClosed (self_subset_thickening hδ K)
  have ht : tsupport f ⊆ cthickening δ K := by
    rw [tsupport,hsupp]
    exact closure_thickening_subset_cthickening δ K
  exact ⟨⟨f,hf,(hK.cthickening).of_isClosed_subset isClosed_closure ht,ht.trans hd⟩,
    fun x hx => (h1 x).mp hx⟩

end Carleman
