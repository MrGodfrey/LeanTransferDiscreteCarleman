module

public import Mathlib.Topology.MetricSpace.Thickening

/-! Measurable interior regions with a certified closed-ball margin. They
exhaust every open set as the margin tends to zero, including the whole space. -/
@[expose] public noncomputable section
open Set Metric Filter
open scoped Topology
namespace Carleman
variable {E : Type*} [MetricSpace E]

def interiorRegion (U : Set E) (ε : ℝ) : Set E := (cthickening ε Uᶜ)ᶜ

theorem isOpen_interiorRegion (U : Set E) (ε : ℝ) : IsOpen (interiorRegion U ε) :=
  isClosed_cthickening.isOpen_compl

theorem interiorRegion_subset (U : Set E) (ε : ℝ) : interiorRegion U ε ⊆ U := by
  intro x hx
  by_contra hn
  exact hx (self_subset_cthickening Uᶜ hn)

theorem interiorRegion_closedBall_subset {U : Set E} {ε : ℝ} {x : E}
    (hx : x ∈ interiorRegion U ε) : closedBall x ε ⊆ U := by
  intro y hy
  by_contra hn
  apply hx
  apply mem_cthickening_of_dist_le x y ε Uᶜ hn
  simpa only [mem_closedBall,dist_comm] using hy

theorem eventually_mem_interiorRegion {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ} (hε : Tendsto ε l (𝓝 0)) :
    ∀ᶠ i in l, x ∈ interiorRegion U (ε i) := by
  have hn : x ∉ closure Uᶜ := by simpa only [hU.isClosed_compl.closure_eq,mem_compl_iff,not_not] using hx
  exact hε.eventually (eventually_notMem_cthickening_of_infEDist_pos hn)
end Carleman
