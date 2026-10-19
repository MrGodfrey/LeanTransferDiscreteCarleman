module

public import Carleman.Control.ReconstructedControlCompactness
public import Carleman.Control.ConformingRegionControl
public import Carleman.Spatial.CartesianCellReconstruction

/-! Exact Bochner control norms and time-integrated physical pairings for both actual realizations. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
namespace Physical
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  (ω : Set Ω) (hω : MeasurableSet ω) (g : TimeGrid)

include hω in
theorem conformingTimeControl_norm (u : Fin g.steps → Lp ℝ 2 (ν.restrict ω)) :
    ‖timeCellReconstruction g (fun i => (restrictRegionCLM ω).adjoint (u i))‖ =
      controlNorm g.dt u := by
  rw [timeCellReconstruction_norm]
  simp only [controlNorm,restrictRegion_adjoint ω hω,zeroExtendLp_norm]

theorem conformingTimeControl_on_cell (u : Fin g.steps → Lp ℝ 2 (ν.restrict ω)) (i : Fin g.steps) :
    ∀ᵐ t ∂volume.restrict (g.physicalTimeCell i),
      timeCellReconstruction g (fun j => (restrictRegionCLM ω).adjoint (u j)) t = zeroExtendLp hω (u i) := by
  simpa only [restrictRegion_adjoint ω hω] using
    timeCellReconstruction_on_cell g (fun j => (restrictRegionCLM ω).adjoint (u j)) i

theorem conformingTimeControl_pairing
    (X : Submodule ℝ (Lp ℝ 2 ν)) [CompleteSpace X]
    (u : Fin g.steps → Lp ℝ 2 (ν.restrict ω)) (z : Fin g.steps → X) :
    inner ℝ (timeCellReconstruction g (fun i => (restrictRegionCLM ω).adjoint (u i)))
      (timeCellReconstruction g (fun i => (z i : Lp ℝ 2 ν))) =
      g.dt*∑ i, inner ℝ (u i) ((conformingRegionControl X ω).adjoint (z i)) := by
  rw [timeCellReconstruction_inner]
  simp only [ContinuousLinearMap.adjoint_inner_left,conformingRegionControl_adjoint_apply]
  rfl

end Physical
variable {d : ℕ} (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
  (ω : Set (SpatialCoordinates d)) (g : TimeGrid)
attribute [local instance] Classical.propDecidable

theorem cartesianTimeControl_norm (u : Fin g.steps → CartesianPhysicalControl o δ hδ N ω) :
    ‖timeCellReconstruction g (fun i => cartesianCellControl o δ hδ N ω (u i))‖ =
      Physical.controlNorm g.dt u := by
  rw [timeCellReconstruction_norm]
  simp only [Physical.controlNorm,cartesianCellControl_norm]

theorem cartesianTimeControl_pairing (u : Fin g.steps → CartesianPhysicalControl o δ hδ N ω)
    (z : Fin g.steps → CartesianPhysicalState δ hδ N) :
    inner ℝ (timeCellReconstruction g (fun i => cartesianCellControl o δ hδ N ω (u i)))
      (timeCellReconstruction g (fun i => cartesianCellIsometry o δ hδ N (z i))) =
      g.dt*∑ i, inner ℝ (u i) ((cartesianPhysicalControlExtension o δ hδ N ω).adjoint (z i)) := by
  rw [timeCellReconstruction_inner]
  simp only [cartesianCellControl_pairing]

end Carleman
