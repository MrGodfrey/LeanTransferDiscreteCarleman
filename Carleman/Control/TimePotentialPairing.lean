module

public import Carleman.Control.TimeWeakTesting
public import Carleman.Spatial.WeakProduct

/-! Move the actual real potential to the test in the full Bochner time pairing. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem timeCellReconstruction_multiplier_inner (g : TimeGrid)
    (a : Fin g.steps → BoundedMultiplier ν) (u v : Fin g.steps → Lp ℝ 2 ν) :
    inner ℝ (timeCellReconstruction g (fun i => (a i).map (u i)))
      (timeCellReconstruction g v)=
      inner ℝ (timeCellReconstruction g u)
        (timeCellReconstruction g (fun i => (a i).map (v i))) := by
  simp only [timeCellReconstruction_inner,BoundedMultiplier.inner_map_left]

theorem fixedTimeCellReconstruction_multiplier_inner (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (a : Fin g.steps → BoundedMultiplier ν) (u v : Fin g.steps → Lp ℝ 2 ν) :
    inner ℝ (fixedTimeCellReconstruction T g hT (fun i => (a i).map (u i)))
      (fixedTimeCellReconstruction T g hT v)=
      inner ℝ (fixedTimeCellReconstruction T g hT u)
        (fixedTimeCellReconstruction T g hT (fun i => (a i).map (v i))) := by
  subst T
  exact timeCellReconstruction_multiplier_inner g a u v

end Carleman
