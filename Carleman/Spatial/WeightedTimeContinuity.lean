module

public import Carleman.Weights.TimeL2Multiplier

/-! Genuine bounded linear weighted Bochner maps, and continuity of the manuscript time squares. -/
@[expose] public noncomputable section
open MeasureTheory Filter
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν) (g : TimeGrid) (w : TimeWeight) (τ : ℝ)
  (hq : AEStronglyMeasurable w.q g.timeMeasure)

def weightedTimeCLM : Lp (Lp E 2 ν) 2 g.timeMeasure →L[ℝ] Lp (Lp E 2 ν) 2 g.timeMeasure :=
  (ρ.timeMap g w τ hq).mkContinuous
    (max 1 (w.max^τ)*Real.exp (ρ.bound*w.max)) (ρ.timeMap_norm_le g w τ hq)


theorem timeSq_eq_weightedTimeCLM_norm_sq (s : ℝ) (u : Lp (Lp E 2 ν) 2 g.timeMeasure) :
    timeSq g w.q s (fun t => (ρ.multiplier w τ t).seminorm) u=
      ‖ρ.weightedTimeCLM g w (τ+s/2) hq u‖^2 :=
  ρ.timeSq_eq_norm_toLp_sq g w τ s hq (Lp.memLp u)

include hq in
theorem continuous_timeSq (s : ℝ) :
    Continuous (fun u : Lp (Lp E 2 ν) 2 g.timeMeasure =>
      timeSq g w.q s (fun t => (ρ.multiplier w τ t).seminorm) u) := by
  simp_rw [ρ.timeSq_eq_weightedTimeCLM_norm_sq g w τ hq s]
  exact ((ρ.weightedTimeCLM g w (τ+s/2) hq).continuous.norm).pow 2

end Carleman.SpatialProfile
