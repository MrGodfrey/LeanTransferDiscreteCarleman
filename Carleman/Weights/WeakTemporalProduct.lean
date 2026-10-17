module

public import Carleman.Weights.TemporalMultiplier

/-! The genuine time product rule for the actual Carleman multiplier acting
on weak H¹ trajectories. All coefficient and product L² regularity is proved. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  {ν : Measure Ω} (ρ : SpatialProfile ν)
  {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)

def weightedTimeDerivative (τ : ℝ) (u du : ℝ → Lp E 2 ν) (t : ℝ) : Lp E 2 ν :=
  ρ.logDerivativeAction h τ t ((ρ.multiplier w τ t).map (u t)) +
    (ρ.multiplier w τ t).map (du t)

omit [CompleteSpace E] in
theorem weightedTimeDerivative_L2 (τ : ℝ) {u du : ℝ → Lp E 2 ν}
    (hu : MemLp u 2 g.timeMeasure) (hdu : MemLp du 2 g.timeMeasure) :
    MemLp (ρ.weightedTimeDerivative h τ u du) 2 g.timeMeasure :=
  (ρ.memLp_logDerivativeAction h τ (ρ.memLp_map w τ h.aestronglyMeasurable hu)).add
    (ρ.memLp_map w τ h.aestronglyMeasurable hdu)

/-- Multiplication by the actual weight preserves H¹ with the original weak
Bochner derivative. No everywhere operator-domain representative is required. -/
theorem hasWeakTimeDerivative_map (τ : ℝ) {u du : ℝ → Lp E 2 ν}
    (hu : HasWeakTimeDerivative g u du) (huc : ContinuousOn u (Icc 0 g.period))
    (hdu : MemLp du 2 g.timeMeasure) :
    HasWeakTimeDerivative g (fun t => (ρ.multiplier w τ t).map (u t))
      (ρ.weightedTimeDerivative h τ u du) := by
  have hi : MemLp (fun t => ρ.weightDerivativeCLM h τ t (u t) +
      ρ.weightCLM w τ t (du t)) 2 g.timeMeasure := by
    simp_rw [ρ.weightDerivativeCLM_apply, ρ.weightCLM_apply]
    exact ρ.weightedTimeDerivative_L2 h τ (g.memLp_of_continuousOn huc) hdu
  change HasWeakTimeDerivative g (fun t => (ρ.multiplier w τ t).map (u t))
    (fun t => ρ.logDerivativeAction h τ t ((ρ.multiplier w τ t).map (u t)) +
      (ρ.multiplier w τ t).map (du t))
  simpa only [weightDerivativeCLM_apply, weightCLM_apply] using
    hu.clm_apply huc hdu (ρ.weightCLM_absolutelyContinuous h τ) (ρ.ae_hasDerivAt_weightCLM h τ) hi

include h in
omit [CompleteSpace E] in
theorem continuousOn_map (τ : ℝ) {u : ℝ → Lp E 2 ν}
    (hu : ContinuousOn u (Icc 0 g.period)) :
    ContinuousOn (fun t => (ρ.multiplier w τ t).map (u t)) (Icc 0 g.period) := by
  simpa only [weightCLM_apply] using (ρ.weightCLM_continuousOn (E := E) h τ).clm_apply hu

include h in
omit [CompleteSpace E] in
theorem map_periodic_trace (τ : ℝ) {u : ℝ → Lp E 2 ν} (hu : u 0 = u g.period) :
    (ρ.multiplier w τ 0).map (u 0) = (ρ.multiplier w τ g.period).map (u g.period) := by
  rw [← ρ.weightCLM_apply, ← ρ.weightCLM_apply, ρ.weightCLM_periodic_trace (E := E) h τ, hu]
end Carleman.SpatialProfile
