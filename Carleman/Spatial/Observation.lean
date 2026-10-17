module

public import Carleman.Spatial.CellComparison

/-! The observation is restriction to a measurable spatial set inside the same L² space. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.BoundedMultiplier
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω}

def cutoff (S : Set Ω) (hS : MeasurableSet S) : BoundedMultiplier ν where
  value := S.indicator (fun _ => (1:ℝ))
  measurable := aestronglyMeasurable_const.indicator hS
  bound := 1
  bound_nonneg := zero_le_one
  bounded := Filter.Eventually.of_forall fun x => by by_cases hx : x ∈ S <;> simp [hx]

def observation (w : BoundedMultiplier ν) (S : Set Ω) (hS : MeasurableSet S) :
    Seminorm ℝ (Lp E 2 ν) := w.seminorm.comp (cutoff S hS).linearMap

theorem observation_le (w : BoundedMultiplier ν) (S : Set Ω) (hS : MeasurableSet S)
    (u : Lp E 2 ν) : w.observation S hS u ≤ w.seminorm u := by
  change ‖w.map ((cutoff S hS).map u)‖ ≤ ‖w.map u‖
  have hb : ‖w.map ((cutoff S hS).map u)‖ ≤ 1 * ‖w.map u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [w.map_ae ((cutoff S hS).map u), w.map_ae u, (cutoff S hS).map_ae u]
      with x hw hv hc
    rw [hw, hv, hc]
    by_cases hx : x ∈ S <;> simp [cutoff, hx]
  simpa only [one_mul] using hb
end Carleman.BoundedMultiplier

namespace Carleman.BoundedMultiplier
variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ν : Measure Ω}

/-- The squared observation norm is exactly the integral on the observed region. -/
theorem observation_sq_integral (w : BoundedMultiplier ν) (S : Set Ω) (hS : MeasurableSet S)
    (u : Lp H 2 ν) :
    (w.observation S hS u)^2 = ∫ x in S, |w.value x|^2 * ‖u x‖^2 ∂ν := by
  change (w.seminorm ((cutoff S hS).map u))^2 = _
  rw [w.seminorm_sq_integral, ← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [(cutoff S hS).map_ae u] with x hx
  rw [hx]
  by_cases hh : x ∈ S <;> simp [cutoff, hh]
end Carleman.BoundedMultiplier

@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialProfile
variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ν : Measure Ω} [SFinite ν] (ρ : SpatialProfile ν)

/-- The same temporal comparison for the actual observed-region seminorm. -/
theorem observation_time_comparison {w : TimeWeight} {g : TimeGrid} {β : ℝ}
    (h : TimeWeightRegularity w g β) (S : Set Ω) (hS : MeasurableSet S)
    (s : Orientation) (τ a τStar : ℝ) (hτ : |τ+a/2| ≤ τStar)
    (hm : β*g.dt*w.max^2 ≤ 1/2) (hmw : (4*β*(τStar+ρ.bound))*g.dt*w.max^2 ≤ 1)
    (u : g.Sequence (Lp H 2 ν)) :
    let p := fun t => (ρ.multiplier w τ t).observation S hS
    TimeSquareIntegrable g w.q a p (s.extension g u) ∧
      timeSq g w.q a p (s.extension g u) ≤ 9*g.powerSq (w.nodes g) a (fun i => p (g.nodeTime i)) u ∧
      g.powerSq (w.nodes g) a (fun i => p (g.nodeTime i)) u ≤ 9*timeSq g w.q a p (s.extension g u) :=
  ρ.powerSq_timeSq_comparison_comp h (BoundedMultiplier.cutoff S hS).linearMap s τ a τStar hτ hm hmw u
end Carleman.SpatialProfile
