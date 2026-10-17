module

public import Carleman.Spatial.WeightedL2

/-! Algebra of actual bounded multiplication operators on L² equivalence classes. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.BoundedMultiplier
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

def one : BoundedMultiplier ν where
  value := fun _ => 1
  measurable := aestronglyMeasurable_const
  bound := 1
  bound_nonneg := zero_le_one
  bounded := Filter.Eventually.of_forall fun _ => by simp

def mul (w a : BoundedMultiplier ν) : BoundedMultiplier ν where
  value := fun x => w.value x * a.value x
  measurable := w.measurable.mul a.measurable
  bound := w.bound*a.bound
  bound_nonneg := mul_nonneg w.bound_nonneg a.bound_nonneg
  bounded := by
    filter_upwards [w.bounded, a.bounded] with x hw ha
    rw [abs_mul]
    exact mul_le_mul hw ha (abs_nonneg _) w.bound_nonneg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem one_map (u : Lp E 2 ν) : (one (ν := ν)).map u = u := by
  apply Lp.ext
  filter_upwards [(one (ν := ν)).map_ae u] with x hx
  simpa [one] using hx

theorem one_seminorm (u : Lp E 2 ν) : (one (ν := ν)).seminorm u = ‖u‖ := by
  change ‖(one (ν := ν)).map u‖ = ‖u‖
  rw [one_map]

theorem mul_map (w a : BoundedMultiplier ν) (u : Lp E 2 ν) :
    (w.mul a).map u = w.map (a.map u) := by
  apply Lp.ext
  filter_upwards [(w.mul a).map_ae u, w.map_ae (a.map u), a.map_ae u] with x h1 h2 h3
  rw [h1, h2, h3]
  exact mul_smul _ _ _

theorem map_inverse (w a : BoundedMultiplier ν)
    (h : ∀ᵐ x ∂ν, w.value x*a.value x=1) (u : Lp E 2 ν) :
    w.map (a.map u) = u := by
  apply Lp.ext
  filter_upwards [w.map_ae (a.map u), a.map_ae u, h] with x h1 h2 hx
  rw [h1, h2, ← mul_smul, hx, one_smul]
end Carleman.BoundedMultiplier
