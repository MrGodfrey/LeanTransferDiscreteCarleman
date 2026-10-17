module

public import Carleman.Periodic.WeightedNorm
public import Carleman.Continuous.WeakSolution

/-! Actual time integrals of squared, spatially weighted seminorms. -/
@[expose] public noncomputable section
open MeasureTheory

namespace Carleman
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def timeDensity (q : ℝ → ℝ) (s : ℝ) (p : ℝ → Seminorm ℝ E) (u : ℝ → E) (t : ℝ) : ℝ :=
  q t ^ s * (p t (u t)) ^ 2

def timeSq (g : TimeGrid) (q : ℝ → ℝ) (s : ℝ) (p : ℝ → Seminorm ℝ E)
    (u : ℝ → E) : ℝ := ∫ t, timeDensity q s p u t ∂g.timeMeasure

/-- Finiteness is retained explicitly whenever these integrals serve as L² norms. -/
def TimeSquareIntegrable (g : TimeGrid) (q : ℝ → ℝ) (s : ℝ)
    (p : ℝ → Seminorm ℝ E) (u : ℝ → E) : Prop :=
  Integrable (timeDensity q s p u) g.timeMeasure

theorem timeSq_nonneg (g : TimeGrid) (q : ℝ → ℝ) (hq : ∀ t, 0 ≤ q t)
    (s : ℝ) (p : ℝ → Seminorm ℝ E) (u : ℝ → E) : 0 ≤ timeSq g q s p u :=
  integral_nonneg fun t => mul_nonneg (Real.rpow_nonneg (hq t) s) (sq_nonneg _)

theorem timeSq_congr_ae (g : TimeGrid) (q : ℝ → ℝ) (s : ℝ)
    (p : ℝ → Seminorm ℝ E) {u v : ℝ → E} (h : u =ᵐ[g.timeMeasure] v) :
    timeSq g q s p u = timeSq g q s p v := by
  apply integral_congr_ae
  filter_upwards [h] with t ht
  simp only [timeDensity, ht]

theorem seminorm_sub_sq_le (p : Seminorm ℝ E) (u v : E) :
    (p (u - v)) ^ 2 ≤ 2 * ((p u) ^ 2 + (p v) ^ 2) := by
  have h : p (u - v) ≤ p u + p v := map_sub_le_add p u v
  have hn := apply_nonneg p (u - v)
  have hu := apply_nonneg p u
  have hv := apply_nonneg p v
  nlinarith [sq_nonneg (p u - p v)]

/-- Triangle estimate for the concrete space-time norm, with finite RHS norms. -/
theorem timeSq_sub_le (g : TimeGrid) (q : ℝ → ℝ) (hq : ∀ t, 0 ≤ q t)
    (s : ℝ) (p : ℝ → Seminorm ℝ E) (u v : ℝ → E)
    (hu : TimeSquareIntegrable g q s p u) (hv : TimeSquareIntegrable g q s p v) :
    timeSq g q s p (u - v) ≤ 2 * (timeSq g q s p u + timeSq g q s p v) := by
  calc
    _ ≤ ∫ t, 2 * (timeDensity q s p u t + timeDensity q s p v t) ∂g.timeMeasure := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun t =>
          mul_nonneg (Real.rpow_nonneg (hq t) s) (sq_nonneg _)
      · exact (hu.add hv).const_mul 2
      · apply Filter.Eventually.of_forall
        intro t
        have h := mul_le_mul_of_nonneg_left (seminorm_sub_sq_le (p t) (u t) (v t))
          (Real.rpow_nonneg (hq t) s)
        simpa only [timeDensity, Pi.sub_apply, mul_add, mul_left_comm] using h
    _ = _ := by rw [integral_const_mul, integral_add hu hv]; rfl

end Carleman

@[expose] public noncomputable section
namespace Carleman
open MeasureTheory
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem timeSq_le (g : TimeGrid) (q : ℝ → ℝ) (hq : ∀ t, 0 ≤ q t)
    (s : ℝ) (p : ℝ → Seminorm ℝ E) (p' : ℝ → Seminorm ℝ F)
    (u : ℝ → E) (v : ℝ → F) (hv : TimeSquareIntegrable g q s p' v)
    (C : ℝ) (h : ∀ᵐ t ∂g.timeMeasure, (p t (u t)) ^ 2 ≤ C * (p' t (v t)) ^ 2) :
    timeSq g q s p u ≤ C * timeSq g q s p' v := by
  calc
    _ ≤ ∫ t, C * timeDensity q s p' v t ∂g.timeMeasure := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun t =>
          mul_nonneg (Real.rpow_nonneg (hq t) s) (sq_nonneg _)
      · exact hv.const_mul C
      · filter_upwards [h] with t ht
        have hh := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg (hq t) s)
        simpa only [timeDensity, mul_left_comm] using hh
    _ = _ := integral_const_mul _ _

end Carleman

@[expose] public noncomputable section
namespace Carleman
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- On `TimeSquareIntegrable` trajectories, the actual weighted L² norm. -/
def timeNorm (g : TimeGrid) (q : ℝ → ℝ) (s : ℝ) (p : ℝ → Seminorm ℝ E)
    (u : ℝ → E) : ℝ := Real.sqrt (timeSq g q s p u)

theorem timeNorm_sq (g : TimeGrid) (q : ℝ → ℝ) (hq : ∀ t, 0 ≤ q t)
    (s : ℝ) (p : ℝ → Seminorm ℝ E) (u : ℝ → E) :
    timeNorm g q s p u ^ 2 = timeSq g q s p u :=
  Real.sq_sqrt (timeSq_nonneg g q hq s p u)
end Carleman
