module

public import Carleman.Spatial.DifferentialExpression
public import Carleman.Spatial.AllowedWeight

/-! Integration of the genuine bounded-coefficient expression estimate. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman.DifferentialExpression
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  {m : ℕ} {E : Fin (m+1) → Type*}
  [∀ k, NormedAddCommGroup (E k)] [∀ k, NormedSpace ℝ (E k)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : Type*} [AddCommGroup V] [Module ℝ V]
  {j : ℕ} (D : DifferentialExpression ν E F j)

/-- Realization on the actual spatial fields of the state. -/
def onFields (J : ∀ k, V →ₗ[ℝ] Lp (E k) 2 ν) : V →ₗ[ℝ] Lp F 2 ν :=
  D.linearMap.comp (LinearMap.pi J)

theorem onFields_apply (J : ∀ k, V →ₗ[ℝ] Lp (E k) 2 ν) (v : V) :
    D.onFields J v = D.apply (fun k => J k v) := rfl

/-- This is the order comparison used by ErrorBridge, for any actual state
trajectory, including the a.e. domain representative of its error. -/
theorem timeSq_le_graph (g : TimeGrid) (q : ℝ → ℝ) (hq : ∀ t, 1 ≤ q t)
    (w : ℝ → BoundedMultiplier ν) (J : ∀ k, V →ₗ[ℝ] Lp (E k) 2 ν)
    (u : ℝ → V) (c b : ℝ)
    (hexp : ∀ k : Fin (m+1), k.val ≤ j → c ≤ 2 * (m-k.val : ℕ) + b)
    (hf : ∀ k, TimeSquareIntegrable g q (2*(m-k.val : ℕ)+b)
      (fun t => (w t).seminorm.comp (J k)) u) :
    timeSq g q c (fun t => (w t).seminorm.comp (D.onFields J)) u ≤
      D.boundSq * ∑ k : Fin (m+1),
        timeSq g q (2*(m-k.val : ℕ)+b) (fun t => (w t).seminorm.comp (J k)) u := by
  let density := fun k t => timeDensity q (2*(m-k.val : ℕ)+b)
    (fun t => (w t).seminorm.comp (J k)) u t
  have hf' : ∀ k, Integrable (density k) g.timeMeasure := hf
  calc
    _ ≤ ∫ t, D.boundSq * ∑ k, density k t ∂g.timeMeasure := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun t =>
          mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hq t)) _) (sq_nonneg _)
      · exact (integrable_finsetSum _ fun k _ => hf' k).const_mul _
      · exact Filter.Eventually.of_forall fun t =>
          D.weighted_density_le (w t) (fun k => J k (u t)) (hq t) hexp
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ fun k _ => hf' k]
      rfl

/-- Strong measurability follows through the actual continuous coefficient maps. -/
theorem aestronglyMeasurable_apply {μ : Measure ℝ} (u : ∀ k, ℝ → Lp (E k) 2 ν)
    (hu : ∀ k, AEStronglyMeasurable (u k) μ) :
    AEStronglyMeasurable (fun t => D.apply (fun k => u k t)) μ :=
  D.orders.aestronglyMeasurable_fun_sum fun k _ =>
    (D.coefficient k).continuousLinearMap.continuous.comp_aestronglyMeasurable (hu k)

end Carleman.DifferentialExpression
