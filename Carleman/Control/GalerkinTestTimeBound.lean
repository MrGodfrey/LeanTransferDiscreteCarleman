module

public import Carleman.Control.GalerkinWeightedTest

/-! The original uniform time bound for Pi_X(sigma² z), proved using the
actual L2 multiplier derivative. No projection stability estimate is needed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}
  (X : Submodule ℝ (Lp E 2 ν)) [CompleteSpace X]
  (ρ : SpatialProfile ν) (w : TimeWeight)
  {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)

omit [CompleteSpace E] [CompleteSpace X] in
theorem weightedInclusionDerivative_bound (τ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) (z : X) :
    ‖weightedInclusionDerivative X ρ w h τ t z‖ ≤
      β*(|τ|+ρ.bound)*w.q t^2*‖weightedInclusion X ρ w τ t z‖ := by
  change ‖ρ.weightDerivativeCLM h τ t (z : Lp E 2 ν)‖ ≤
    β*(|τ|+ρ.bound)*w.q t^2*‖ρ.weightCLM w τ t (z : Lp E 2 ν)‖
  rw [ρ.weightDerivativeCLM_apply,ρ.logDerivativeAction_eq h τ ht,ρ.weightCLM_apply]
  exact ρ.logDerivative_seminorm_le h τ ht _

theorem galerkinWeightedTest_time_bound (τ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) (z : X) :
    |inner ℝ z (galerkinWeightedTestDerivative X ρ w h τ t z)| ≤
      (2*β*(|τ|+ρ.bound))*(w.q t*(ρ.multiplier w τ t).seminorm (z : Lp E 2 ν))^2 := by
  rw [galerkinWeightedTestDerivative_pairing]
  let W := weightedInclusion X ρ w τ t z
  let D := weightedInclusionDerivative X ρ w h τ t z
  have hc : |inner ℝ D W+inner ℝ W D| ≤ 2*‖W‖*‖D‖ := by
    exact (abs_add_le _ _).trans ((add_le_add (abs_real_inner_le_norm _ _)
      (abs_real_inner_le_norm _ _)).trans_eq (by ring))
  have hh := hc.trans (mul_le_mul_of_nonneg_left
    (weightedInclusionDerivative_bound X ρ w h τ ht z) (by positivity : 0 ≤ 2*‖W‖))
  have hw : ‖W‖ = (ρ.multiplier w τ t).seminorm (z : Lp E 2 ν) := by
    change ‖ρ.weightCLM w τ t (z : Lp E 2 ν)‖ = _
    rw [ρ.weightCLM_apply]
    rfl
  rw [hw] at hh
  exact hh.trans_eq (by ring)

theorem galerkinWeightedTest_time_bound_uniform (τStar τ : ℝ) (hτ : |τ| ≤ τStar)
    {t : ℝ} (ht : t ∈ Icc 0 g.period) (z : X) :
    |inner ℝ z (galerkinWeightedTestDerivative X ρ w h τ t z)| ≤
      (2*β*(τStar+ρ.bound))*(w.q t*(ρ.multiplier w τ t).seminorm (z : Lp E 2 ν))^2 := by
  apply (galerkinWeightedTest_time_bound X ρ w h τ ht z).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add hτ (le_refl ρ.bound)) (by positivity [h.beta_pos])) (sq_nonneg _)

end Carleman.Physical
