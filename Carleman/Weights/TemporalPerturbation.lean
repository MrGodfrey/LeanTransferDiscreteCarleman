module

public import Carleman.Weights.TemporalDerivatives
public import Carleman.Spatial.WeightedTime
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! The temporal perturbation in Lemma 3.1 as a genuine Bochner L² estimate.
Both sides are proved measurable and square integrable before comparing norms.
The estimate constant is independent of T, qmax and the mesh. -/
@[expose] public noncomputable section
open Set MeasureTheory
namespace Carleman

theorem TimeGrid.ae_mem_period (g : TimeGrid) : ∀ᵐ t ∂g.timeMeasure, t ∈ Ioo 0 g.period :=
  ae_restrict_mem measurableSet_Ioo

namespace TimeWeightRegularity
variable {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)

/-- On the open period the supplied within derivative is the actual derivative,
so its measurability does not require any extra regularity assumption. -/
theorem derivative_ae : h.derivative =ᵐ[g.timeMeasure] deriv w.q := by
  filter_upwards [g.ae_mem_period] with t ht
  exact ((h.hasDeriv t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)).deriv.symm

theorem aestronglyMeasurable_derivative : AEStronglyMeasurable h.derivative g.timeMeasure :=
  (aestronglyMeasurable_deriv w.q g.timeMeasure).congr h.derivative_ae.symm

include h in
/-- The actual shifted trajectory belongs to Bochner L² whenever the state does. -/
theorem memLp_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) {L : ℝ} (hL : 0 < L) {u : ℝ → E} (hu : MemLp u 2 g.timeMeasure) :
    MemLp (fun t => ((L*w.q t)^(2*m)) • u t) 2 g.timeMeasure := by
  apply hu.of_le_mul (c := (L*w.max)^(2*m))
    (((h.aestronglyMeasurable.const_mul L).pow _).smul hu.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  change ‖((L*w.q t)^(2*m)) • u t‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity [w.pos t])]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (mul_pos hL (w.pos t)).le
      (mul_le_mul_of_nonneg_left (w.upper t) hL.le) _) (norm_nonneg _)

end TimeWeightRegularity
namespace SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν)
  {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)

def valueMultiplier : BoundedMultiplier ν where
  value := ρ.value
  measurable := ρ.measurable
  bound := ρ.bound
  bound_nonneg := ρ.bound_nonneg
  bounded := ρ.bounded

/-- A global representative of the true logarithmic time derivative action.
Only its values on the time interval enter the conclusions. -/
def logDerivativeAction (τ t : ℝ) (u : Lp E 2 ν) : Lp E 2 ν :=
  (τ * (h.derivative t / w.q t)) • u +
    h.derivative t • ρ.valueMultiplier.map u

theorem logDerivativeAction_eq (τ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period)
    (u : Lp E 2 ν) :
    ρ.logDerivativeAction h τ t u = (ρ.logDerivative h τ ht).map u := by
  apply Lp.ext
  filter_upwards [(ρ.logDerivative h τ ht).map_ae u, ρ.valueMultiplier.map_ae u,
    Lp.coeFn_add ((τ*(h.derivative t/w.q t)) • u)
      (h.derivative t • ρ.valueMultiplier.map u),
    Lp.coeFn_smul (τ*(h.derivative t/w.q t)) u,
    Lp.coeFn_smul (h.derivative t) (ρ.valueMultiplier.map u)] with x h1 h2 h3 h4 h5
  change (((τ*(h.derivative t/w.q t)) • u) +
    h.derivative t • ρ.valueMultiplier.map u) x = _
  rw [h3, h1]
  simp only [Pi.add_apply, Pi.smul_apply] at h3 h4 h5 ⊢
  rw [h4, h5, h2]
  simp only [logDerivative, valueMultiplier, add_smul, mul_smul]
  congr 1
  exact smul_comm _ _ _

theorem aestronglyMeasurable_logDerivativeAction (τ : ℝ) {u : ℝ → Lp E 2 ν}
    (hu : AEStronglyMeasurable u g.timeMeasure) :
    AEStronglyMeasurable (fun t => ρ.logDerivativeAction h τ t (u t)) g.timeMeasure :=
  ((((h.aestronglyMeasurable_derivative.aemeasurable.div
      h.aestronglyMeasurable.aemeasurable).aestronglyMeasurable).const_mul τ).smul hu).add
    (h.aestronglyMeasurable_derivative.smul
      (ρ.valueMultiplier.continuousLinearMap.continuous.comp_aestronglyMeasurable hu))

theorem memLp_logDerivativeAction (τ : ℝ) {u : ℝ → Lp E 2 ν}
    (hu : MemLp u 2 g.timeMeasure) :
    MemLp (fun t => ρ.logDerivativeAction h τ t (u t)) 2 g.timeMeasure := by
  apply hu.of_le_mul (c := β*(|τ|+ρ.bound)*w.max^2)
    (ρ.aestronglyMeasurable_logDerivativeAction h τ hu.aestronglyMeasurable)
  filter_upwards [g.ae_mem_period] with t ht
  rw [ρ.logDerivativeAction_eq h τ (Ioo_subset_Icc_self ht)]
  apply (ρ.logDerivative_seminorm_le h τ (Ioo_subset_Icc_self ht) (u t)).trans
  have hb : 0 ≤ β*(|τ|+ρ.bound) := by positivity [h.beta_pos, ρ.bound_nonneg]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (w.nonneg t) (w.upper t) 2) hb)
    (norm_nonneg _)

/-- The actual L²(0,T;L²(Omega)) temporal perturbation estimate (9.26-eq4).
Every norm is that of a constructed L² class. -/
theorem logDerivative_spacetime_le {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 < L)
    (τ : ℝ) {u : ℝ → Lp E 2 ν} (hu : MemLp u 2 g.timeMeasure) :
    ‖(ρ.memLp_logDerivativeAction h τ hu).toLp
      (fun t => ρ.logDerivativeAction h τ t (u t))‖ ≤
    (β*(|τ|+ρ.bound)/L^(2*m)) *
      ‖(h.memLp_shift m hL hu).toLp (fun t => ((L*w.q t)^(2*m)) • u t)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(ρ.memLp_logDerivativeAction h τ hu).coeFn_toLp,
    (h.memLp_shift m hL hu).coeFn_toLp, g.ae_mem_period] with t h1 h2 ht
  rw [h1, h2, ρ.logDerivativeAction_eq h τ (Ioo_subset_Icc_self ht)]
  exact ρ.logDerivative_shift_le h hm hL τ (Ioo_subset_Icc_self ht) (u t)

end SpatialProfile
end Carleman
