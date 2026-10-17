module

public import Carleman.Spatial.WeightedL2
public import Carleman.Weights.CellRegularity
public import Mathlib.MeasureTheory.Integral.Prod

/-! Realization of the paper's q^tau exp(plus/minus q rho) on spatial L². -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded measurable spatial profile. Smooth rho on the paper's bounded
closed domain supplies this datum. Negation represents theta inverse. -/
structure SpatialProfile (ν : Measure Ω) where
  value : Ω → ℝ
  measurable : AEStronglyMeasurable value ν
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounded : ∀ᵐ x ∂ν, |value x| ≤ bound

namespace SpatialProfile
variable {ν : Measure Ω} (ρ : SpatialProfile ν)

def neg : SpatialProfile ν where
  value := -ρ.value
  measurable := ρ.measurable.neg
  bound := ρ.bound
  bound_nonneg := ρ.bound_nonneg
  bounded := by simpa only [Pi.neg_apply, abs_neg] using ρ.bounded

/-- The actual positive spatial multiplier, not an unspecified norm family. -/
def multiplier (w : TimeWeight) (τ t : ℝ) : BoundedMultiplier ν where
  value x := w.q t ^ τ * Real.exp (ρ.value x * w.q t)
  measurable := (Real.continuous_exp.comp_aestronglyMeasurable
    (ρ.measurable.mul_const (w.q t))).const_mul _
  bound := w.q t ^ τ * Real.exp (ρ.bound * w.q t)
  bound_nonneg := by positivity [w.pos t]
  bounded := by
    filter_upwards [ρ.bounded] with x hx
    rw [abs_of_pos (mul_pos (Real.rpow_pos_of_pos (w.pos t) τ) (Real.exp_pos _))]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (w.nonneg t) τ)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hx) (w.nonneg t))

theorem multiplier_value (w : TimeWeight) (τ t : ℝ) (x : Ω) :
    (ρ.multiplier w τ t).value x = TimeWeightRegularity.allowedWeight (w := w) τ (ρ.value x) t := rfl

/-- Negating the same bounded profile realizes theta inverse with the same bound. -/
theorem multiplier_neg_value (w : TimeWeight) (τ t : ℝ) (x : Ω) :
    (ρ.neg.multiplier w τ t).value x = w.q t ^ τ * (Real.exp (ρ.value x * w.q t))⁻¹ := by
  simp only [multiplier, neg, Pi.neg_apply, neg_mul, Real.exp_neg]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem seminorm_definite (w : TimeWeight) (τ t : ℝ) (u : Lp E 2 ν) :
    (ρ.multiplier w τ t).seminorm u = 0 ↔ u = 0 :=
  (ρ.multiplier w τ t).seminorm_eq_zero_iff
    (Filter.Eventually.of_forall fun x => ne_of_gt (TimeWeightRegularity.allowedWeight_pos τ (ρ.value x) t)) u

/-- The pointwise cell lemma gives a concrete L² comparison, for every field u. -/
theorem seminorm_cell_le {w : TimeWeight} {g : TimeGrid} {β : ℝ}
    (h : TimeWeightRegularity w g β) (τ τStar : ℝ) (hτ : |τ| ≤ τStar)
    {s t : ℝ} (hs : s ∈ Icc 0 g.period) (ht : t ∈ Icc 0 g.period)
    (hd : |t-s| ≤ g.dt) (hm : β * g.dt * w.max ^ 2 ≤ 1/2)
    (hmw : (4*β*(τStar+ρ.bound)) * g.dt * w.max ^ 2 ≤ 1) (u : Lp E 2 ν) :
    (ρ.multiplier w τ t).seminorm u ≤ 3 * (ρ.multiplier w τ s).seminorm u := by
  apply BoundedMultiplier.seminorm_le_of_weight_le
  filter_upwards [ρ.bounded] with x hx
  rw [ρ.multiplier_value, ρ.multiplier_value,
    abs_of_pos (TimeWeightRegularity.allowedWeight_pos τ (ρ.value x) t),
    abs_of_pos (TimeWeightRegularity.allowedWeight_pos τ (ρ.value x) s)]
  exact h.weight_le τ (ρ.value x) τStar ρ.bound hτ hx hs ht hd hm hmw

/-- q powers in the graph/state/observation norms shift the same allowed exponent. -/
theorem multiplier_map_add_exponent (w : TimeWeight) (τ a t : ℝ) (u : Lp E 2 ν) :
    (ρ.multiplier w (τ+a) t).map u = w.q t ^ a • (ρ.multiplier w τ t).map u := by
  apply Lp.ext
  filter_upwards [(ρ.multiplier w (τ+a) t).map_ae u,
    (ρ.multiplier w τ t).map_ae u,
    Lp.coeFn_smul (w.q t ^ a) ((ρ.multiplier w τ t).map u)] with x h1 h2 h3
  simp only [Pi.smul_apply] at h3
  rw [h1, h3, h2]
  simp only [multiplier, Real.rpow_add (w.pos t), smul_smul]
  congr 1
  ring

theorem seminorm_add_exponent (w : TimeWeight) (τ a t : ℝ) (u : Lp E 2 ν) :
    (ρ.multiplier w (τ+a) t).seminorm u = w.q t ^ a * (ρ.multiplier w τ t).seminorm u := by
  rw [BoundedMultiplier.seminorm_apply, ρ.multiplier_map_add_exponent, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (w.pos t) a)]
  rfl

theorem density_eq_shifted_seminorm_sq (w : TimeWeight) (τ a t : ℝ) (u : Lp E 2 ν) :
    w.q t ^ a * ((ρ.multiplier w τ t).seminorm u)^2 =
      ((ρ.multiplier w (τ+a/2) t).seminorm u)^2 := by
  rw [ρ.seminorm_add_exponent, mul_pow]
  have hp : (w.q t ^ (a/2)) ^ 2 = w.q t ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (w.nonneg t)]
    congr 1
    norm_num
  rw [hp]
/-- A bound for finiteness only; comparison constants below do not use qmax or T. -/
theorem seminorm_global_le (w : TimeWeight) (τ t : ℝ) (u : Lp E 2 ν) :
    (ρ.multiplier w τ t).seminorm u ≤
      (max 1 (w.max ^ τ) * Real.exp (ρ.bound * w.max)) * ‖u‖ := by
  apply ((ρ.multiplier w τ t).seminorm_le u).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul (rpow_le_max_one (w.lower t) (w.upper t))
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (w.upper t) ρ.bound_nonneg))
    (Real.exp_pos _).le (by positivity)

end SpatialProfile
end Carleman

@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.SpatialProfile
variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ν : Measure Ω} [SFinite ν] (ρ : SpatialProfile ν)

/-- Measurability of the actual spatial L² integral as time varies. -/
theorem aestronglyMeasurable_seminorm_sq (w : TimeWeight) (τ : ℝ) (u : Lp H 2 ν)
    {μ : Measure ℝ} (hq : AEStronglyMeasurable w.q μ) :
    AEStronglyMeasurable (fun t => ((ρ.multiplier w τ t).seminorm u)^2) μ := by
  have hq' : AEStronglyMeasurable (fun z : ℝ × Ω => w.q z.1) (μ.prod ν) := hq.comp_fst
  have hr : AEStronglyMeasurable (fun z : ℝ × Ω => ρ.value z.2) (μ.prod ν) := ρ.measurable.comp_snd
  have hu : AEStronglyMeasurable (fun z : ℝ × Ω => ‖u z.2‖^2) (μ.prod ν) :=
    ((Lp.aestronglyMeasurable u).norm.pow 2).comp_snd
  have hm := ((hq'.aemeasurable.pow_const τ).aestronglyMeasurable.mul
    (Real.continuous_exp.comp_aestronglyMeasurable (hr.mul hq'))).norm.pow 2
  have hi := (hm.mul hu).integral_prod_right'
  convert hi using 1
  funext t
  rw [(ρ.multiplier w τ t).seminorm_sq_integral]
  rfl
end Carleman.SpatialProfile
