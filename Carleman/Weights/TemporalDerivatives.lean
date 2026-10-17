module

public import Carleman.Spatial.AllowedWeight

/-! True time derivatives of the allowed weights, on the closed time interval.
The L² logarithmic multiplier bound is the temporal perturbation in Lemma 3.1.
It uses no derivative of an evolution trajectory and no time mesh restriction. -/
@[expose] public noncomputable section
open Set MeasureTheory
namespace Carleman.TimeWeightRegularity
variable {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)
include h

theorem hasDerivWithinAt_logWeight (τ r : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    HasDerivWithinAt (logWeight (w := w) τ r)
      (τ * (h.derivative t / w.q t) + r * h.derivative t) (Icc 0 g.period) t :=
  (((h.hasDeriv t ht).log (ne_of_gt (w.pos t))).const_mul τ).add
    ((h.hasDeriv t ht).const_mul r)

theorem hasDerivWithinAt_allowedWeight (τ r : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    HasDerivWithinAt (allowedWeight (w := w) τ r)
      (allowedWeight (w := w) τ r t *
        (τ * (h.derivative t / w.q t) + r * h.derivative t)) (Icc 0 g.period) t := by
  simpa only [← allowedWeight_eq_exp] using (h.hasDerivWithinAt_logWeight τ r ht).exp

theorem derivWithin_logWeight_bound (τ r : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    |derivWithin (logWeight (w := w) τ r) (Icc 0 g.period) t| ≤
      β * (|τ| + |r|) * w.q t ^ 2 := by
  rw [(h.hasDerivWithinAt_logWeight τ r ht).derivWithin
    (uniqueDiffOn_Icc (g.period_pos) t ht)]
  exact h.logWeight_derivative_bound τ r ht

omit h in
theorem allowedWeight_inv (τ r t : ℝ) :
    (allowedWeight (w := w) τ r t)⁻¹ = allowedWeight (w := w) (-τ) (-r) t := by
  rw [allowedWeight_eq_exp, allowedWeight_eq_exp, ← Real.exp_neg]
  congr 1
  simp only [logWeight]; ring

end Carleman.TimeWeightRegularity

namespace Carleman.SpatialProfile
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} (ρ : SpatialProfile ν)
  {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)

/-- Multiplication by the actual derivative ∂t log(q^tau exp(q rho)). -/
def logDerivative (τ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) : BoundedMultiplier ν where
  value := fun x => τ * (h.derivative t / w.q t) + ρ.value x * h.derivative t
  measurable := aestronglyMeasurable_const.add (ρ.measurable.mul_const _)
  bound := β * (|τ| + ρ.bound) * w.q t ^ 2
  bound_nonneg := by
    have := h.beta_pos
    have := ρ.bound_nonneg
    positivity
  bounded := by
    filter_upwards [ρ.bounded] with x hx
    exact (h.logWeight_derivative_bound τ (ρ.value x) ht).trans
      (by have := h.beta_pos; gcongr)

/-- The multiplier is identified with the true within derivative a.e. in space. -/
theorem logDerivative_value (τ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) (x : Ω) :
    (ρ.logDerivative h τ ht).value x =
      derivWithin (TimeWeightRegularity.logWeight (w := w) τ (ρ.value x))
        (Icc 0 g.period) t := by
  rw [(h.hasDerivWithinAt_logWeight τ (ρ.value x) ht).derivWithin
    (uniqueDiffOn_Icc g.period_pos t ht)]
  rfl

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem logDerivative_seminorm_le (τ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period)
    (v : Lp H 2 ν) :
    (ρ.logDerivative h τ ht).seminorm v ≤ β * (|τ| + ρ.bound) * w.q t ^ 2 * ‖v‖ :=
  (ρ.logDerivative h τ ht).seminorm_le v

/-- The temporal perturbation is bounded relative to the actual shifted L²
term, with C/L^(2m), uniformly in T and q. -/
theorem logDerivative_shift_le {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 < L)
    (τ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) (v : Lp H 2 ν) :
    (ρ.logDerivative h τ ht).seminorm v ≤
      (β * (|τ| + ρ.bound) / L^(2*m)) * ‖((L*w.q t)^(2*m)) • v‖ := by
  have hβ := h.beta_pos
  have hb := ρ.bound_nonneg
  have hpow : w.q t ^ 2 ≤ w.q t ^ (2*m) :=
    pow_le_pow_right₀ (w.lower t) (by omega)
  have hh := (ρ.logDerivative_seminorm_le h τ ht v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
      (norm_nonneg v))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (mul_pos hL (w.pos t)) _), mul_pow]
  convert hh using 1
  field_simp
end Carleman.SpatialProfile

@[expose] public noncomputable section
open Set
namespace Carleman.TimeWeightRegularity
variable {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)
include h

/-- The precise shift derivative ratio used in Lemma 3.1, with the original
lower weight q_c retained. Put k=2m-1. -/
theorem shifted_power_derivative_ratio (k : ℕ) {L qc : ℝ} (hL : 0 < L)
    (hqc : 0 < qc) (hlower : ∀ t, qc ≤ w.q t)
    {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    |derivWithin (fun s => (L*w.q s)^(k+1)) (Icc 0 g.period) t| /
      ((L*w.q t)^(k+1))^2 ≤ (k+1 : ℝ)*β / (L^(k+1)*qc^k) := by
  have hd := ((h.hasDeriv t ht).const_mul L).fun_pow (k+1)
  rw [hd.derivWithin (uniqueDiffOn_Icc g.period_pos t ht)]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hp : 0 < L*w.q t := mul_pos hL (w.pos t)
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k:ℝ)+1),
    abs_of_nonneg (pow_nonneg hp.le _), abs_mul, abs_of_pos hL]
  have hnum := mul_le_mul_of_nonneg_left (h.derivative_bound t ht)
    (show 0 ≤ ((k:ℝ)+1)*(L*w.q t)^k*L by positivity)
  have hr : (((k:ℝ)+1)*(L*w.q t)^k*(L*|h.derivative t|)) /
        ((L*w.q t)^(k+1))^2 ≤ (((k:ℝ)+1)*β)/(L^(k+1)*(w.q t)^k) := by
    apply (div_le_iff₀ (sq_pos_of_pos (pow_pos hp _))).mpr
    have he : (((k:ℝ)+1)*β)/(L^(k+1)*(w.q t)^k)*((L*w.q t)^(k+1))^2 =
        (((k:ℝ)+1)*(L*w.q t)^k*L)*(β*w.q t^2) := by
      rw [mul_pow, pow_succ L, pow_succ (w.q t)]
      field_simp
      ring
    rw [he]
    convert hnum using 1; ring
  apply hr.trans
  exact div_le_div_of_nonneg_left (by positivity [h.beta_pos])
    (mul_pos (pow_pos hL _) (pow_pos hqc _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hqc.le (hlower t) k) (pow_nonneg hL.le _))
end Carleman.TimeWeightRegularity

@[expose] public noncomputable section
open Set
namespace Carleman.TimeWeightRegularity
variable {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)
include h

/-- The exact continuous shift mu=(Lq)^(2m), with the original q_c dependence. -/
theorem shift_derivative_ratio {m : ℕ} (hm : 0 < m) {L qc : ℝ} (hL : 0 < L)
    (hqc : 0 < qc) (hlower : ∀ t, qc ≤ w.q t)
    {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    |derivWithin (fun s => (L*w.q s)^(2*m)) (Icc 0 g.period) t| /
      ((L*w.q t)^(2*m))^2 ≤ (2*m : ℝ)*β / (L^(2*m)*qc^(2*m-1)) := by
  have hh := h.shifted_power_derivative_ratio (2*m-1) hL hqc hlower ht
  have he : 2*m-1+1 = 2*m := by omega
  have hr : ((2*m-1 : ℕ) : ℝ)+1 = 2*m := by exact_mod_cast he
  simpa only [he, hr] using hh
end Carleman.TimeWeightRegularity
