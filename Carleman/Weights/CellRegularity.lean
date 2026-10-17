module

public import Carleman.Transfer.Weights
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The first-derivative part of the paper's Q class, on the closed time interval.
No all-time domain regularity of an evolution trajectory is involved. -/
@[expose] public noncomputable section
open Set
namespace Carleman

structure TimeWeightRegularity (w : TimeWeight) (g : TimeGrid) (β : ℝ) where
  beta_pos : 0 < β
  derivative : ℝ → ℝ
  hasDeriv : ∀ t ∈ Icc 0 g.period,
    HasDerivWithinAt w.q (derivative t) (Icc 0 g.period) t
  derivative_bound : ∀ t ∈ Icc 0 g.period, |derivative t| ≤ β * w.q t ^ 2
  endpoint : w.q 0 = w.q g.period

/-- C² on the paper's closed interval supplies the first-derivative datum.
Second-derivative and derivative-trace matching assumptions are not needed by this lemma. -/
def TimeWeightRegularity.ofContDiffOn {w : TimeWeight} {g : TimeGrid} {β : ℝ}
    (hβ : 0 < β) (hc : ContDiffOn ℝ 2 w.q (Icc 0 g.period))
    (hb : ∀ t ∈ Icc 0 g.period,
      |derivWithin w.q (Icc 0 g.period) t| ≤ β*w.q t^2)
    (he : w.q 0 = w.q g.period) : TimeWeightRegularity w g β where
  beta_pos := hβ
  derivative := derivWithin w.q (Icc 0 g.period)
  hasDeriv := fun t ht => (hc.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  derivative_bound := hb
  endpoint := he

namespace TimeWeightRegularity
variable {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)
include h

theorem continuousOn : ContinuousOn w.q (Icc 0 g.period) :=
  fun t ht => (h.hasDeriv t ht).continuousWithinAt

theorem aestronglyMeasurable : MeasureTheory.AEStronglyMeasurable w.q g.timeMeasure :=
  (h.continuousOn.aestronglyMeasurable (μ := MeasureTheory.volume) measurableSet_Icc).mono_measure
    (MeasureTheory.Measure.restrict_mono_set _ Ioo_subset_Icc_self)

theorem reciprocal_lipschitz {s t : ℝ} (hs : s ∈ Icc 0 g.period)
    (ht : t ∈ Icc 0 g.period) : |(w.q t)⁻¹ - (w.q s)⁻¹| ≤ β * |t-s| := by
  have hd : ∀ x ∈ Icc 0 g.period,
      HasDerivWithinAt (fun y => (w.q y)⁻¹) (-h.derivative x / w.q x ^ 2)
        (Icc 0 g.period) x := fun x hx => (h.hasDeriv x hx).inv (ne_of_gt (w.pos x))
  have hb : ∀ x ∈ Icc 0 g.period, ‖-h.derivative x / w.q x ^ 2‖ ≤ β := by
    intro x hx
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (sq_pos_of_pos (w.pos x))]
    exact (div_le_iff₀ (sq_pos_of_pos (w.pos x))).mpr (h.derivative_bound x hx)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc 0 g.period) hs ht

theorem difference_le {s t : ℝ} (hs : s ∈ Icc 0 g.period)
    (ht : t ∈ Icc 0 g.period) (hd : |t-s| ≤ g.dt) :
    |w.q t - w.q s| ≤ β * g.dt * (w.q t * w.q s) := by
  have hr := (h.reciprocal_lipschitz hs ht).trans (mul_le_mul_of_nonneg_left hd h.beta_pos.le)
  have he : (w.q t)⁻¹ - (w.q s)⁻¹ = (w.q s - w.q t) / (w.q t * w.q s) := by
    field_simp [ne_of_gt (w.pos t), ne_of_gt (w.pos s)]
  rw [he, abs_div, abs_sub_comm, abs_of_pos (mul_pos (w.pos t) (w.pos s))] at hr
  exact (div_le_iff₀ (mul_pos (w.pos t) (w.pos s))).mp hr

theorem small_node (hm : β * g.dt * w.max ^ 2 ≤ 1/2) (s : ℝ) :
    β * g.dt * w.q s ≤ 1/2 := by
  have hq : w.q s ≤ w.max ^ 2 := by nlinarith [w.upper s, w.max_ge_one]
  exact (mul_le_mul_of_nonneg_left hq (mul_nonneg h.beta_pos.le g.dt_pos.le)).trans hm

/-- Uniform cell comparability; the constant 2 is independent of T, qmax and the grid. -/
theorem comparable {s t : ℝ} (hs : s ∈ Icc 0 g.period)
    (ht : t ∈ Icc 0 g.period) (hd : |t-s| ≤ g.dt)
    (hm : β * g.dt * w.max ^ 2 ≤ 1/2) :
    w.q t ≤ 2 * w.q s ∧ w.q s ≤ 2 * w.q t := by
  have hb := h.small_node hm s
  have he := h.difference_le hs ht hd
  have hmul := mul_le_mul_of_nonneg_right hb (w.nonneg t)
  have h1 := (abs_le.mp he).1
  have h2 := (abs_le.mp he).2
  constructor <;> nlinarith [w.pos t]

/-- The relative q error in Lemma 3.2(ii), at either endpoint of a cell. -/
theorem relative_q {s t : ℝ} (hs : s ∈ Icc 0 g.period)
    (ht : t ∈ Icc 0 g.period) (hd : |t-s| ≤ g.dt)
    (hm : β * g.dt * w.max ^ 2 ≤ 1/2) :
    |w.q t / w.q s - 1| ≤ (2*β) * g.dt * w.q s := by
  have he := h.difference_le hs ht hd
  have hc := (h.comparable hs ht hd hm).1
  have hi : w.q t / w.q s - 1 = (w.q t - w.q s) / w.q s := by field_simp [ne_of_gt (w.pos s)]
  rw [hi, abs_div, abs_of_pos (w.pos s)]
  apply (div_le_iff₀ (w.pos s)).mpr
  have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ β * g.dt * w.q s from
    mul_nonneg (mul_nonneg h.beta_pos.le g.dt_pos.le) (w.nonneg s))
  nlinarith


/-- The log of either allowed weight: take r = rho(x) or r = -rho(x). -/
def logWeight (τ r t : ℝ) : ℝ := τ * Real.log (w.q t) + r * w.q t

def allowedWeight (τ r t : ℝ) : ℝ := w.q t ^ τ * Real.exp (r * w.q t)

omit h in
theorem allowedWeight_pos (τ r t : ℝ) : 0 < allowedWeight (w := w) τ r t :=
  mul_pos (Real.rpow_pos_of_pos (w.pos t) τ) (Real.exp_pos _)

omit h in
theorem allowedWeight_eq_exp (τ r t : ℝ) :
    allowedWeight (w := w) τ r t = Real.exp (logWeight (w := w) τ r t) := by
  simp only [allowedWeight, logWeight, Real.rpow_def_of_pos (w.pos t), Real.exp_add,
    mul_comm (Real.log (w.q t)) τ]

omit h in
theorem cell_distance {s t x : ℝ} (hx : x ∈ uIcc s t) (hd : |t-s| ≤ g.dt) :
    |x-s| ≤ g.dt := by
  rcases mem_uIcc.mp hx with hx | hx
  · exact abs_le.mpr ⟨by linarith [hx.1, hx.2, g.dt_pos, (abs_le.mp hd).1], by linarith [hx.1, hx.2, g.dt_pos, (abs_le.mp hd).2]⟩
  · exact abs_le.mpr ⟨by linarith [hx.1, hx.2, g.dt_pos, (abs_le.mp hd).1], by linarith [hx.1, hx.2, g.dt_pos, (abs_le.mp hd).2]⟩

theorem logWeight_derivative_bound (τ r : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    |τ * (h.derivative t / w.q t) + r * h.derivative t| ≤
      β * (|τ| + |r|) * w.q t ^ 2 := by
  have hv : |h.derivative t / w.q t| ≤ β * w.q t ^ 2 := by
    rw [abs_div, abs_of_pos (w.pos t)]
    exact (div_le_self (abs_nonneg _) (w.lower t)).trans (h.derivative_bound t ht)
  calc
    _ ≤ |τ| * |h.derivative t / w.q t| + |r| * |h.derivative t| := by
      simpa only [abs_mul] using abs_add_le (τ * (h.derivative t / w.q t)) (r * h.derivative t)
    _ ≤ |τ| * (β * w.q t ^ 2) + |r| * (β * w.q t ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (h.derivative_bound t ht) (abs_nonneg _))
    _ = _ := by ring

/-- The allowed-weight logarithmic estimate, uniform over |tau| <= tauStar and |rho| <= R. -/
theorem logWeight_difference (τ r τStar R : ℝ) (hτ : |τ| ≤ τStar) (hr : |r| ≤ R)
    {s t : ℝ} (hs : s ∈ Icc 0 g.period) (ht : t ∈ Icc 0 g.period)
    (hd : |t-s| ≤ g.dt) (hm : β * g.dt * w.max ^ 2 ≤ 1/2) :
    |logWeight (w := w) τ r t - logWeight (w := w) τ r s| ≤
      (4*β*(τStar+R)) * g.dt * w.q s ^ 2 := by
  have hsub := uIcc_subset_Icc hs ht
  have hf : ∀ x ∈ uIcc s t,
      HasDerivWithinAt (logWeight (w := w) τ r)
        (τ * (h.derivative x / w.q x) + r * h.derivative x) (uIcc s t) x := by
    intro x hx
    exact (((h.hasDeriv x (hsub hx)).log (ne_of_gt (w.pos x))).const_mul τ |>.add
      ((h.hasDeriv x (hsub hx)).const_mul r)).mono hsub
  have hK : 0 ≤ β * (τStar+R) :=
    mul_nonneg h.beta_pos.le (add_nonneg ((abs_nonneg _).trans hτ) ((abs_nonneg _).trans hr))
  have hb : ∀ x ∈ uIcc s t,
      ‖τ * (h.derivative x / w.q x) + r * h.derivative x‖ ≤
        4*β*(τStar+R) * w.q s ^ 2 := by
    intro x hx
    rw [Real.norm_eq_abs]
    have hc := (h.comparable hs (hsub hx) (cell_distance hx hd) hm).1
    have hsq : w.q x ^ 2 ≤ 4 * w.q s ^ 2 := by nlinarith [w.nonneg x, w.nonneg s]
    calc
      _ ≤ β * (|τ|+|r|) * w.q x ^ 2 := h.logWeight_derivative_bound τ r (hsub hx)
      _ ≤ β * (τStar+R) * w.q x ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hτ hr)
          h.beta_pos.le) (sq_nonneg _)
      _ ≤ β * (τStar+R) * (4 * w.q s ^ 2) := mul_le_mul_of_nonneg_left hsq hK
      _ = _ := by ring
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hb
    (convex_Icc (min s t) (max s t)) left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at he
  have hn : 0 ≤ 4*β*(τStar+R) * w.q s ^ 2 := by nlinarith [sq_nonneg (w.q s)]
  exact he.trans ((mul_le_mul_of_nonneg_left hd hn).trans_eq (by ring))

/-- Relative allowed-weight error with an explicit common cell threshold. -/
theorem relative_weight (τ r τStar R : ℝ) (hτ : |τ| ≤ τStar) (hr : |r| ≤ R)
    {s t : ℝ} (hs : s ∈ Icc 0 g.period) (ht : t ∈ Icc 0 g.period)
    (hd : |t-s| ≤ g.dt) (hm : β * g.dt * w.max ^ 2 ≤ 1/2)
    (hmw : (4*β*(τStar+R)) * g.dt * w.max ^ 2 ≤ 1) :
    |allowedWeight (w := w) τ r t / allowedWeight (w := w) τ r s - 1| ≤
      (8*β*(τStar+R)) * g.dt * w.q s ^ 2 := by
  have he := h.logWeight_difference τ r τStar R hτ hr hs ht hd hm
  have hK : 0 ≤ 4*β*(τStar+R) * g.dt := by
    have : 0 ≤ τStar+R := add_nonneg ((abs_nonneg _).trans hτ) ((abs_nonneg _).trans hr)
    positivity [h.beta_pos, g.dt_pos]
  have hsq : w.q s ^ 2 ≤ w.max ^ 2 := by nlinarith [w.upper s, w.nonneg s, w.max_ge_one]
  have hb : |logWeight (w := w) τ r t - logWeight (w := w) τ r s| ≤ 1 :=
    he.trans ((mul_le_mul_of_nonneg_left hsq hK).trans hmw)
  rw [allowedWeight_eq_exp, allowedWeight_eq_exp, ← Real.exp_sub]
  exact (Real.abs_exp_sub_one_le hb).trans ((mul_le_mul_of_nonneg_left he (by norm_num)).trans_eq (by ring))


theorem weight_le (τ r τStar R : ℝ) (hτ : |τ| ≤ τStar) (hr : |r| ≤ R)
    {s t : ℝ} (hs : s ∈ Icc 0 g.period) (ht : t ∈ Icc 0 g.period)
    (hd : |t-s| ≤ g.dt) (hm : β * g.dt * w.max ^ 2 ≤ 1/2)
    (hmw : (4*β*(τStar+R)) * g.dt * w.max ^ 2 ≤ 1) :
    allowedWeight (w := w) τ r t ≤ 3 * allowedWeight (w := w) τ r s := by
  have he := h.relative_weight τ r τStar R hτ hr hs ht hd hm hmw
  have hK : 0 ≤ 4*β*(τStar+R) * g.dt := by
    have : 0 ≤ τStar+R := add_nonneg ((abs_nonneg _).trans hτ) ((abs_nonneg _).trans hr)
    positivity [h.beta_pos, g.dt_pos]
  have hsq : w.q s ^ 2 ≤ w.max ^ 2 := by nlinarith [w.upper s, w.nonneg s, w.max_ge_one]
  have hb := (mul_le_mul_of_nonneg_left hsq hK).trans hmw
  have he' := (abs_le.mp he).2
  have hh : allowedWeight (w := w) τ r t / allowedWeight (w := w) τ r s ≤ 3 := by
    nlinarith
  exact (div_le_iff₀ (allowedWeight_pos τ r s)).mp hh

/-- Polynomial shift variation; k=2m gives the manuscript's shift power. -/
theorem power_difference (k : ℕ) (hk : 1 ≤ k)
    {s t : ℝ} (hs : s ∈ Icc 0 g.period) (ht : t ∈ Icc 0 g.period)
    (hd : |t-s| ≤ g.dt) (hm : β * g.dt * w.max ^ 2 ≤ 1/2) :
    |w.q t ^ k - w.q s ^ k| ≤
      (2*(k:ℝ)*2^(k-1)*β) * g.dt * w.q s ^ (k+1) := by
  have hc := (h.comparable hs ht hd hm).1
  have he := h.difference_le hs ht hd
  have hdif : |w.q t - w.q s| ≤ 2*β*g.dt*w.q s^2 := by
    have hh := mul_le_mul_of_nonneg_right hc
      (mul_nonneg (mul_nonneg h.beta_pos.le g.dt_pos.le) (w.nonneg s))
    nlinarith
  have hm' : max |w.q t| |w.q s| ≤ 2 * w.q s := by
    rw [abs_of_pos (w.pos t), abs_of_pos (w.pos s)]
    exact max_le hc (by linarith [w.pos s])
  calc
    _ ≤ |w.q t - w.q s| * k * max |w.q t| |w.q s| ^ (k-1) := abs_pow_sub_pow_le _ _ _
    _ ≤ (2*β*g.dt*w.q s^2) * k * (2*w.q s) ^ (k-1) := by
      gcongr
      positivity [h.beta_pos, g.dt_pos]
    _ = _ := by
      rw [mul_pow]
      have hp : w.q s ^ (k+1) = w.q s ^ 2 * w.q s ^ (k-1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      ring

/-- L occurs only through the exact factor L^k. No threshold depends on L or T. -/
theorem shift_difference (L : ℝ) (hL : 0 ≤ L) (k : ℕ) (hk : 1 ≤ k)
    {s t : ℝ} (hs : s ∈ Icc 0 g.period) (ht : t ∈ Icc 0 g.period)
    (hd : |t-s| ≤ g.dt) (hm : β * g.dt * w.max ^ 2 ≤ 1/2) :
    |(L*w.q t)^k - (L*w.q s)^k| ≤
      (2*(k:ℝ)*2^(k-1)*β) * L^k * g.dt * w.q s ^ (k+1) := by
  rw [mul_pow, mul_pow, ← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hL k)]
  exact (mul_le_mul_of_nonneg_left (h.power_difference k hk hs ht hd hm)
    (pow_nonneg hL k)).trans_eq (by ring)

end TimeWeightRegularity
end Carleman
