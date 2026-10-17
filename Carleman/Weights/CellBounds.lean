module

public import Carleman.Weights.CellRegularity
public import Carleman.Periodic.CellAnchor

/-! Explicit uniform thresholds and both orientation bounds from Lemma 3.2. -/
@[expose] public noncomputable section
open Set MeasureTheory
namespace Carleman

def cellThreshold (β τStar R : ℝ) : ℝ := 1 / (1 + 2*β + 4*β*(τStar+R))

theorem cellThreshold_pos {β τStar R : ℝ} (hβ : 0 < β) (hτ : 0 ≤ τStar) (hR : 0 ≤ R) :
    0 < cellThreshold β τStar R := by unfold cellThreshold; positivity

theorem cellThreshold_bounds {β τStar R D : ℝ} (hβ : 0 < β) (hτ : 0 ≤ τStar)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hm : D ≤ cellThreshold β τStar R) :
    β*D ≤ 1/2 ∧ (4*β*(τStar+R))*D ≤ 1 := by
  have hden : 0 < 1 + 2*β + 4*β*(τStar+R) := by positivity
  have hh := (le_div_iff₀ hden).mp hm
  have hp : 0 ≤ (4*β*(τStar+R))*D := by positivity
  constructor <;> nlinarith

namespace TimeWeightRegularity
variable {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)
include h

theorem mesh_bounds (τStar R : ℝ) (hτ : 0 ≤ τStar) (hR : 0 ≤ R)
    (hm : g.dt*w.max^2 ≤ cellThreshold β τStar R) :
    β*g.dt*w.max^2 ≤ 1/2 ∧ (4*β*(τStar+R))*g.dt*w.max^2 ≤ 1 := by
  simpa only [mul_assoc] using cellThreshold_bounds h.beta_pos hτ hR
    (mul_nonneg g.dt_pos.le (sq_nonneg _)) hm

/-- Relative q error against the actual node used by either extension. -/
theorem relative_q_extension (s : Orientation) {t : ℝ} (ht : t ∈ Icc 0 g.period)
    (hm : β*g.dt*w.max^2 ≤ 1/2) :
    |w.q t / s.extension g (w.nodes g) t - 1| ≤
      (2*β)*g.dt*s.extension g (w.nodes g) t := by
  have he := h.relative_q (s.anchor_mem g ht) ht (s.anchor_distance g t) hm
  rwa [s.anchor_value_eq_extension g w.q h.endpoint ht] at he

/-- Relative sigma error against the actual frozen weight of either orientation. -/
theorem relative_weight_extension (s : Orientation) (τ r τStar R : ℝ)
    (hτ : |τ| ≤ τStar) (hr : |r| ≤ R) {t : ℝ} (ht : t ∈ Icc 0 g.period)
    (hm : β*g.dt*w.max^2 ≤ 1/2) (hmw : (4*β*(τStar+R))*g.dt*w.max^2 ≤ 1) :
    |allowedWeight (w := w) τ r t /
      s.extension g (fun i => allowedWeight (w := w) τ r (g.nodeTime i)) t - 1| ≤
        (8*β*(τStar+R))*g.dt*(s.extension g (w.nodes g) t)^2 := by
  have he := h.relative_weight τ r τStar R hτ hr (s.anchor_mem g ht) ht
    (s.anchor_distance g t) hm hmw
  have hp : allowedWeight (w := w) τ r 0 = allowedWeight (w := w) τ r g.period := by
    simp only [allowedWeight, h.endpoint]
  rw [s.anchor_value_eq_extension g _ hp ht,
    s.anchor_value_eq_extension g w.q h.endpoint ht] at he
  exact he

/-- The frozen shift is the existing nodal mu, with no second sequence interface. -/
theorem shift_extension (s : Orientation) (L : ℝ) (hL : 0 ≤ L) (k : ℕ) (hk : 1 ≤ k)
    {t : ℝ} (ht : t ∈ Icc 0 g.period) (hm : β*g.dt*w.max^2 ≤ 1/2) :
    |(L*w.q t)^k - s.extension g (fun i => (L*w.nodes g i)^k) t| ≤
      (2*(k:ℝ)*2^(k-1)*β) * L^k * g.dt * w.q t^(k+1) := by
  have he := h.shift_difference L hL k hk ht (s.anchor_mem g ht)
    (by simpa only [abs_sub_comm] using s.anchor_distance g t) hm
  have hp : (fun r => (L*w.q r)^k) 0 = (fun r => (L*w.q r)^k) g.period := by simp only [h.endpoint]
  rw [s.anchor_value_eq_extension g (fun r => (L*w.q r)^k) hp ht] at he
  simpa only [TimeWeight.nodes, abs_sub_comm] using he

/-- Forward quotient measured at the right endpoint, as used in the Euler proof. -/
theorem weight_time_quotient (τ r τStar R : ℝ) (hτ : |τ| ≤ τStar) (hr : |r| ≤ R)
    {s t : ℝ} (hs : s ∈ Icc 0 g.period) (ht : t ∈ Icc 0 g.period)
    (hd : |t-s| ≤ g.dt) (hm : β*g.dt*w.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+R))*g.dt*w.max^2 ≤ 1) :
    |(allowedWeight (w := w) τ r t / allowedWeight (w := w) τ r s - 1) / g.dt| ≤
      (32*β*(τStar+R)) * w.q t^2 := by
  have he := h.relative_weight τ r τStar R hτ hr hs ht hd hm hmw
  have hc := (h.comparable hs ht hd hm).2
  have hsq : w.q s ^ 2 ≤ 4*w.q t^2 := by nlinarith [w.nonneg s, w.nonneg t]
  have hK : 0 ≤ 8*β*(τStar+R)*g.dt := by
    have : 0 ≤ τStar+R := add_nonneg ((abs_nonneg _).trans hτ) ((abs_nonneg _).trans hr)
    positivity [h.beta_pos, g.dt_pos]
  rw [abs_div, abs_of_pos g.dt_pos]
  apply (div_le_iff₀ g.dt_pos).mpr
  exact he.trans ((mul_le_mul_of_nonneg_left hsq hK).trans_eq (by ring))

/-- The essential-supremum statement for an arbitrary bounded spatial rho. -/
theorem weight_time_quotient_essSup {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (ρ : Ω → ℝ) (τ τStar R : ℝ) (hτ : |τ| ≤ τStar) (hρ : ∀ᵐ x ∂ν, |ρ x| ≤ R)
    {s t : ℝ} (hs : s ∈ Icc 0 g.period) (ht : t ∈ Icc 0 g.period)
    (hd : |t-s| ≤ g.dt) (hm : β*g.dt*w.max^2 ≤ 1/2)
    (hmw : (4*β*(τStar+R))*g.dt*w.max^2 ≤ 1) :
    eLpNormEssSup (fun x =>
      (allowedWeight (w := w) τ (ρ x) t / allowedWeight (w := w) τ (ρ x) s - 1) / g.dt) ν ≤
        ENNReal.ofReal ((32*β*(τStar+R)) * w.q t^2) := by
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [hρ] with x hx
  simpa only [Real.norm_eq_abs] using h.weight_time_quotient τ (ρ x) τStar R hτ hx hs ht hd hm hmw

/-- Cyclic nodal shift increments, including the last-to-first step. -/
theorem shift_node_increment (L : ℝ) (hL : 0 ≤ L) (k : ℕ) (hk : 1 ≤ k)
    (hm : β*g.dt*w.max^2 ≤ 1/2) (i : g.Index) :
    |(L*w.nodes g (g.next i))^k - (L*w.nodes g i)^k| ≤
      (2*(k:ℝ)*2^(k-1)*β) * L^k * g.dt * w.nodes g i^(k+1) := by
  have hs := g.cellTime_mem i.val (Nat.le_of_lt i.isLt)
  have ht := g.cellTime_mem (i.val+1) (Nat.succ_le_of_lt i.isLt)
  have hd : |g.cellTime (i.val+1) - g.cellTime i.val| ≤ g.dt := by
    rw [g.cellTime_succ_sub, abs_of_pos g.dt_pos]
  have he := h.shift_difference L hL k hk hs ht hd hm
  rw [g.next_node_value w.q h.endpoint i] at he
  exact he

/-- H_n uses sigma_n / sigma_(n-1), not a reversed quotient. -/
theorem weight_node_quotient (τ r τStar R : ℝ) (hτ : |τ| ≤ τStar) (hr : |r| ≤ R)
    (hm : β*g.dt*w.max^2 ≤ 1/2) (hmw : (4*β*(τStar+R))*g.dt*w.max^2 ≤ 1)
    (i : g.Index) :
    |(allowedWeight (w := w) τ r (g.nodeTime i) /
      allowedWeight (w := w) τ r (g.nodeTime (g.prev i)) - 1) / g.dt| ≤
        (32*β*(τStar+R)) * w.nodes g i^2 := by
  let j := g.prev i
  have hs := g.cellTime_mem j.val (Nat.le_of_lt j.isLt)
  have ht := g.cellTime_mem (j.val+1) (Nat.succ_le_of_lt j.isLt)
  have hd : |g.cellTime (j.val+1) - g.cellTime j.val| ≤ g.dt := by
    rw [g.cellTime_succ_sub, abs_of_pos g.dt_pos]
  have he := h.weight_time_quotient τ r τStar R hτ hr hs ht hd hm hmw
  have hp : allowedWeight (w := w) τ r 0 = allowedWeight (w := w) τ r g.period := by
    simp only [allowedWeight, h.endpoint]
  rw [g.next_node_value _ hp j, g.next_node_value w.q h.endpoint j] at he
  simpa only [j, TimeGrid.next_prev, TimeWeight.nodes, TimeGrid.cellTime, TimeGrid.nodeTime] using he

end TimeWeightRegularity
end Carleman
