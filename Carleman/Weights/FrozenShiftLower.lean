module

public import Carleman.Weights.CellBounds
public import Carleman.Continuous.PeriodicEvolution

/-! The actual frozen shift has the original coercive lower bound. Only the
proved factor-two cell comparison is used, for both cell orientations. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.TimeWeightRegularity
variable {g : TimeGrid} {w : TimeWeight} {β : ℝ} (h : TimeWeightRegularity w g β)
include h

theorem frozen_shift_lower (s : Orientation) {L : ℝ} (hL : 0 ≤ L) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 g.period) (hcell : β*g.dt*w.max^2 ≤ 1/2) :
    (L/2*w.q t)^k ≤ (s.frozenMultiplier g (fun i => (L*w.nodes g i)^k)).value t := by
  have hq := (h.comparable (s.anchor_mem g ht) ht (s.anchor_distance g t) hcell).1
  have hp : (L/2*w.q t)^k ≤ (L*w.q (s.anchor g t))^k := by
    apply pow_le_pow_left₀ (by positivity [w.nonneg t])
    nlinarith [mul_le_mul_of_nonneg_left hq hL]
  have hend : (fun r => (L*w.q r)^k) 0 = (fun r => (L*w.q r)^k) g.period := by
    simp only [h.endpoint]
  rw [s.anchor_value_eq_extension g (fun r => (L*w.q r)^k) hend ht] at hp
  exact hp

theorem frozen_shift_lower_ae (s : Orientation) {L : ℝ} (hL : 0 ≤ L) (k : ℕ)
    (hcell : β*g.dt*w.max^2 ≤ 1/2) :
    ∀ᵐ t ∂g.timeMeasure,
      (L/2)^k*w.q t^k ≤ (s.frozenMultiplier g (fun i => (L*w.nodes g i)^k)).value t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simpa only [mul_pow] using h.frozen_shift_lower s hL k ⟨ht.1.le, ht.2.le⟩ hcell

end Carleman.TimeWeightRegularity

namespace Carleman
/-- Doubling the ordinary form threshold suffices, uniformly before T and
both directions. No μ−barμ estimate or L-dependent perturbation is used. -/
theorem frozen_shift_margin_uniform (m : ℕ) (hm : 0 < m) (β : ℝ) (hβ : 0 < β) (C : ℝ) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight)
        (_h : TimeWeightRegularity w g β) (L : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ →
        ∀ᵐ t ∂g.timeMeasure,
          C*w.q t^(2*m) ≤ (s.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).value t := by
  let M := max 1 C
  refine ⟨2*M, cellThreshold β 0 0, by dsimp [M]; linarith [le_max_left (1:ℝ) C],
    cellThreshold_pos hβ le_rfl le_rfl, ?_⟩
  intro g s w h L hL hmesh
  have hhalf : M ≤ L/2 := by linarith
  have hhalf1 : 1 ≤ L/2 := (le_max_left _ _).trans hhalf
  have hpow : C ≤ (L/2)^(2*m) := by
    apply ((le_max_right _ _).trans hhalf).trans
    simpa only [pow_one] using pow_le_pow_right₀ hhalf1 (show 1 ≤ 2*m by omega)
  have hL0 : 0 ≤ L := by linarith
  have hcell := (h.mesh_bounds 0 0 le_rfl le_rfl hmesh).1
  filter_upwards [h.frozen_shift_lower_ae s hL0 (2*m) hcell] with t ht
  exact (mul_le_mul_of_nonneg_right hpow (pow_nonneg (w.nonneg t) _)).trans ht
end Carleman
