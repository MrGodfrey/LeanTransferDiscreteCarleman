module

public import Carleman.Weights.CellBounds

/-! Discharges the scalar shift multiplier in ErrorBridge using the actual frozen mu. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {w : TimeWeight} {g : TimeGrid} {β : ℝ}
  (h : TimeWeightRegularity w g β) (a : CarlemanExponents)
include h

theorem frozenShift_extension_sq_le (s : Orientation) (L : ℝ) (hL : 0 ≤ L)
    (hm : β*g.dt*w.max^2 ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    (s.extension g (frozenShift a w g L) t)^2 ≤ (2*L)^(4*a.m) * w.q t^(4*a.m:ℝ) := by
  have hc := (h.comparable (s.anchor_mem g ht) ht (s.anchor_distance g t) hm).2
  rw [s.anchor_value_eq_extension g w.q h.endpoint ht] at hc
  change s.extension g (w.nodes g) t ≤ 2*w.q t at hc
  have hn : 0 ≤ s.extension g (w.nodes g) t := by
    rw [s.extension_eq_cellNumber]
    exact w.nonneg _
  have he : s.extension g (frozenShift a w g L) t = (L*s.extension g (w.nodes g) t)^(2*a.m) := by
    cases s <;> rfl
  rw [he, ← pow_mul]
  have hk : 2*a.m*2 = 4*a.m := by omega
  rw [hk]
  have hh : L*s.extension g (w.nodes g) t ≤ (2*L)*w.q t := by
    exact (mul_le_mul_of_nonneg_left hc hL).trans_eq (by ring)
  have hp := pow_le_pow_left₀ (mul_nonneg hL hn) hh (4*a.m)
  have hr : w.q t^(4*a.m:ℝ) = w.q t^(4*a.m) := by
    norm_cast
  simpa only [mul_pow, hr] using hp

/-- The precise q^(4m) loss in the existing ErrorBridge.shift field, with finiteness. -/
theorem frozenShift_timeSq_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Orientation) (L : ℝ) (hL : 0 ≤ L) (hm : β*g.dt*w.max^2 ≤ 1/2)
    (p : ℝ → Seminorm ℝ E) (u : ℝ → E)
    (hu : TimeSquareIntegrable g w.q (4*a.m:ℝ) p u) :
    TimeSquareIntegrable g w.q 0 p (fun t => s.extension g (frozenShift a w g L) t • u t) ∧
    timeSq g w.q 0 p (fun t => s.extension g (frozenShift a w g L) t • u t) ≤
      (2*L)^(4*a.m) * timeSq g w.q (4*a.m:ℝ) p u := by
  let μ := s.extension g (frozenShift a w g L)
  let d := timeDensity w.q 0 p (fun t => μ t • u t)
  let e := timeDensity w.q (4*a.m:ℝ) p u
  have heq : d = fun t => (μ t)^2 / w.q t^(4*a.m:ℝ) * e t := by
    funext t
    dsimp [d, e, timeDensity]
    rw [Real.rpow_zero, one_mul, map_smul_eq_mul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos (w.pos t) (4*a.m:ℝ))]
  have hmeas : AEStronglyMeasurable d g.timeMeasure := by
    rw [heq]
    exact (((s.integrable_extension g (frozenShift a w g L)).aestronglyMeasurable.pow 2).aemeasurable.div
      (h.aestronglyMeasurable.aemeasurable.pow_const (4*a.m:ℝ))).aestronglyMeasurable.mul hu.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂g.timeMeasure, d t ≤ (2*L)^(4*a.m)*e t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    have hh := frozenShift_extension_sq_le h a s L hL hm ⟨ht.1.le, ht.2.le⟩
    dsimp [d, e, timeDensity]
    rw [Real.rpow_zero, one_mul, map_smul_eq_mul, Real.norm_eq_abs, mul_pow, sq_abs]
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (by ring)
  have hi : Integrable d g.timeMeasure := (hu.const_mul ((2*L)^(4*a.m))).mono' hmeas (by
    filter_upwards [hbound] with t ht
    simpa only [Real.norm_eq_abs, d, e, timeDensity, Real.rpow_zero, one_mul, abs_sq] using ht)
  refine ⟨hi, ?_⟩
  have hh := integral_mono_ae hi (hu.const_mul ((2*L)^(4*a.m))) hbound
  rw [integral_const_mul] at hh
  exact hh
end Carleman
