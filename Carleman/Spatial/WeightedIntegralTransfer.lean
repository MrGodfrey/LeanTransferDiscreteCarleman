module

public import Carleman.Spatial.LocalWeightedNorm

/-! Transfer a genuine unweighted L² energy bound to a locally comparable
weight. The positive anchor cancels, leaving a uniform W⁴ factor. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.BoundedMultiplier
variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {ν : Measure Ω}

private theorem lp_norm_sq_integral (u : Lp E 2 ν) :
    ‖u‖^2 = ∫ x, ‖u x‖^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

omit [InnerProductSpace ℝ E] in
private theorem toLp_weighted_integral (f : Ω → E) (hf : MemLp f 2 ν) (a : Ω → ℝ) :
    (∫ x, a x*‖hf.toLp f x‖^2 ∂ν) = ∫ x, a x*‖f x‖^2 ∂ν := by
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem integral_transfer (w : BoundedMultiplier ν) {W s A : ℝ}
    (hW : 0 ≤ W) (hs : 0 < s) (hA : 0 ≤ A)
    (hw : ∀ᵐ x ∂ν, |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|)
    (u : Lp E 2 ν) (v : Lp F 2 ν)
    (h : (∫ x, ‖u x‖^2 ∂ν) ≤ A*(∫ x, ‖v x‖^2 ∂ν)) :
    (∫ x, |w.value x|^2*‖u x‖^2 ∂ν) ≤
      W^4*A*(∫ x, |w.value x|^2*‖v x‖^2 ∂ν) := by
  have hu := w.seminorm_le_anchor W s (hw.mono fun _ hx => hx.1) u
  have hv := w.norm_le_seminorm_anchor W s hs (hw.mono fun _ hx => hx.2) v
  rw [← lp_norm_sq_integral u,← lp_norm_sq_integral v] at h
  rw [← w.seminorm_sq_integral u,← w.seminorm_sq_integral v]
  calc
    _ ≤ (W*s*‖u‖)^2 := (sq_le_sq₀ (apply_nonneg _ _) (by positivity)).mpr hu
    _ = (W*s)^2*‖u‖^2 := by ring
    _ ≤ (W*s)^2*(A*‖v‖^2) := mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ ≤ (W*s)^2*(A*((W/s)*w.seminorm v)^2) := by
      gcongr
    _ = _ := by field_simp

theorem integral_transfer_memLp (w : BoundedMultiplier ν) {W s A : ℝ}
    (hW : 0 ≤ W) (hs : 0 < s) (hA : 0 ≤ A)
    (hw : ∀ᵐ x ∂ν, |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|)
    {u : Ω → E} {v : Ω → F} (hu : MemLp u 2 ν) (hv : MemLp v 2 ν)
    (h : (∫ x, ‖u x‖^2 ∂ν) ≤ A*(∫ x, ‖v x‖^2 ∂ν)) :
    (∫ x, |w.value x|^2*‖u x‖^2 ∂ν) ≤
      W^4*A*(∫ x, |w.value x|^2*‖v x‖^2 ∂ν) := by
  have hb := w.integral_transfer hW hs hA hw (hu.toLp u) (hv.toLp v) (by
    have hu' := toLp_weighted_integral u hu (fun _ => 1)
    have hv' := toLp_weighted_integral v hv (fun _ => 1)
    simp only [one_mul] at hu' hv'
    rw [hu',hv']
    exact h)
  rw [toLp_weighted_integral u hu,toLp_weighted_integral v hv] at hb
  exact hb

end Carleman.BoundedMultiplier
