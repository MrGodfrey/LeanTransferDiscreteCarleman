module

public import Carleman.Spatial.WeakDerivative
public import Carleman.Spatial.MultiplierContinuity

/-! Multiplication of actual weak derivatives by a bounded smooth spatial
weight. Smoothness is required only on the open domain, not on all of space. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Carleman
namespace BoundedMultiplier
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem inner_map_left (w : BoundedMultiplier ν) (u v : Lp ℝ 2 ν) :
    inner ℝ (w.map u) v = inner ℝ u (w.map v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [w.map_ae u, w.map_ae v] with x hu hv
  simp only [hu, hv, RCLike.inner_apply, conj_trivial, smul_eq_mul]
  ring

end BoundedMultiplier
namespace SpatialTest
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {S : Set E}

/-- Compact support inside S makes the product globally smooth, even when
the coefficient is assumed smooth only on S. -/
def mulOn (φ : SpatialTest S) (hS : IsOpen S) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f S) : SpatialTest S where
  value := f * φ.value
  smooth := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ S
    · exact (hf.contDiffAt (hS.mem_nhds hx)).mul φ.smooth.contDiffAt
    · have hn : x ∉ tsupport φ.value := fun h => hx (φ.support h)
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      change f y * φ.value y = 0
      simp only [Pi.zero_apply] at hy
      rw [hy, mul_zero]
  compact := φ.compact.mul_left
  support := tsupport_mul_subset_right.trans φ.support

variable {ν : Measure E} [IsFiniteMeasureOnCompacts ν]

theorem mulOn_toLp (φ : SpatialTest S) (hS : IsOpen S)
    (w : BoundedMultiplier ν) (hw : ContDiffOn ℝ ∞ w.value S) :
    (φ.mulOn hS hw).toLp ν = w.map (φ.toLp ν) := by
  apply Lp.ext
  filter_upwards [(φ.mulOn hS hw).toLp_ae ν, w.map_ae (φ.toLp ν), φ.toLp_ae ν]
    with x h1 h2 h3
  rw [h1, h2, h3]
  rfl

theorem mulOn_derivativeLp (φ : SpatialTest S) (hS : IsOpen S)
    (hν : ∀ᵐ x ∂ν, x ∈ S) (e : E) (w dw : BoundedMultiplier ν)
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : dw.value =ᵐ[ν] (fun x => fderiv ℝ w.value x e)) :
    (φ.mulOn hS hw).derivativeLp ν e =
      w.map (φ.derivativeLp ν e) + dw.map (φ.toLp ν) := by
  apply Lp.ext
  filter_upwards [(φ.mulOn hS hw).derivativeLp_ae ν e,
    w.map_ae (φ.derivativeLp ν e), dw.map_ae (φ.toLp ν), φ.derivativeLp_ae ν e,
    φ.toLp_ae ν, hdw, hν,
    Lp.coeFn_add (w.map (φ.derivativeLp ν e)) (dw.map (φ.toLp ν))]
    with x h1 h2 h3 h4 h5 hd hx h6
  rw [h1, h6]
  simp only [Pi.add_apply, h2, h3, h4, h5, hd, smul_eq_mul]
  change fderiv ℝ (w.value * φ.value) x e = _
  rw [fderiv_mul ((hw.contDiffAt (hS.mem_nhds hx)).differentiableAt (by simp))
    (φ.smooth.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

end SpatialTest
namespace IsWeakSpatialDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ν : Measure E} [IsFiniteMeasureOnCompacts ν] {S : Set E} {e : E}
  {u v : Lp ℝ 2 ν}

/-- The genuine distributional product rule, on a.e. L² classes. -/
theorem mul (h : IsWeakSpatialDerivative ν S e u v) (hS : IsOpen S)
    (hν : ∀ᵐ x ∂ν, x ∈ S) (w dw : BoundedMultiplier ν)
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : dw.value =ᵐ[ν] (fun x => fderiv ℝ w.value x e)) :
    IsWeakSpatialDerivative ν S e (w.map u) (w.map v + dw.map u) := by
  intro φ
  have hh := h (φ.mulOn hS hw)
  rw [φ.mulOn_derivativeLp hS hν e w dw hw hdw, φ.mulOn_toLp hS w hw,
    inner_add_right] at hh
  rw [inner_add_left, w.inner_map_left, w.inner_map_left, dw.inner_map_left]
  linarith

end IsWeakSpatialDerivative
end Carleman
