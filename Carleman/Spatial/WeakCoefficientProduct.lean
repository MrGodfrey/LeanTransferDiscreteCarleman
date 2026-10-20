module

public import Carleman.Spatial.MollifiedProductTests

/-! Distributional multiplication by a bounded weakly differentiable
coefficient. No smooth representative of the coefficient is assumed. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

namespace SpatialTest

theorem inner_valueMultiplier (φ : SpatialTest S)
    (w : BoundedMultiplier (volume.restrict S))
    (W u : Lp ℝ 2 (volume.restrict S)) (hW : W =ᵐ[volume.restrict S] w.value) :
    inner ℝ W ((φ.valueMultiplier (volume.restrict S)).map u)=
      inner ℝ (w.map u) (φ.toLp (volume.restrict S)) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hW,(φ.valueMultiplier (volume.restrict S)).map_ae u,
    w.map_ae u,φ.toLp_ae (volume.restrict S)] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  simp only [RCLike.inner_apply,conj_trivial,smul_eq_mul]
  change (φ.value x*u x)*w.value x=φ.value x*(w.value x*u x)
  ring
end SpatialTest
namespace IsWeakSpatialDerivative

theorem mul_bounded_of_weakLp (hS : IsOpen S)
    {e : SpatialCoordinates d} {u v W DW : Lp ℝ 2 (volume.restrict S)}
    (huv : IsWeakSpatialDerivative (volume.restrict S) S e u v)
    (w dw : BoundedMultiplier (volume.restrict S))
    (hW : W =ᵐ[volume.restrict S] w.value)
    (hDW : DW =ᵐ[volume.restrict S] dw.value)
    (hw : IsWeakSpatialDerivative (volume.restrict S) S e W DW) :
    IsWeakSpatialDerivative (volume.restrict S) S e (w.map u) (w.map v+dw.map u) := by
  intro φ
  have hl := (tendsto_const_nhds (x := W)).inner (𝕜 := ℝ) (φ.mollifiedProduct_derivativeLp_tendsto hS huv)
  have hr := ((tendsto_const_nhds (x := DW)).inner (𝕜 := ℝ) (φ.mollifiedProduct_toLp_tendsto hS u)).neg
  have he : inner ℝ W ((φ.valueMultiplier (volume.restrict S)).map v+
        ((φ.derivativeTest e).valueMultiplier (volume.restrict S)).map u)=
      -inner ℝ DW ((φ.valueMultiplier (volume.restrict S)).map u) := by
    apply tendsto_nhds_unique hl
    apply hr.congr'
    exact Eventually.of_forall fun n => (hw (φ.mollifiedProduct hS u n)).symm
  rw [inner_add_right,φ.inner_valueMultiplier w W v hW,
    (φ.derivativeTest e).inner_valueMultiplier w W u hW,
    SpatialTest.derivativeTest_toLp,φ.inner_valueMultiplier dw DW u hDW] at he
  rw [inner_add_left]
  linarith only [he]
end IsWeakSpatialDerivative
namespace BoundedMultiplier
variable {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasure ν]

def toLp (w : BoundedMultiplier ν) : Lp ℝ 2 ν :=
  (MemLp.of_bound w.measurable w.bound (by simpa only [Real.norm_eq_abs] using w.bounded)).toLp w.value

theorem toLp_ae (w : BoundedMultiplier ν) : w.toLp =ᵐ[ν] w.value := MemLp.coeFn_toLp _
end BoundedMultiplier

/-- The actual distributional derivative of bounded measurable coefficients. -/
def IsWeakMultiplierDerivative (S : Set (SpatialCoordinates d)) (e : SpatialCoordinates d)
    (w dw : BoundedMultiplier (volume.restrict S)) : Prop :=
  ∀ φ : SpatialTest S,
    (∫ x in S, fderiv ℝ φ.value x e*w.value x) = -(∫ x in S, φ.value x*dw.value x)

theorem isWeakMultiplierDerivative_iff [IsFiniteMeasure (volume.restrict S)]
    {e : SpatialCoordinates d} {w dw : BoundedMultiplier (volume.restrict S)} :
    IsWeakMultiplierDerivative S e w dw ↔
      IsWeakSpatialDerivative (volume.restrict S) S e w.toLp dw.toLp := by
  rw [IsWeakSpatialDerivative.iff_integral]
  have h1 (φ : SpatialTest S) :
      (∫ x in S, fderiv ℝ φ.value x e*w.toLp x) = ∫ x in S, fderiv ℝ φ.value x e*w.value x := by
    apply integral_congr_ae
    filter_upwards [w.toLp_ae] with x hx
    rw [hx]
  have h2 (φ : SpatialTest S) :
      (∫ x in S, φ.value x*dw.toLp x) = ∫ x in S, φ.value x*dw.value x := by
    apply integral_congr_ae
    filter_upwards [dw.toLp_ae] with x hx
    rw [hx]
  simp only [IsWeakMultiplierDerivative,h1,h2]

theorem IsWeakSpatialDerivative.mul_weakCoefficient [IsFiniteMeasure (volume.restrict S)]
    (hS : IsOpen S) {e : SpatialCoordinates d} {u v : Lp ℝ 2 (volume.restrict S)}
    (huv : IsWeakSpatialDerivative (volume.restrict S) S e u v)
    (w dw : BoundedMultiplier (volume.restrict S))
    (hw : IsWeakMultiplierDerivative S e w dw) :
    IsWeakSpatialDerivative (volume.restrict S) S e (w.map u) (w.map v+dw.map u) :=
  huv.mul_bounded_of_weakLp hS w dw w.toLp_ae dw.toLp_ae
    (isWeakMultiplierDerivative_iff.mp hw)

end Carleman
