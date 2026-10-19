module

public import Carleman.Spatial.MollifiedHessianEnergy
public import Carleman.Spatial.SmoothH2NodalGradient

/-! The smooth nodal estimates applied to actual local mollifications of
every original weak H² jet. The controlling Hessian is the original jet's
field, with constants independent of the mollifier and its radius. Passage
to nodal values of the unmollified weak state is not asserted here. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem WeakSobolevJet.mollified_nodal_value_integral
    (hS : MeasurableSet S) (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (hd : d ≤ 3)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    (hinside : ∀ x ∈ simplicialCell T.points, ∀ y ∈ tsupport κ.value, x-y ∈ S)
    {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D) :
    let U := zeroExtendLp hS (WeakSobolevJet.value u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
    (∫ x in simplicialCell T.points, (U x-simplexNodalInterpolant T (fun i => U (T.points i)) x)^2) ≤
      16*(tensorCoordinateBound d 2)^2*(d:ℝ)^2*D^4*‖WeakSobolevJet.field 2 u‖^2 := by
  intro U
  have he := WeakSobolevJet.mollified_hessian_energy_le hS (simplicialCell_measurable T.points) u κ hκ hunit hinside
  have hb := simplexNodal_smooth_h2_value_integral T hd
    ((κ.smooth_convolution (zeroExtendLp hS (WeakSobolevJet.value u))).of_le (by simp)) hD hdiam
  exact (hb.trans (mul_le_mul_of_nonneg_left he.2 (by positivity))).trans_eq (by ring)

theorem WeakSobolevJet.mollified_nodal_gradient_integral
    (hS : MeasurableSet S) (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (hd : d ≤ 3)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    (hinside : ∀ x ∈ simplicialCell T.points, ∀ y ∈ tsupport κ.value, x-y ∈ S)
    {a : SpatialCoordinates d} {r D γ : ℝ} (hr : 0 < r) (hD : 0 ≤ D)
    (hball : Metric.ball a r ⊆ simplicialCell T.points) (hshape : D ≤ γ*r)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ D) :
    let U := zeroExtendLp hS (WeakSobolevJet.value u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
    (∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ U x-
      affineScalarDerivative (simplexNodalInterpolant T (fun i => U (T.points i))))‖^2) ≤
      ((2:ℝ)^d*(d:ℝ)+128*γ^2*‖derivativeOneFiber (d := d)‖^2)*
        (tensorCoordinateBound d 2)^2*(d:ℝ)^2*D^2*‖WeakSobolevJet.field 2 u‖^2 := by
  intro U
  have he := WeakSobolevJet.mollified_hessian_energy_le hS (simplicialCell_measurable T.points) u κ hκ hunit hinside
  have hb := simplexNodal_smooth_h2_gradient_integral T hd
    ((κ.smooth_convolution (zeroExtendLp hS (WeakSobolevJet.value u))).of_le (by simp)) hr hD hball hshape hdiam
  exact (hb.trans (mul_le_mul_of_nonneg_left he.2 (by positivity))).trans_eq (by ring)

end Carleman
