module

public import Carleman.Spatial.MollifiedConeInterpolation
public import Carleman.Spatial.LocalMollifierLimit

/-! The local interpolation estimate for genuine weak derivatives on the
original open domain. Zero extension is used only for L² convolution; the
weak identity is required and transferred only inside the domain. -/
@[expose] public noncomputable section
open MeasureTheory Set Metric
open scoped Convolution
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem weak_cone_interpolation_fullLp (hS : IsOpen S) (p : InwardConePatch S)
    {z : SpatialCoordinates d} {t : ℝ} (hz : ‖z-p.direction‖ ≤ 1)
    (ht : 0 < t) (hheight : t ≤ p.height)
    {u v w : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (huv : IsWeakSpatialDerivative volume S z u v)
    (hvw : IsWeakSpatialDerivative volume S z v w) :
    bochnerL2Norm (volume.restrict (p.region ∩ S)) v ≤ 2/t*‖u‖+t*‖w‖ := by
  apply local_mollifier_norm_bound (p.open_region.inter hS) v (by positivity)
  intro n
  apply mollified_cone_interpolation p (isOpen_interiorRegion _ _).measurableSet
    (fun _ hx => interiorRegion_closedBall_subset hx) hz ht hheight huv hvw
    (spatialMollifier d n) _ (spatialMollifier_nonneg n) (spatialMollifier_integral n)
  exact le_of_eq (shrinkingBump d n).tsupport_normed_eq

theorem weak_cone_interpolation (hS : IsOpen S) (p : InwardConePatch S)
    {z : SpatialCoordinates d} {t : ℝ} (hz : ‖z-p.direction‖ ≤ 1)
    (ht : 0 < t) (hheight : t ≤ p.height)
    {u v w : Lp ℝ 2 ((volume : Measure (SpatialCoordinates d)).restrict S)}
    (huv : IsWeakSpatialDerivative (volume.restrict S) S z u v)
    (hvw : IsWeakSpatialDerivative (volume.restrict S) S z v w) :
    bochnerL2Norm (volume.restrict (p.region ∩ S)) v ≤ 2/t*‖u‖+t*‖w‖ := by
  have he := weak_cone_interpolation_fullLp hS p hz ht hheight
    (huv.zeroExtend hS.measurableSet) (hvw.zeroExtend hS.measurableSet)
  rw [zeroExtendLp_norm,zeroExtendLp_norm] at he
  have hae : zeroExtendLp hS.measurableSet v =ᵐ[volume.restrict (p.region ∩ S)] v :=
    (zeroExtendLp_ae_restrict hS.measurableSet v).filter_mono
      (ae_mono (Measure.restrict_mono inter_subset_right le_rfl))
  rwa [bochnerL2Norm_congr_ae hae] at he
end Carleman
