module

public import Carleman.Spatial.SmoothLaplacianProduct
public import Carleman.Spatial.WeakPoissonConvolution

/-! The exact localized Poisson identity for a smooth convolution.
The cutoff support, rather than the entire ambient domain, must remain
inside the region where the reflected convolution kernel is admissible. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution BigOperators ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem spatialLaplacian_smooth {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (spatialLaplacian f) := by
  apply ContDiff.sum
  intro i _
  have hd := (hf.fderiv_right (by simp)).clm_apply
    (contDiff_const : ContDiff ℝ ∞ (fun _ : SpatialCoordinates d => EuclideanSpace.basisFun (Fin d) ℝ i))
  exact (hd.fderiv_right (by simp)).clm_apply contDiff_const

theorem SpatialTest.laplacian_eq_zero_of_notMem_tsupport (η : SpatialTest S)
    {x : SpatialCoordinates d} (hx : x ∉ tsupport η.value) : spatialLaplacian η.value x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hn : x ∉ tsupport (η.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).value :=
    fun h => hx (tsupport_fderiv_apply_subset ℝ _ h)
  exact congrArg (fun A : SpatialCoordinates d →L[ℝ] ℝ => A (EuclideanSpace.basisFun (Fin d) ℝ i))
    (fderiv_of_notMem_tsupport ℝ hn)

theorem IsWeakNegativeLaplacian.cutoff_convolution (hS : MeasurableSet S)
    {u : WeakSobolevJet d 1 (volume.restrict S) S} {f : Lp ℝ 2 (volume.restrict S)}
    (h : IsWeakNegativeLaplacian u f) (η : SpatialTest S)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hinside : ∀ x ∈ tsupport η.value, ∀ y ∈ tsupport κ.value, x-y ∈ S)
    (x : SpatialCoordinates d) :
    let U := zeroExtendLp hS (WeakSobolevJet.value u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value;
    spatialLaplacian (fun y => η.value y*U y) x =
      -η.value x*(zeroExtendLp hS f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x +
      2*(∑ i : Fin d, (fderiv ℝ η.value x (EuclideanSpace.basisFun (Fin d) ℝ i))*
        (zeroExtendLp hS (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x) +
      (spatialLaplacian η.value x)*U x := by
  intro U
  rw [spatialLaplacian_mul η.smooth (κ.smooth_convolution _)]
  change η.value x*spatialLaplacian U x +
    2*(∑ i : Fin d, (fderiv ℝ η.value x (EuclideanSpace.basisFun (Fin d) ℝ i))*
      (fderiv ℝ U x (EuclideanSpace.basisFun (Fin d) ℝ i))) + U x*spatialLaplacian η.value x = _
  by_cases hx : x ∈ tsupport η.value
  · have hl := h.mollified_laplacian hS κ x (hinside x hx)
    change -spatialLaplacian U x = _ at hl
    have hd (i : Fin d) : fderiv ℝ U x (EuclideanSpace.basisFun (Fin d) ℝ i) =
        (zeroExtendLp hS (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x :=
      ((u.property 0 Sym.nil i).zeroExtend hS).fderiv_convolution_local κ x (hinside x hx)
    simp_rw [hd]
    rw [← hl]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hx,fderiv_of_notMem_tsupport ℝ hx,
      η.laplacian_eq_zero_of_notMem_tsupport hx]
    simp

end Carleman
