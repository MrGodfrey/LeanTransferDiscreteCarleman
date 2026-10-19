module

public import Carleman.Spatial.CompactTestH2Jet

/-! The classical Laplacian product rule for actual smooth functions,
and compactly supported localization by an original spatial test. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace Carleman
variable {d : ℕ}

def spatialLaplacian (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin d) ℝ i)) x
    (EuclideanSpace.basisFun (Fin d) ℝ i)

theorem smooth_directional_mul {f g : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x e : SpatialCoordinates d) :
    fderiv ℝ (fun y => f y*g y) x e =
      f x*fderiv ℝ g x e + g x*fderiv ℝ f x e := by
  change fderiv ℝ (f*g) x e = _
  rw [fderiv_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]

theorem smooth_second_directional_mul {f g : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x e : SpatialCoordinates d) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => f z*g z) y e) x e =
      f x*fderiv ℝ (fun y => fderiv ℝ g y e) x e +
      2*(fderiv ℝ f x e)*(fderiv ℝ g x e) +
      g x*fderiv ℝ (fun y => fderiv ℝ f y e) x e := by
  have hdf : ContDiff ℝ ∞ (fun y => fderiv ℝ f y e) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hdg : ContDiff ℝ ∞ (fun y => fderiv ℝ g y e) :=
    (hg.fderiv_right (by simp)).clm_apply contDiff_const
  have he : (fun y => fderiv ℝ (fun z => f z*g z) y e) =
      (fun y => f y*fderiv ℝ g y e + g y*fderiv ℝ f y e) :=
    funext fun y => smooth_directional_mul hf hg y e
  rw [he]
  change fderiv ℝ ((fun y => f y*fderiv ℝ g y e) +
    (fun y => g y*fderiv ℝ f y e)) x e = _
  rw [fderiv_add ((hf.mul hdg).differentiable (by simp) x)
    ((hg.mul hdf).differentiable (by simp) x),add_apply,
    smooth_directional_mul hf hdg,smooth_directional_mul hg hdf]
  ring

theorem spatialLaplacian_mul {f g : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : SpatialCoordinates d) :
    spatialLaplacian (fun y => f y*g y) x =
      f x*spatialLaplacian g x +
        2*(∑ i : Fin d, (fderiv ℝ f x (EuclideanSpace.basisFun (Fin d) ℝ i))*
          (fderiv ℝ g x (EuclideanSpace.basisFun (Fin d) ℝ i))) +
      g x*spatialLaplacian f x := by
  simp only [spatialLaplacian,smooth_second_directional_mul hf hg,Finset.sum_add_distrib,
    Finset.mul_sum,mul_assoc]

namespace SpatialTest
variable {S : Set (SpatialCoordinates d)}

def mulSmooth (η : SpatialTest S) {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ ∞ f) : SpatialTest S where
  value x := η.value x*f x
  smooth := η.smooth.mul hf
  compact := η.compact.mul_right
  support := tsupport_mul_subset_left.trans η.support

theorem laplacianLp_ae (φ : SpatialTest S) :
    φ.laplacianLp =ᵐ[volume.restrict S] spatialLaplacian φ.value := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin d =>
    (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
      (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)),
    ae_all_iff.mpr (fun i : Fin d =>
      (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp_ae
        (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i))] with x hx hd
  change (∑ i : Fin d, (φ.derivativeTest (EuclideanSpace.basisFun (Fin d) ℝ i)).derivativeLp
    (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)) x = _
  rw [hx]
  exact Finset.sum_congr rfl (fun i _ => hd i)

end SpatialTest
end Carleman
