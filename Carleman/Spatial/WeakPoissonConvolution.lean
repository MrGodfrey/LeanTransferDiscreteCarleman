module

public import Carleman.Spatial.LocalHessianConvolution
public import Carleman.Spatial.WeakProductComponents

/-! Mollification of the actual weak Poisson equation on the interior.
Only the support of the reflected kernel is required to stay in the domain;
no second weak derivative or H² extension of the original state is used. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem IsWeakSpatialDerivative.mixed_convolution_first
    {e₀ : SpatialCoordinates d} {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (h : IsWeakSpatialDerivative volume S e₀ u v)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d))) (x e₁ : SpatialCoordinates d)
    (hinside : ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    fderiv ℝ (fun y => fderiv ℝ
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) y e₁) x e₀ =
      (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => fderiv ℝ κ.value y e₁)) x := by
  have he : (fun y => fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) y e₁) =
      u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (κ.directionalKernel e₁).value :=
    funext fun y => κ.fderiv_convolution_integral u y e₁
  rw [he,(κ.directionalKernel e₁).fderiv_convolution_integral]
  exact h.convolution_exchange_local (κ.directionalKernel e₁) x
    (fun y hy => hinside y (κ.directionalKernel_support e₁ hy))

theorem IsWeakNegativeLaplacian.integral_test
    {u : WeakSobolevJet d 1 (volume.restrict S) S} {f : Lp ℝ 2 (volume.restrict S)}
    (h : IsWeakNegativeLaplacian u f) (φ : SpatialTest S) :
    (∑ i : Fin d, ∫ x in S, fderiv ℝ φ.value x (EuclideanSpace.basisFun (Fin d) ℝ i) *
      derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) x) =
      ∫ x in S, φ.value x*f x := by
  have hh := h φ
  rw [weakGradientPairing_coordinates] at hh
  simp only [φ.sobolevJet_derivative,L2.inner_def] at hh
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [φ.derivativeLp_ae (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)] with x hx
    simp only [hx,RCLike.inner_apply,conj_trivial]
  · apply integral_congr_ae
    filter_upwards [φ.toLp_ae (volume.restrict S)] with x hx
    simp only [hx,RCLike.inner_apply,conj_trivial]

theorem IsWeakNegativeLaplacian.convolution_identity (hS : MeasurableSet S)
    {u : WeakSobolevJet d 1 (volume.restrict S) S} {f : Lp ℝ 2 (volume.restrict S)}
    (h : IsWeakNegativeLaplacian u f)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d))) (x : SpatialCoordinates d)
    (hinside : ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    -(∑ i : Fin d, (zeroExtendLp hS
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => fderiv ℝ κ.value y (EuclideanSpace.basisFun (Fin d) ℝ i))) x) =
      (zeroExtendLp hS f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x := by
  have hh := h.integral_test (κ.reflectedWithin x hinside)
  change (∑ i : Fin d, ∫ y in S, fderiv ℝ (κ.reflected x).value y
    (EuclideanSpace.basisFun (Fin d) ℝ i)*
      derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u) y) =
    ∫ y in S, κ.value (x-y)*f y at hh
  simp_rw [κ.reflected_derivative,neg_mul,integral_neg] at hh
  rw [Finset.sum_neg_distrib] at hh
  have he (v : Lp ℝ 2 (volume.restrict S)) (g : SpatialCoordinates d → ℝ) :
      (∫ y, zeroExtendLp hS v y*g y) = ∫ y in S, v y*g y := by
    simpa only [mul_comm] using integral_mul_zeroExtendLp hS v g
  simp only [convolution,ContinuousLinearMap.lsmul_apply,smul_eq_mul]
  simp_rw [he]
  simpa only [mul_comm] using hh

theorem IsWeakNegativeLaplacian.mollified_laplacian (hS : MeasurableSet S)
    {u : WeakSobolevJet d 1 (volume.restrict S) S} {f : Lp ℝ 2 (volume.restrict S)}
    (h : IsWeakNegativeLaplacian u f)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d))) (x : SpatialCoordinates d)
    (hinside : ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    let U := zeroExtendLp hS (WeakSobolevJet.value u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value;
    -(∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ U y (EuclideanSpace.basisFun (Fin d) ℝ i))
      x (EuclideanSpace.basisFun (Fin d) ℝ i)) =
      (zeroExtendLp hS f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) x := by
  intro U
  have he (i : Fin d) := ((u.property 0 Sym.nil i).zeroExtend hS).mixed_convolution_first κ x
    (EuclideanSpace.basisFun (Fin d) ℝ i) hinside
  change -(∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ
    (zeroExtendLp hS (WeakSobolevJet.value u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value)
      y (EuclideanSpace.basisFun (Fin d) ℝ i)) x (EuclideanSpace.basisFun (Fin d) ℝ i)) = _
  calc
    _ = -(∑ i : Fin d, (zeroExtendLp hS
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => fderiv ℝ κ.value y (EuclideanSpace.basisFun (Fin d) ℝ i))) x) := by
      congr 1
      exact Finset.sum_congr rfl (fun i _ => he i)
    _ = _ := h.convolution_identity hS κ x hinside

end Carleman
