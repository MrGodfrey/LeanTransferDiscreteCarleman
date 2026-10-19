module

public import Carleman.Weights.InteriorHeatMatrix
public import Carleman.Spatial.SmoothDirectionalEnergy

/-! Actual Laplacian and gradient-energy derivatives of the Gaussian profile. -/
@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

theorem interiorCarlemanProfile_laplacian (c : SpatialCoordinates d) (l : ℝ)
    (x : SpatialCoordinates d) :
    spatialLaplacian (interiorCarlemanProfile c l) x=
      (4*l^2*‖x-c‖^2-2*(d:ℝ)*l)*interiorGaussian c l x := by
  have hn i : inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (EuclideanSpace.basisFun (Fin d) ℝ i)=1 := by
    rw [real_inner_self_eq_norm_sq,(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one,one_pow]
  have he i : fderiv ℝ (fun y => fderiv ℝ (interiorCarlemanProfile c l) y
      (EuclideanSpace.basisFun (Fin d) ℝ i)) x (EuclideanSpace.basisFun (Fin d) ℝ i)=
      (4*l^2*interiorGaussian c l x)*((x-c) i)^2-2*l*interiorGaussian c l x := by
    rw [interiorCarlemanProfile_hessian,hn,EuclideanSpace.inner_basisFun_real]
    ring
  unfold spatialLaplacian
  simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,← EuclideanSpace.real_norm_sq_eq]
  ring

theorem interiorCarlemanProfile_energy (c : SpatialCoordinates d) (l : ℝ)
    (x : SpatialCoordinates d) :
    directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) (interiorCarlemanProfile c l) x=
      4*l^2*(interiorGaussian c l x)^2*‖x-c‖^2 := by
  have he i : (smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) (interiorCarlemanProfile c l) x)^2=
      (4*l^2*(interiorGaussian c l x)^2)*((x-c) i)^2 := by
    rw [smoothD,interiorCarlemanProfile_fderiv_apply,EuclideanSpace.inner_basisFun_real]
    ring
  simp only [directionalEnergy,he,← Finset.mul_sum,← EuclideanSpace.real_norm_sq_eq]

theorem interiorCarlemanProfile_energy_fderiv (c : SpatialCoordinates d) (l : ℝ)
    (x v : SpatialCoordinates d) :
    fderiv ℝ (directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ)
      (interiorCarlemanProfile c l)) x v =
      8*l^2*(interiorGaussian c l x)^2*(1-2*l*‖x-c‖^2)*inner ℝ (x-c) v := by
  have he : directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) (interiorCarlemanProfile c l)=
      (fun y => 4*l^2*(interiorGaussian c l y)^2*‖y-c‖^2) :=
    funext (interiorCarlemanProfile_energy c l)
  rw [he]
  have h := (((interiorGaussian_hasFDerivAt c l x).pow 2).const_mul (4*l^2)).mul
    (((hasFDerivAt_id x).sub_const c).norm_sq)
  have hh := congrArg (fun A : SpatialCoordinates d →L[ℝ] ℝ => A v) h.fderiv
  convert! hh using 1
  simp only [add_apply,smul_apply,smul_eq_mul,innerSL_apply_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,id_eq]
  ring

theorem interiorCarlemanProfile_laplacian_fderiv (c : SpatialCoordinates d) (l : ℝ)
    (x v : SpatialCoordinates d) :
    fderiv ℝ (spatialLaplacian (interiorCarlemanProfile c l)) x v =
      (-8*l^3*‖x-c‖^2+(4*(d:ℝ)+8)*l^2)*interiorGaussian c l x*inner ℝ (x-c) v := by
  have he : spatialLaplacian (interiorCarlemanProfile c l)=
      (fun y => (4*l^2*‖y-c‖^2-2*(d:ℝ)*l)*interiorGaussian c l y) :=
    funext (interiorCarlemanProfile_laplacian c l)
  rw [he]
  have h := (((((hasFDerivAt_id x).sub_const c).norm_sq).const_mul (4*l^2)).sub_const
    (2*(d:ℝ)*l)).mul (interiorGaussian_hasFDerivAt c l x)
  have hh := congrArg (fun A : SpatialCoordinates d →L[ℝ] ℝ => A v) h.fderiv
  convert! hh using 1
  simp only [add_apply,smul_apply,smul_eq_mul,innerSL_apply_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,id_eq]
  ring

theorem interiorCarlemanProfile_energy_pair (c : SpatialCoordinates d) (l : ℝ)
    (x : SpatialCoordinates d) :
    directionalPair (EuclideanSpace.basisFun (Fin d) ℝ)
      (directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) (interiorCarlemanProfile c l))
      (interiorCarlemanProfile c l) x =
      32*l^4*(interiorGaussian c l x)^3*‖x-c‖^4-
        16*l^3*(interiorGaussian c l x)^3*‖x-c‖^2 := by
  have he i :
      smoothD (EuclideanSpace.basisFun (Fin d) ℝ i)
        (directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) (interiorCarlemanProfile c l)) x *
      smoothD (EuclideanSpace.basisFun (Fin d) ℝ i) (interiorCarlemanProfile c l) x =
      (-16*l^3*(interiorGaussian c l x)^3*(1-2*l*‖x-c‖^2))*((x-c) i)^2 := by
    simp only [smoothD,interiorCarlemanProfile_energy_fderiv,
      interiorCarlemanProfile_fderiv_apply,EuclideanSpace.inner_basisFun_real]
    ring
  simp only [directionalPair,he,← Finset.mul_sum,← EuclideanSpace.real_norm_sq_eq]
  ring

theorem interiorCarlemanProfile_gaussian_pair (c : SpatialCoordinates d) (l : ℝ)
    (x : SpatialCoordinates d) :
    directionalPair (EuclideanSpace.basisFun (Fin d) ℝ) (interiorGaussian c l)
      (interiorCarlemanProfile c l) x =
    directionalEnergy (EuclideanSpace.basisFun (Fin d) ℝ) (interiorCarlemanProfile c l) x := by
  unfold directionalPair directionalEnergy
  apply Finset.sum_congr rfl
  intro i _
  simp only [smoothD,interiorGaussian_fderiv_apply,interiorCarlemanProfile_fderiv_apply]
  ring

end Carleman
