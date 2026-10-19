module

public import Carleman.Weights.InteriorHeatCoefficients

/-! The actual matrix term of the pointwise heat identity after Gaussian specialization. -/
@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace Carleman
variable {d : ℕ}

theorem interiorGaussianHeatPhase_second_spatialD (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (t : ℝ) (x v w : SpatialCoordinates d) :
    smoothD (0,w) (smoothD (0,v) (interiorGaussianHeatPhase c l q)) (t,x)=
      q t*(4*l^2*interiorGaussian c l x*inner ℝ (x-c) v*inner ℝ (x-c) w-
        2*l*interiorGaussian c l x*inner ℝ w v) := by
  have hρ := interiorCarlemanProfile_contDiff c l
  have he : smoothD (0,v) (interiorGaussianHeatPhase c l q)=
      separableHeatPhase q (smoothD v (interiorCarlemanProfile c l)) :=
    funext fun y => separableHeatPhase_spatialD hq hρ y.1 y.2 v
  rw [he,separableHeatPhase_spatialD hq (smoothD_contDiff hρ v)]
  change q t*fderiv ℝ (fun y => fderiv ℝ (interiorCarlemanProfile c l) y v) x w=_
  rw [interiorCarlemanProfile_hessian]

private theorem finite_radial_matrix (A B : ℝ) (r v : Fin d → ℝ) :
    (∑ i, ∑ j, (A*r j*r i-B*(if i=j then 1 else 0))*v i*v j)=
      A*(∑ i, r i*v i)^2-B*∑ i, (v i)^2 := by
  classical
  have he i j : (A*r j*r i-B*(if i=j then 1 else 0))*v i*v j=
      A*(r i*v i)*(r j*v j)-(if j=i then B*(v i)^2 else 0) := by
    by_cases h : i=j
    · subst j
      simp only [ite_true]
      ring
    · simp only [h,Ne.symm h,ite_false,mul_zero,sub_zero]
      ring
  simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_ite_eq',Finset.mem_univ,
    ite_true,← Finset.sum_mul]
  ring

theorem interiorGaussianHeatMatrixEnergy_formula (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (z : (ℝ × SpatialCoordinates d) → ℝ) (t : ℝ) (x : SpatialCoordinates d) :
    pointwiseHeatMatrixEnergy spaceTimeSpatialDirection (interiorGaussianHeatPhase c l q)
      (interiorGaussianHeatPsi c l q) z (t,x)=
      4*q t*l*interiorGaussian c l x*directionalEnergy spaceTimeSpatialDirection z (t,x)+
      8*q t*l^2*interiorGaussian c l x*
        (∑ i, (x-c) i*smoothD (spaceTimeSpatialDirection i) z (t,x))^2 := by
  have hij (i j : Fin d) : inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (EuclideanSpace.basisFun (Fin d) ℝ j)=(if i=j then 1 else 0) := by
    rw [EuclideanSpace.basisFun_inner]
    simp [EuclideanSpace.basisFun_apply]
  have he i j : smoothD (spaceTimeSpatialDirection i)
      (smoothD (spaceTimeSpatialDirection j) (interiorGaussianHeatPhase c l q)) (t,x)=
      (4*q t*l^2*interiorGaussian c l x)*(x-c) j*(x-c) i-
      (2*q t*l*interiorGaussian c l x)*(if i=j then 1 else 0) := by
    change smoothD (0,EuclideanSpace.basisFun (Fin d) ℝ i)
      (smoothD (0,EuclideanSpace.basisFun (Fin d) ℝ j) _) (t,x)=_
    rw [interiorGaussianHeatPhase_second_spatialD c l hq,EuclideanSpace.inner_basisFun_real,
      EuclideanSpace.inner_basisFun_real,hij]
    ring
  have hH : directionalHessianForm spaceTimeSpatialDirection (interiorGaussianHeatPhase c l q) z (t,x)=
      (4*q t*l^2*interiorGaussian c l x)*
        (∑ i, (x-c) i*smoothD (spaceTimeSpatialDirection i) z (t,x))^2-
      (2*q t*l*interiorGaussian c l x)*directionalEnergy spaceTimeSpatialDirection z (t,x) := by
    simp only [directionalHessianForm,he,directionalEnergy]
    exact finite_radial_matrix _ _ _ _
  unfold pointwiseHeatMatrixEnergy
  rw [hH]
  simp only [interiorGaussianHeatPsi,separableHeatPhase]
  ring

theorem interiorGaussianHeatMatrixEnergy_coercive (c : SpatialCoordinates d) (l : ℝ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (z : (ℝ × SpatialCoordinates d) → ℝ) (t : ℝ) (ht : 0 ≤ q t) (x : SpatialCoordinates d) :
    4*q t*l*interiorGaussian c l x*directionalEnergy spaceTimeSpatialDirection z (t,x) ≤
    pointwiseHeatMatrixEnergy spaceTimeSpatialDirection (interiorGaussianHeatPhase c l q)
      (interiorGaussianHeatPsi c l q) z (t,x) := by
  rw [interiorGaussianHeatMatrixEnergy_formula c l hq]
  have hn : 0 ≤ 8*q t*l^2*interiorGaussian c l x*
      (∑ i, (x-c) i*smoothD (spaceTimeSpatialDirection i) z (t,x))^2 := by
    positivity [interiorGaussian_pos c l x]
  exact le_add_of_nonneg_right hn

end Carleman
