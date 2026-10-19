module

public import Carleman.Weights.IntrinsicSmoothClosure
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The actual interior Gaussian weight used in the continuous heat argument.
All first and second derivatives below are genuine Frechet derivatives. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ}

def interiorQuadratic (c x : SpatialCoordinates d) : ℝ := -‖x-c‖^2

def interiorGaussian (c : SpatialCoordinates d) (l : ℝ) (x : SpatialCoordinates d) : ℝ :=
  Real.exp (l*interiorQuadratic c x)

def interiorCarlemanProfile (c : SpatialCoordinates d) (l : ℝ) (x : SpatialCoordinates d) : ℝ :=
  interiorGaussian c l x-2

theorem interiorQuadratic_contDiff (c : SpatialCoordinates d) :
    ContDiff ℝ ∞ (interiorQuadratic c) :=
  ((contDiff_id.sub contDiff_const).norm_sq ℝ).neg

theorem interiorGaussian_contDiff (c : SpatialCoordinates d) (l : ℝ) :
    ContDiff ℝ ∞ (interiorGaussian c l) :=
  (contDiff_const.mul (interiorQuadratic_contDiff c)).exp

theorem interiorCarlemanProfile_contDiff (c : SpatialCoordinates d) (l : ℝ) :
    ContDiff ℝ ∞ (interiorCarlemanProfile c l) :=
  (interiorGaussian_contDiff c l).sub contDiff_const

theorem interiorQuadratic_hasFDerivAt (c x : SpatialCoordinates d) :
    HasFDerivAt (interiorQuadratic c) ((-2:ℝ) • innerSL ℝ (x-c)) x := by
  have h := ((hasFDerivAt_id x).sub_const c).norm_sq.neg
  change HasFDerivAt (fun y => -‖y-c‖^2) _ x
  convert! h using 1
  ext u
  simp only [smul_apply,smul_eq_mul,neg_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,id_eq]
  ring

theorem interiorGaussian_hasFDerivAt (c : SpatialCoordinates d) (l : ℝ)
    (x : SpatialCoordinates d) :
    HasFDerivAt (interiorGaussian c l)
      ((-2*l*interiorGaussian c l x) • innerSL ℝ (x-c)) x := by
  have h := ((interiorQuadratic_hasFDerivAt c x).const_mul l).exp
  change HasFDerivAt (fun y => Real.exp (l*interiorQuadratic c y)) _ x
  convert! h using 1
  ext u
  simp only [interiorGaussian,smul_apply,smul_eq_mul]
  ring

theorem interiorCarlemanProfile_hasFDerivAt (c : SpatialCoordinates d) (l : ℝ)
    (x : SpatialCoordinates d) :
    HasFDerivAt (interiorCarlemanProfile c l)
      ((-2*l*interiorGaussian c l x) • innerSL ℝ (x-c)) x :=
  (interiorGaussian_hasFDerivAt c l x).sub_const 2

theorem interiorGaussian_fderiv_apply (c : SpatialCoordinates d) (l : ℝ)
    (x u : SpatialCoordinates d) :
    fderiv ℝ (interiorGaussian c l) x u=
      -2*l*interiorGaussian c l x*inner ℝ (x-c) u := by
  rw [(interiorGaussian_hasFDerivAt c l x).fderiv]
  rfl

theorem interiorCarlemanProfile_fderiv_apply (c : SpatialCoordinates d) (l : ℝ)
    (x u : SpatialCoordinates d) :
    fderiv ℝ (interiorCarlemanProfile c l) x u=
      -2*l*interiorGaussian c l x*inner ℝ (x-c) u := by
  rw [(interiorCarlemanProfile_hasFDerivAt c l x).fderiv]
  rfl

theorem interiorGaussian_pos (c : SpatialCoordinates d) (l : ℝ) (x : SpatialCoordinates d) :
    0 < interiorGaussian c l x := Real.exp_pos _

theorem interiorGaussian_le_one (c : SpatialCoordinates d) {l : ℝ} (hl : 0 ≤ l)
    (x : SpatialCoordinates d) : interiorGaussian c l x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonneg_of_nonpos hl (neg_nonpos.mpr (sq_nonneg _))

theorem interiorCarlemanProfile_bounds (c : SpatialCoordinates d) {l : ℝ} (hl : 0 ≤ l)
    (x : SpatialCoordinates d) : -2 < interiorCarlemanProfile c l x ∧
      interiorCarlemanProfile c l x ≤ -1 := by
  have hp := interiorGaussian_pos c l x
  have hu := interiorGaussian_le_one c hl x
  dsimp only [interiorCarlemanProfile]
  constructor <;> linarith

theorem interiorCarlemanProfile_hessian (c : SpatialCoordinates d) (l : ℝ)
    (x u v : SpatialCoordinates d) :
    fderiv ℝ (fun y => fderiv ℝ (interiorCarlemanProfile c l) y u) x v=
      4*l^2*interiorGaussian c l x*inner ℝ (x-c) u*inner ℝ (x-c) v-
        2*l*interiorGaussian c l x*inner ℝ v u := by
  have he : (fun y => fderiv ℝ (interiorCarlemanProfile c l) y u)=
      (fun y => -2*l*interiorGaussian c l y*inner ℝ (y-c) u) := by
    funext y
    exact interiorCarlemanProfile_fderiv_apply c l y u
  rw [he]
  have hinner := ((hasFDerivAt_id x).sub_const c).inner ℝ (hasFDerivAt_const u x)
  have h := ((interiorGaussian_hasFDerivAt c l x).const_mul (-2*l)).mul hinner
  have hf := congrArg (fun A : SpatialCoordinates d →L[ℝ] ℝ => A v) h.fderiv
  convert! hf using 1
  simp only [smul_apply,smul_eq_mul,add_apply,
    ContinuousLinearMap.comp_apply,fderivInnerCLM_apply,ContinuousLinearMap.prod_apply,
    zero_apply,ContinuousLinearMap.id_apply,inner_zero_right,zero_add,id_eq]
  change 4*l^2*interiorGaussian c l x*inner ℝ (x-c) u*inner ℝ (x-c) v-
      2*l*interiorGaussian c l x*inner ℝ v u =
    (-2*l*interiorGaussian c l x)*inner ℝ v u+
      inner ℝ (x-c) u*((-2*l)*((-2*l*interiorGaussian c l x)*inner ℝ (x-c) v))
  ring

end Carleman
