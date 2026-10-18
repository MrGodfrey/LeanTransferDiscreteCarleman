module

public import Carleman.Geometry.CoordinateBoxConvexity
public import Carleman.Spatial.AffineChangeVolume
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Positive diagonal coordinate changes, their actual determinant and Euclidean
norm bounds. These are the physical-box scaling maps, not assigned norm models. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def coordinateDilation (ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) :
    SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d :=
  (show SpatialCoordinates d ≃ₗ[ℝ] SpatialCoordinates d from
    { toFun := fun x => WithLp.toLp 2 (fun i => ℓ i*x i)
      invFun := fun x => WithLp.toLp 2 (fun i => (ℓ i)⁻¹*x i)
      left_inv := fun x => by
        apply PiLp.ext
        intro i
        change (ℓ i)⁻¹*(ℓ i*x i)=x i
        rw [← mul_assoc,inv_mul_cancel₀ (hℓ i).ne',one_mul]
      right_inv := fun x => by
        apply PiLp.ext
        intro i
        change ℓ i*((ℓ i)⁻¹*x i)=x i
        rw [← mul_assoc,mul_inv_cancel₀ (hℓ i).ne',one_mul]
      map_add' := fun x y => by
        apply PiLp.ext
        intro i
        exact mul_add _ _ _
      map_smul' := fun c x => by
        apply PiLp.ext
        intro i
        change ℓ i*(c*x i)=c*(ℓ i*x i)
        ring }).toContinuousLinearEquiv

theorem coordinateDilation_apply (ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (x : SpatialCoordinates d) (i : Fin d) : coordinateDilation ℓ hℓ x i=ℓ i*x i := rfl

theorem coordinateDilation_symm_apply (ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (x : SpatialCoordinates d) (i : Fin d) : (coordinateDilation ℓ hℓ).symm x i=(ℓ i)⁻¹*x i := rfl

theorem coordinateDilation_basis (ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) (i : Fin d) :
    coordinateDilation ℓ hℓ (EuclideanSpace.basisFun (Fin d) ℝ i)=
      ℓ i • EuclideanSpace.basisFun (Fin d) ℝ i := by
  apply PiLp.ext
  intro j
  simp only [coordinateDilation_apply,EuclideanSpace.basisFun_apply]
  by_cases h : i=j
  · subst j
    simp
  · simp [Ne.symm h]

theorem coordinateDilation_norm_le (ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ i, ℓ i ≤ L) (x : SpatialCoordinates d) :
    ‖coordinateDilation ℓ hℓ x‖ ≤ L*‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [coordinateDilation_apply,mul_pow]
  exact mul_le_mul_of_nonneg_right (sq_le_sq₀ (hℓ i).le hL |>.mpr (hbound i)) (sq_nonneg _)

theorem coordinateDilation_symm_norm_le (ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (m : ℝ) (hm : 0 < m) (hbound : ∀ i, m ≤ ℓ i) (x : SpatialCoordinates d) :
    ‖(coordinateDilation ℓ hℓ).symm x‖ ≤ m⁻¹*‖x‖ := by
  have he : (coordinateDilation ℓ hℓ).symm x =
      coordinateDilation (fun i => (ℓ i)⁻¹) (fun i => inv_pos.mpr (hℓ i)) x := by
    apply PiLp.ext
    intro i
    rfl
  rw [he]
  exact coordinateDilation_norm_le _ _ _ (inv_pos.mpr hm).le
    (fun i => inv_anti₀ hm (hbound i)) x

theorem coordinateDilation_jacobian (ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) :
    affineJacobian (coordinateDilation ℓ hℓ)=∏ i, ℓ i := by
  classical
  have hm : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (coordinateDilation ℓ hℓ).toLinearMap =
      Matrix.diagonal ℓ := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change (coordinateDilation ℓ hℓ (EuclideanSpace.basisFun (Fin d) ℝ j)) i = _
    rw [coordinateDilation_basis]
    by_cases h : i=j
    · subst j
      simp [EuclideanSpace.basisFun_apply]
    · simp [EuclideanSpace.basisFun_apply,h]
  rw [affineJacobian,← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
    hm,Matrix.det_diagonal,abs_of_pos (Finset.prod_pos fun i _ => hℓ i)]

end Carleman
