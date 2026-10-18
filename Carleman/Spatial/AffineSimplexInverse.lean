module

public import Carleman.Spatial.AffineSimplexNorm
public import Carleman.Spatial.DerivativeFiberNorm

/-! Reference inverse estimates transported by genuine affine coordinates.
The uniform h⁻¹ bound uses an explicit geometric inverse-map bound. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

theorem affineSimplex_gradient_bound_sq (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ (L : SpatialCoordinates d →L[ℝ] ℝ)
      (B : SpatialCoordinates d →L[ℝ] SpatialCoordinates d),
      ‖derivativeOneFiber (L.comp B)‖ ≤ D*‖B‖*‖derivativeOneFiber L‖)
    (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d) (b : SpatialCoordinates d)
    (c : Fin (d+1) → ℝ) :
    ‖simplexNodalGradientLp (affineSimplex T A b) c‖^2 ≤
      affineJacobian A * ((D*‖A.symm.toContinuousLinearMap‖)^2*‖simplexNodalGradientLp T c‖^2) := by
  rw [affineSimplex_gradient_norm_sq,simplexNodalGradientLp_norm_sq]
  apply mul_le_mul_of_nonneg_left _ (affineJacobian_pos A).le
  rw [← integral_const_mul]
  apply integral_mono (integrable_const _) (integrable_const _)
  intro x
  have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    (hb (simplexNodalDerivativeLinear T c) A.symm.toContinuousLinearMap)
  nlinarith only [h]

theorem affineSimplex_inverse : ∃ C > (0:ℝ),
    ∀ (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d) (b : SpatialCoordinates d)
      (c : Fin (d+1) → ℝ),
    ‖simplexNodalGradientLp (affineSimplex T A b) c‖ ≤
      C*‖A.symm.toContinuousLinearMap‖*‖simplexNodalLp (affineSimplex T A b) c‖ := by
  obtain ⟨D,hD,hdb⟩ := derivativeOneFiber_comp_bound (d := d)
  obtain ⟨R,hR,hrb⟩ := simplex_reference_inverse T
  refine ⟨D*R,mul_pos hD hR,?_⟩
  intro A b c
  have hJ := (affineJacobian_pos A).le
  have hr2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hrb c)
  have hsq : ‖simplexNodalGradientLp (affineSimplex T A b) c‖^2 ≤
      (D*R*‖A.symm.toContinuousLinearMap‖*‖simplexNodalLp (affineSimplex T A b) c‖)^2 := by
    calc
      _ ≤ affineJacobian A*((D*‖A.symm.toContinuousLinearMap‖)^2*
          ‖simplexNodalGradientLp T c‖^2) := affineSimplex_gradient_bound_sq T D hD.le hdb A b c
      _ ≤ affineJacobian A*((D*‖A.symm.toContinuousLinearMap‖)^2*
          (R*‖simplexNodalLp T c‖)^2) := by
        gcongr
      _ = (D*R*‖A.symm.toContinuousLinearMap‖)^2*(affineJacobian A*‖simplexNodalLp T c‖^2) := by ring
      _ = (D*R*‖A.symm.toContinuousLinearMap‖)^2*‖simplexNodalLp (affineSimplex T A b) c‖^2 := by
        rw [affineSimplex_nodal_norm_sq]
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

theorem affineSimplex_inverse_uniform (κ : ℝ) (hκ : 0 < κ) : ∃ C > (0:ℝ),
    ∀ (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d) (b : SpatialCoordinates d)
      (h : ℝ), 0 < h → ‖A.symm.toContinuousLinearMap‖ ≤ κ/h →
    ∀ c : Fin (d+1) → ℝ,
    ‖simplexNodalGradientLp (affineSimplex T A b) c‖ ≤
      (C/h)*‖simplexNodalLp (affineSimplex T A b) c‖ := by
  obtain ⟨R,hR,hbound⟩ := affineSimplex_inverse T
  refine ⟨R*κ,mul_pos hR hκ,?_⟩
  intro A b h _ hshape c
  calc
    _ ≤ R*‖A.symm.toContinuousLinearMap‖*‖simplexNodalLp (affineSimplex T A b) c‖ := hbound A b c
    _ ≤ R*(κ/h)*‖simplexNodalLp (affineSimplex T A b) c‖ := by gcongr
    _ = _ := by ring

end Carleman
