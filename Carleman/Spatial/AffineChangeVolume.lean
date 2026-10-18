module

public import Carleman.Spatial.SimplexReferenceInverse
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Actual invertible affine changes of Euclidean coordinates, including
the Jacobian in restricted volume and scalar integrals. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d) (b : SpatialCoordinates d)

def affineChange : SpatialCoordinates d ≃ₜ SpatialCoordinates d :=
  A.toHomeomorph.trans (Homeomorph.addRight b)

theorem affineChange_apply (x : SpatialCoordinates d) : affineChange A b x = A x+b := rfl

def affineJacobian : ℝ := |LinearMap.det A.toLinearMap|

theorem affineJacobian_pos : 0 < affineJacobian A :=
  abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero

theorem affineChange_map_volume :
    Measure.map (affineChange A b) volume = ENNReal.ofReal (affineJacobian A)⁻¹ • volume := by
  change Measure.map ((fun y => y+b) ∘ A) volume = _
  rw [← Measure.map_map (by fun_prop) A.continuous.measurable]
  change Measure.map (fun y => y+b) (Measure.map A.toLinearMap volume) = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (SpatialCoordinates d))
    (f := A.toLinearMap) A.toLinearEquiv.isUnit_det'.ne_zero]
  rw [Measure.map_smul _ (by fun_prop),map_add_right_eq_self]
  simp only [affineJacobian,abs_inv]

theorem affineChange_map_restrict (S : Set (SpatialCoordinates d)) :
    Measure.map (affineChange A b) (volume.restrict S) =
      ENNReal.ofReal (affineJacobian A)⁻¹ • volume.restrict (affineChange A b '' S) := by
  have he : MeasurableEmbedding (affineChange A b) :=
    (affineChange A b).toMeasurableEquiv.measurableEmbedding
  have hh := he.restrict_map volume (affineChange A b '' S)
  rw [Set.preimage_image_eq _ (affineChange A b).injective] at hh
  rw [← hh,affineChange_map_volume,Measure.restrict_smul]

theorem integral_comp_affineChange (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    (∫ x in S, f (affineChange A b x)) =
      (affineJacobian A)⁻¹ * ∫ y in affineChange A b '' S, f y := by
  have he : MeasurableEmbedding (affineChange A b) :=
    (affineChange A b).toMeasurableEquiv.measurableEmbedding
  rw [← he.integral_map,
    affineChange_map_restrict,integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr (affineJacobian_pos A).le),smul_eq_mul]

end Carleman
