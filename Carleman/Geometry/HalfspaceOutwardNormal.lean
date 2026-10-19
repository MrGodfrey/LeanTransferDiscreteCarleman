module

public import Carleman.Geometry.FiniteHalfspaceFaces
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! The unit outward normal is constructed from the real defining functional. -/
@[expose] public noncomputable section
namespace Carleman
variable {d : ℕ}

def halfspaceOutwardNormal (L : SpatialCoordinates d →L[ℝ] ℝ) : SpatialCoordinates d :=
  (-‖L‖⁻¹) • (InnerProductSpace.toDual ℝ (SpatialCoordinates d)).symm L

theorem halfspaceOutwardNormal_norm {L : SpatialCoordinates d →L[ℝ] ℝ} (hL : L ≠ 0) :
    ‖halfspaceOutwardNormal L‖=1 := by
  have hp : 0 < ‖L‖ := norm_pos_iff.mpr hL
  rw [halfspaceOutwardNormal,norm_smul,Real.norm_eq_abs,abs_neg,
    abs_of_pos (inv_pos.mpr hp),(InnerProductSpace.toDual ℝ (SpatialCoordinates d)).symm.norm_map,
    inv_mul_cancel₀ hp.ne']

theorem halfspaceOutwardNormal_eval {L : SpatialCoordinates d →L[ℝ] ℝ}
    (hL : L ≠ 0) (v : SpatialCoordinates d) :
    L v = -‖L‖*inner ℝ v (halfspaceOutwardNormal L) := by
  have hp : ‖L‖ ≠ 0 := norm_ne_zero_iff.mpr hL
  have hdual : inner ℝ v ((InnerProductSpace.toDual ℝ (SpatialCoordinates d)).symm L) = L v := by
    calc
      _ = inner ℝ ((InnerProductSpace.toDual ℝ (SpatialCoordinates d)).symm L) v :=
        real_inner_comm _ _
      _ = L v := InnerProductSpace.toDual_symm_apply
  rw [halfspaceOutwardNormal,inner_smul_right,hdual]
  field_simp

theorem halfspaceOutwardNormal_plane {L : SpatialCoordinates d →L[ℝ] ℝ}
    (hL : L ≠ 0) (v : SpatialCoordinates d) :
    inner ℝ v (halfspaceOutwardNormal L)=0 ↔ L v=0 := by
  rw [halfspaceOutwardNormal_eval hL v]
  constructor
  · intro h
    rw [h,mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (norm_ne_zero_iff.mpr hL))

theorem halfspaceOutwardNormal_support {L : SpatialCoordinates d →L[ℝ] ℝ}
    (hL : L ≠ 0) {b : ℝ} (x : SpatialCoordinates d) (hx : L x=b)
    (y : SpatialCoordinates d) (hy : b < L y) :
    inner ℝ (y-x) (halfspaceOutwardNormal L) ≤ 0 := by
  have hp : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h := halfspaceOutwardNormal_eval hL (y-x)
  rw [map_sub,hx] at h
  nlinarith

end Carleman
