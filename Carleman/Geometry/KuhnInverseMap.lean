module

public import Carleman.Geometry.CartesianKuhnSimplex

/-! The actual affine map defining a Kuhn cell has the uniform inverse
operator norm bound dictated by the physical coordinate steps. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem coordinatePermutation_symm_norm (π : Equiv.Perm (Fin d)) (x : SpatialCoordinates d) :
    ‖(coordinatePermutation π).symm x‖=‖x‖ := by
  have he : ‖(coordinatePermutation π).symm x‖^2=‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    change (∑ j, (x (π j))^2)=∑ j, (x j)^2
    exact Equiv.sum_comp π (fun j => (x j)^2)
  nlinarith [norm_nonneg ((coordinatePermutation π).symm x),norm_nonneg x]

theorem cartesianKuhn_inverse_map_bound (δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (π : Equiv.Perm (Fin d)) (κ h : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (hlower : ∀ j, h/κ ≤ δ j) :
    ‖(((coordinatePermutation π).trans (coordinateDilation δ hδ)).symm).toContinuousLinearMap‖ ≤ κ/h := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hκ.le hh.le)
  intro x
  change ‖(coordinatePermutation π).symm ((coordinateDilation δ hδ).symm x)‖ ≤ κ/h*‖x‖
  rw [coordinatePermutation_symm_norm]
  simpa only [inv_div] using coordinateDilation_symm_norm_le δ hδ (h/κ) (div_pos hh hκ) hlower x

end Carleman
