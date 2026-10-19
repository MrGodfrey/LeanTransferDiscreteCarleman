module

public import Carleman.Spatial.CellwiseScaledWeight

/-! Exact summation of weighted local L² errors on the actual finite mesh.
The same argument handles the inverse-size value error without overlap loss. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem weighted_cell_errors_sum (hS : IsOpen S) (hc : Convex ℝ S)
    (w : BoundedMultiplier (volume.restrict S)) (u : Lp E 2 (volume.restrict S))
    (v : Lp F 2 (volume.restrict S)) (c : ι → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hcell : ∀ i, (∫ x in M.cell i, |w.value x|^2*‖u x‖^2) ≤
      A*(c i)^2*(∫ x in M.cell i, |w.value x|^2*‖v x‖^2)) :
    w.seminorm u ≤ Real.sqrt A*(M.cellWeight c w).seminorm v := by
  apply (sq_le_sq₀ (apply_nonneg _ _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt hA,M.cellWeight_sq_sum hS hc,w.seminorm_sq_integral,
    M.integral_eq_sum_cells hS hc _ (w.integrable_density u),Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by simpa only [mul_assoc] using hcell i

theorem weighted_cell_inverse_errors_sum (hS : IsOpen S) (hc : Convex ℝ S)
    (w : BoundedMultiplier (volume.restrict S)) (u : Lp ℝ 2 (volume.restrict S))
    (v : Lp F 2 (volume.restrict S)) (ℓ : ι → ℝ)
    {A : ℝ} (hA : 0 ≤ A)
    (hcell : ∀ i, (∫ x in M.cell i, |w.value x|^2*‖u x‖^2) ≤
      A*(ℓ i)^4*(∫ x in M.cell i, |w.value x|^2*‖v x‖^2)) :
    (M.inverseWeight ℓ w).seminorm u ≤ Real.sqrt A*(M.cellWeight ℓ w).seminorm v := by
  apply (sq_le_sq₀ (apply_nonneg _ _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt hA,M.cellWeight_sq_sum hS hc,M.inverseWeight_sq_sum hS hc,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ((ℓ i)⁻¹)^2*(A*(ℓ i)^4*(∫ x in M.cell i, |w.value x|^2*‖v x‖^2)) :=
      mul_le_mul_of_nonneg_left (hcell i) (sq_nonneg _)
    _ = _ := by field_simp

end Carleman.SimplicialPartition
