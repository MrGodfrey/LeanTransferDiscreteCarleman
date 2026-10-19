module

public import Carleman.Spatial.CellwiseInverseWeight

/-! Arbitrary actual cellwise scalar multipliers, including the mesh-size
and its square, with exact vector-valued L² energy decompositions. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def cellWeight (c : ι → ℝ) (w : BoundedMultiplier (volume.restrict S)) :
    BoundedMultiplier (volume.restrict S) := M.inverseWeight (fun i => (c i)⁻¹) w

theorem cellWeight_on_cell (hS : IsOpen S) (hc : Convex ℝ S) (c : ι → ℝ)
    (w : BoundedMultiplier (volume.restrict S)) (i : ι) :
    ∀ᵐ x ∂volume.restrict (M.cell i), (M.cellWeight c w).value x=c i*w.value x := by
  filter_upwards [(M.inverseWeight_on_cell hS.measurableSet (fun i => (c i)⁻¹) w i).filter_mono
    (ae_mono (M.cell_measure_le_domain hS hc i)),
    ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x hx hi
  simpa only [cellWeight,inv_inv] using hx hi

theorem cellWeight_sq_sum (hS : IsOpen S) (hc : Convex ℝ S) (c : ι → ℝ)
    (w : BoundedMultiplier (volume.restrict S)) (u : Lp E 2 (volume.restrict S)) :
    ((M.cellWeight c w).seminorm u)^2 =
      ∑ i, (c i)^2 * ∫ x in M.cell i, |w.value x|^2*‖u x‖^2 := by
  rw [BoundedMultiplier.seminorm_sq_integral,
    M.integral_eq_sum_cells hS hc _ ((M.cellWeight c w).integrable_density u)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [M.cellWeight_on_cell hS hc c w i] with x hx
  rw [hx,abs_mul,mul_pow,sq_abs]
  ring

theorem cellWeight_seminorm_le (hS : IsOpen S) (hc : Convex ℝ S) (c : ι → ℝ)
    (w : BoundedMultiplier (volume.restrict S)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, |c i| ≤ B) (u : Lp E 2 (volume.restrict S)) :
    (M.cellWeight c w).seminorm u ≤ B*w.seminorm u := by
  apply (sq_le_sq₀ (apply_nonneg _ _) (by positivity)).mp
  rw [M.cellWeight_sq_sum hS hc,mul_pow,w.seminorm_sq_integral,
    M.integral_eq_sum_cells hS hc _ (w.integrable_density u),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => by positivity)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (c i)) hB).mpr (hb i)

end Carleman.SimplicialPartition
