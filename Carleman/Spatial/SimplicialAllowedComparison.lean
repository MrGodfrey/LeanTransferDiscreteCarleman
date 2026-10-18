module

public import Carleman.Spatial.SimplicialDiameter
public import Carleman.Weights.SpatialComparison

/-! Uniform comparison with the actual allowed weight at any point of a cell. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

theorem maxDiameter_mul_q_le (w : TimeWeight) {δ : ℝ} (hm : M.maxDiameter*w.max ≤ δ) (t : ℝ) :
    M.maxDiameter*w.q t ≤ δ :=
  (mul_le_mul_of_nonneg_left (w.upper t) M.maxDiameter_nonneg).trans hm

theorem allowedWeight_cell_comparison (ρ : SpatialProfile (volume.restrict S)) {L : ℝ}
    (hL : 0 ≤ L)
    (hρ : ∀ x ∈ closure S, ∀ y ∈ closure S, |ρ.value x-ρ.value y| ≤ L*dist x y)
    (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1) (hm : M.maxDiameter*w.q t ≤ 1)
    (i : ι) {x y : SpatialCoordinates d} (hx : x ∈ M.cell i) (hy : y ∈ M.cell i) :
    |((ρ.scaled η).multiplier w τ t).value x| ≤
        Real.exp L*((ρ.scaled η).multiplier w τ t).value y ∧
      ((ρ.scaled η).multiplier w τ t).value y ≤
        Real.exp L*|((ρ.scaled η).multiplier w τ t).value x| := by
  have hb : |ρ.value x-ρ.value y| ≤ L*M.cellDiameter i :=
    (hρ x (M.inside i hx) y (M.inside i hy)).trans
      (mul_le_mul_of_nonneg_left (M.dist_le_cellDiameter i hx hy) hL)
  have he : Real.exp ((L*M.cellDiameter i)*w.q t) ≤ Real.exp L := by
    apply Real.exp_le_exp.mpr
    have hm' := (mul_le_mul_of_nonneg_right (M.cellDiameter_le_max i) (w.nonneg t)).trans hm
    nlinarith [mul_le_mul_of_nonneg_left hm' hL]
  rw [abs_of_pos (ρ.scaled_multiplier_pos η w τ t x)]
  constructor
  · exact (ρ.scaled_multiplier_spatial_le η hη w τ t hb).trans
      (mul_le_mul_of_nonneg_right he (ρ.scaled_multiplier_pos η w τ t y).le)
  · have hb' : |ρ.value y-ρ.value x| ≤ L*M.cellDiameter i := by
      simpa only [abs_sub_comm] using hb
    exact (ρ.scaled_multiplier_spatial_le η hη w τ t hb').trans
      (mul_le_mul_of_nonneg_right he (ρ.scaled_multiplier_pos η w τ t x).le)

end Carleman.SimplicialPartition
