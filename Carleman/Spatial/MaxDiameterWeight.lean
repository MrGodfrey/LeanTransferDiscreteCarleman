module

public import Carleman.Spatial.CellwiseScaledWeight
public import Carleman.Spatial.SimplicialDiameter

/-! The actual upper mesh-size comparison converts local mesh powers to
powers of the maximum diameter, uniformly in the number of cells. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cellWeight_mesh_power_le (hS : IsOpen S) (hc : Convex ℝ S)
    (ℓ : ι → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i) {B : ℝ} (hB : 0 ≤ B)
    (hscale : ∀ i, ℓ i ≤ B*M.cellDiameter i)
    (w : BoundedMultiplier (volume.restrict S)) (u : Lp E 2 (volume.restrict S)) (p : ℕ) :
    (M.cellWeight (fun i => (ℓ i)^p) w).seminorm u ≤ (B*M.maxDiameter)^p*w.seminorm u := by
  apply M.cellWeight_seminorm_le hS hc _ w (by positivity [M.maxDiameter_nonneg])
  intro i
  rw [abs_of_nonneg (pow_nonneg (hℓ i) p)]
  exact pow_le_pow_left₀ (hℓ i) ((hscale i).trans
    (mul_le_mul_of_nonneg_left (M.cellDiameter_le_max i) hB)) p

end Carleman.SimplicialPartition
