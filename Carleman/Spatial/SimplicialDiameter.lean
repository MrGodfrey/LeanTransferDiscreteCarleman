module

public import Carleman.Spatial.SimplicialPartition

/-! Actual cell diameters and their finite maximum, including the empty mesh. -/
@[expose] public noncomputable section
open Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def cellDiameter (i : ι) : ℝ := Metric.diam (M.cell i)

theorem cellDiameter_nonneg (i : ι) : 0 ≤ M.cellDiameter i := Metric.diam_nonneg

theorem dist_le_cellDiameter (i : ι) {x y : SpatialCoordinates d}
    (hx : x ∈ M.cell i) (hy : y ∈ M.cell i) : dist x y ≤ M.cellDiameter i :=
  Metric.dist_le_diam_of_mem (simplicialCell_compact _).isBounded hx hy

variable [Fintype ι]

def maxDiameter : ℝ := (Finset.univ.sup (fun i => (⟨M.cellDiameter i,M.cellDiameter_nonneg i⟩ : NNReal)) : NNReal)

theorem maxDiameter_nonneg : 0 ≤ M.maxDiameter := NNReal.coe_nonneg _

theorem cellDiameter_le_max (i : ι) : M.cellDiameter i ≤ M.maxDiameter := by
  exact_mod_cast (Finset.le_sup (f := fun j => (⟨M.cellDiameter j,M.cellDiameter_nonneg j⟩ : NNReal))
    (Finset.mem_univ i))

omit [Fintype ι] in
theorem cellScale_le_inball {κ B : ℝ} (hB : 0 ≤ B) (r ℓ : ι → ℝ)
    (hshape : ∀ i, M.cellDiameter i ≤ κ*r i) (hscale : ∀ i, ℓ i ≤ B*M.cellDiameter i) :
    ∀ i, ℓ i ≤ (B*κ)*r i := by
  intro i
  calc
    ℓ i ≤ B*M.cellDiameter i := hscale i
    _ ≤ B*(κ*r i) := mul_le_mul_of_nonneg_left (hshape i) hB
    _ = _ := by ring

end Carleman.SimplicialPartition
