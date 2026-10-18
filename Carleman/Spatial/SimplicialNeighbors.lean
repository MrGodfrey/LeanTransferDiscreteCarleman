module

public import Carleman.Spatial.SimplicialDiameter

/-! Actual shared-vertex neighbors and their spatial diameter bound. -/
@[expose] public noncomputable section
open Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def VertexNeighbors (i j : ι) : Prop :=
  ∃ k l : Fin (d+1), (M.simplex i).points k = (M.simplex j).points l

theorem VertexNeighbors.symm {i j : ι} (h : M.VertexNeighbors i j) : M.VertexNeighbors j i := by
  obtain ⟨k,l,hkl⟩ := h
  exact ⟨l,k,hkl.symm⟩

theorem vertexNeighbors_dist_le {i j : ι} (h : M.VertexNeighbors i j)
    {x y : SpatialCoordinates d} (hx : x ∈ M.cell i) (hy : y ∈ M.cell j) :
    dist x y ≤ M.cellDiameter i+M.cellDiameter j := by
  obtain ⟨k,l,hkl⟩ := h
  have hi : (M.simplex i).points k ∈ M.cell i := subset_convexHull ℝ _ (Set.mem_range_self k)
  have hj : (M.simplex i).points k ∈ M.cell j := by
    rw [hkl]
    exact subset_convexHull ℝ _ (Set.mem_range_self l)
  exact (dist_triangle x ((M.simplex i).points k) y).trans
    (add_le_add (M.dist_le_cellDiameter i hx hi) (M.dist_le_cellDiameter j hj hy))

variable [Fintype ι]

theorem vertexNeighbors_dist_le_max {i j : ι} (h : M.VertexNeighbors i j)
    {x y : SpatialCoordinates d} (hx : x ∈ M.cell i) (hy : y ∈ M.cell j) :
    dist x y ≤ 2*M.maxDiameter := by
  have hh := M.vertexNeighbors_dist_le h hx hy
  linarith [M.cellDiameter_le_max i,M.cellDiameter_le_max j]

end Carleman.SimplicialPartition
