module

public import Carleman.Spatial.SimplicialNeighbors
public import Mathlib.Data.Finset.Lattice.Fold

/-! A single positive weight at each geometric vertex, from neighboring cell weights. -/
@[expose] public noncomputable section
open Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def incidentCells (x : SpatialCoordinates d) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => ∃ k, (M.simplex i).points k=x)

theorem mem_incidentCells (x : SpatialCoordinates d) (i : ι) :
    i ∈ M.incidentCells x ↔ ∃ k, (M.simplex i).points k=x := by
  classical
  simp [incidentCells]

def nodalWeightMinimum (a : ι → ℝ) (x : SpatialCoordinates d) : ℝ := by
  classical
  exact if h : (M.incidentCells x).Nonempty then (M.incidentCells x).inf' h a else 1

theorem nodalWeightMinimum_pos (a : ι → ℝ) (ha : ∀ i, 0 < a i) (x : SpatialCoordinates d) :
    0 < M.nodalWeightMinimum a x := by
  classical
  unfold nodalWeightMinimum
  split
  · rw [Finset.lt_inf'_iff]
    exact fun i _ => ha i
  · exact zero_lt_one

theorem nodalWeightMinimum_vertex_bounds (a : ι → ℝ) {θ : ℝ} (hθ : 0 < θ)
    (hg : ∀ i j, M.VertexNeighbors i j → a i ≤ θ*a j) (i : ι) (k : Fin (d+1)) :
    a i/θ ≤ M.nodalWeightMinimum a ((M.simplex i).points k) ∧
      M.nodalWeightMinimum a ((M.simplex i).points k) ≤ a i := by
  classical
  have hi : i ∈ M.incidentCells ((M.simplex i).points k) := (M.mem_incidentCells _ _).mpr ⟨k,rfl⟩
  have hn : (M.incidentCells ((M.simplex i).points k)).Nonempty := ⟨i,hi⟩
  rw [nodalWeightMinimum,dite_eq_left hn]
  constructor
  · apply Finset.le_inf'
    intro j hj
    obtain ⟨l,hl⟩ := (M.mem_incidentCells _ _).mp hj
    exact (div_le_iff₀ hθ).mpr (by simpa only [mul_comm θ] using hg i j ⟨k,l,hl.symm⟩)
  · exact Finset.inf'_le _ hi

theorem nodalWeightMinimum_local_ratio (a : ι → ℝ) {θ : ℝ} (hθ : 0 < θ)
    (hg : ∀ i j, M.VertexNeighbors i j → a i ≤ θ*a j) (i : ι) (k l : Fin (d+1)) :
    M.nodalWeightMinimum a ((M.simplex i).points k) ≤
      θ*M.nodalWeightMinimum a ((M.simplex i).points l) := by
  have hk := (M.nodalWeightMinimum_vertex_bounds a hθ hg i k).2
  have hl := (M.nodalWeightMinimum_vertex_bounds a hθ hg i l).1
  exact hk.trans (by simpa only [mul_comm θ] using (div_le_iff₀ hθ).mp hl)

end Carleman.SimplicialPartition
