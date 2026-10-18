module

public import Carleman.Spatial.SimplexNodalInterpolation
public import Mathlib.Topology.LocallyFinite

/-! Pointwise gluing of genuine local nodal interpolants on face-matching
simplices. This constructs a continuous function on the closed domain;
Sobolev membership and zero trace are separate obligations. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*}
  {S : Set (SpatialCoordinates d)} (M : Carleman.SimplicialPartition S ι)

/-- The common part is contained in the convex hull of the common vertices.
The reverse containment follows from convexity of the two cells. -/
def FaceMatching : Prop :=
  ∀ i j, M.cell i ∩ M.cell j ⊆ convexHull ℝ
    (Set.range (M.simplex i).points ∩ Set.range (M.simplex j).points)

def localNodal (f : SpatialCoordinates d → ℝ) (i : ι) : SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  simplexNodalInterpolant (M.simplex i) (fun k => f ((M.simplex i).points k))

theorem localNodal_vertex (f : SpatialCoordinates d → ℝ) (i : ι) (k : Fin (d+1)) :
    M.localNodal f i ((M.simplex i).points k) = f ((M.simplex i).points k) :=
  simplexNodalInterpolant_vertex _ _ _

theorem localNodal_agree (hM : M.FaceMatching) (f : SpatialCoordinates d → ℝ)
    (i j : ι) {x : SpatialCoordinates d} (hi : x ∈ M.cell i) (hj : x ∈ M.cell j) :
    M.localNodal f i x = M.localNodal f j x := by
  have hagree : (Set.range (M.simplex i).points ∩ Set.range (M.simplex j).points).EqOn
      (M.localNodal f i) (M.localNodal f j) := by
    rintro y ⟨⟨k,hk⟩,⟨l,hl⟩⟩
    rw [← hk,M.localNodal_vertex,show (M.simplex i).points k = (M.simplex j).points l from hk.trans hl.symm,
      M.localNodal_vertex]
  exact AffineMap.eqOn_affineSpan hagree
    ((convexHull_subset_affineSpan _) (hM i j ⟨hi,hj⟩))

/-- Defined pointwise with a harmless zero value outside the closed cover.
Independence of the selected cell is proved next from face matching. -/
def nodalFunction (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ := by
  classical
  exact if hx : ∃ i, x ∈ M.cell i then M.localNodal f hx.choose x else 0

theorem nodalFunction_on_cell (hM : M.FaceMatching) (f : SpatialCoordinates d → ℝ)
    (i : ι) {x : SpatialCoordinates d} (hx : x ∈ M.cell i) :
    M.nodalFunction f x = M.localNodal f i x := by
  have he : ∃ j, x ∈ M.cell j := ⟨i,hx⟩
  rw [nodalFunction,dite_eq_left he]
  exact M.localNodal_agree hM f _ i he.choose_spec hx

theorem nodalFunction_vertex (hM : M.FaceMatching) (f : SpatialCoordinates d → ℝ)
    (i : ι) (k : Fin (d+1)) :
    M.nodalFunction f ((M.simplex i).points k) = f ((M.simplex i).points k) := by
  rw [M.nodalFunction_on_cell hM f i (subset_convexHull ℝ _ (Set.mem_range_self k)),
    M.localNodal_vertex]

variable [Fintype ι]

theorem nodalFunction_continuousOn (hM : M.FaceMatching) (f : SpatialCoordinates d → ℝ) :
    ContinuousOn (M.nodalFunction f) (closure S) := by
  rw [← M.cells_union]
  apply (locallyFinite_of_finite M.cell).continuousOn_iUnion
    (fun i => (simplicialCell_compact (M.simplex i).points).isClosed)
  intro i
  exact (M.localNodal f i).continuous_of_finiteDimensional.continuousOn.congr
    (fun _ hx => M.nodalFunction_on_cell hM f i hx)

theorem nodalFunction_reproduces (hM : M.FaceMatching) (p : SpatialCoordinates d →ᵃ[ℝ] ℝ)
    {x : SpatialCoordinates d} (hx : x ∈ closure S) : M.nodalFunction p x = p x := by
  rw [← M.cells_union] at hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  rw [M.nodalFunction_on_cell hM p i hi]
  change simplexNodalInterpolant (M.simplex i) (fun k => p ((M.simplex i).points k)) x = _
  rw [simplexNodalInterpolant_reproduces]

end Carleman.SimplicialPartition
