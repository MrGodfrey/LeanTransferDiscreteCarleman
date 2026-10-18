module

public import Carleman.Spatial.PiecewiseAffinePartition
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Actual convex hull cells from finite vertex arrays. Affine independence
and mesh quality are separate geometric properties; none are inferred here. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def simplicialCell (v : Fin (d+1) → SpatialCoordinates d) : Set (SpatialCoordinates d) :=
  convexHull ℝ (Set.range v)

theorem simplicialCell_convex (v : Fin (d+1) → SpatialCoordinates d) :
    Convex ℝ (simplicialCell v) := convex_convexHull ℝ _

theorem simplicialCell_compact (v : Fin (d+1) → SpatialCoordinates d) :
    IsCompact (simplicialCell v) := (Set.finite_range v).isCompact_convexHull ℝ

theorem simplicialCell_measurable (v : Fin (d+1) → SpatialCoordinates d) :
    MeasurableSet (simplicialCell v) := (simplicialCell_compact v).isClosed.measurableSet

theorem simplicialCell_frontier_null (v : Fin (d+1) → SpatialCoordinates d) :
    volume (frontier (simplicialCell v)) = 0 := (simplicialCell_convex v).addHaar_frontier volume


/-- A genuine d-simplex in Euclidean d-space has nonempty interior. -/
theorem simplicialCell_interior_nonempty (T : Affine.Simplex ℝ (SpatialCoordinates d) d) :
    (interior (simplicialCell T.points)).Nonempty := by
  apply (simplicialCell_convex T.points).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [simplicialCell,affineSpan_convexHull]
  exact T.affineSpan_eq_top (by simp [SpatialCoordinates])

variable {ι : Type*} [Fintype ι] (v : ι → Fin (d+1) → SpatialCoordinates d)

def simplicialRadius : ℝ := ∑ i, ∑ k, ‖v i k‖

theorem simplicialRadius_nonneg : 0 ≤ simplicialRadius v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem simplicialCell_norm_le (i : ι) {x : SpatialCoordinates d}
    (hx : x ∈ simplicialCell (v i)) : ‖x‖ ≤ simplicialRadius v := by
  have hvertex : Set.range (v i) ⊆ Metric.closedBall 0 (simplicialRadius v) := by
    rintro _ ⟨k,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (Finset.single_le_sum (fun j _ => norm_nonneg (v i j)) (Finset.mem_univ k)).trans
      (Finset.single_le_sum
        (fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg (v j k)) (Finset.mem_univ i))
  have hh := convexHull_min hvertex (convex_closedBall (0 : SpatialCoordinates d) (simplicialRadius v)) hx
  simpa only [Metric.mem_closedBall,dist_zero_right] using hh

/-- Pairwise interior disjointness and coverage give an actual a.e. partition;
finite closed-cell boundary overlaps are removed by their proven null measure. -/
theorem simplicialCells_ae_partition (S : Set (SpatialCoordinates d))
    (hcover : S ⊆ ⋃ i, simplicialCell (v i))
    (hdisjoint : Pairwise fun i j => Disjoint (interior (simplicialCell (v i)))
      (interior (simplicialCell (v j)))) (hS : MeasurableSet S) :
    ∀ᵐ x ∂(volume.restrict S), ∃ i, x ∈ simplicialCell (v i) ∧
      ∀ j, x ∈ simplicialCell (v j) → j=i := by
  have hn (i : ι) : ∀ᵐ x ∂(volume.restrict S), x ∉ frontier (simplicialCell (v i)) := by
    apply ae_restrict_of_ae
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using simplicialCell_frontier_null (v i)
  have hall : ∀ᵐ x ∂(volume.restrict S), ∀ i, x ∉ frontier (simplicialCell (v i)) :=
    ae_all_iff.mpr hn
  filter_upwards [ae_restrict_mem hS,hall] with x hx hfront
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover hx)
  refine ⟨i,hi,?_⟩
  intro j hj
  by_contra hji
  have hxi := (mem_interior_iff_notMem_frontier hi).mpr (hfront i)
  have hxj := (mem_interior_iff_notMem_frontier hj).mpr (hfront j)
  exact Set.disjoint_left.mp (hdisjoint hji) hxj hxi

end Carleman
