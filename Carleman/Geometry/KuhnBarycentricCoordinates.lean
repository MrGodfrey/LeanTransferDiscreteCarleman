module

public import Carleman.Geometry.CartesianKuhnSimplex
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Convex.Combination

/-! Explicit barycentric coordinates of the actual prefix Kuhn simplex.
They are adjacent differences of (1,x₀,...,x_{d-1},0). -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def kuhnExtendedCoordinate (x : SpatialCoordinates d) : Fin (d+2) → ℝ :=
  Fin.cons 1 (Fin.snoc (fun j => x j) 0)

theorem kuhnExtendedCoordinate_zero (x : SpatialCoordinates d) : kuhnExtendedCoordinate x 0=1 := rfl

theorem kuhnExtendedCoordinate_last (x : SpatialCoordinates d) :
    kuhnExtendedCoordinate x (Fin.last (d+1))=0 := by
  simp [kuhnExtendedCoordinate]

theorem kuhnExtendedCoordinate_inner (x : SpatialCoordinates d) (j : Fin d) :
    kuhnExtendedCoordinate x j.succ.castSucc=x j := by
  rw [kuhnExtendedCoordinate,Fin.castSucc_succ,Fin.cons_succ,Fin.snoc_castSucc]

def kuhnBarycentricWeight (x : SpatialCoordinates d) (k : Fin (d+1)) : ℝ :=
  kuhnExtendedCoordinate x k.castSucc-kuhnExtendedCoordinate x k.succ

theorem kuhnBarycentricWeight_sum (x : SpatialCoordinates d) :
    ∑ k, kuhnBarycentricWeight x k=1 := by
  have h₁ := Fin.sum_univ_castSucc (kuhnExtendedCoordinate x)
  have h₂ := Fin.sum_univ_succ (kuhnExtendedCoordinate x)
  rw [kuhnExtendedCoordinate_last] at h₁
  rw [kuhnExtendedCoordinate_zero] at h₂
  simp only [kuhnBarycentricWeight,Finset.sum_sub_distrib]
  linarith

theorem kuhnBarycentricWeight_reconstruct (x : SpatialCoordinates d) :
    ∑ k, kuhnBarycentricWeight x k • (kuhnReferenceSimplex d).points k = x := by
  apply PiLp.ext
  intro j
  change (EuclideanSpace.proj j) (∑ k, kuhnBarycentricWeight x k •
    (kuhnReferenceSimplex d).points k)=x j
  rw [map_sum]
  change (∑ k, kuhnBarycentricWeight x k*(kuhnReferenceSimplex d).points k j)=x j
  simp_rw [kuhnReferenceSimplex_points,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun k : Fin (d+1) => j.val < k.val)=Finset.Icc j.succ (Fin.last d) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Icc,Fin.le_def,
      Fin.val_succ,Fin.val_last]
    omega
  rw [he]
  have hn (k : Fin (d+1)) : kuhnBarycentricWeight x k=
      -(kuhnExtendedCoordinate x k.succ-kuhnExtendedCoordinate x k.castSucc) := by
    unfold kuhnBarycentricWeight
    ring
  simp_rw [hn]
  rw [Finset.sum_neg_distrib,Fin.sum_Icc_sub (Fin.le_last _) (kuhnExtendedCoordinate x)]
  simp [kuhnExtendedCoordinate,Fin.castSucc_succ]

theorem kuhnBarycentricWeight_nonneg (x : SpatialCoordinates d)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hmono : Antitone (fun j => x j)) :
    ∀ k, 0 ≤ kuhnBarycentricWeight x k := by
  cases d with
  | zero =>
    intro k
    have hk : k=0 := Fin.ext (by omega)
    subst k
    change 0 ≤ kuhnExtendedCoordinate x 0-kuhnExtendedCoordinate x (Fin.last 1)
    rw [kuhnExtendedCoordinate_zero,kuhnExtendedCoordinate_last]
    norm_num
  | succ n =>
    intro k
    induction k using Fin.cases with
    | zero =>
      change 0 ≤ kuhnExtendedCoordinate x 0-kuhnExtendedCoordinate x (0:Fin (n+1)).succ.castSucc
      rw [kuhnExtendedCoordinate_zero,kuhnExtendedCoordinate_inner]
      exact sub_nonneg.mpr (hx 0).2
    | succ k =>
      induction k using Fin.lastCases with
      | last =>
        change 0 ≤ kuhnExtendedCoordinate x (Fin.last n).succ.castSucc-
          kuhnExtendedCoordinate x (Fin.last (n+2))
        rw [kuhnExtendedCoordinate_inner,kuhnExtendedCoordinate_last,sub_zero]
        exact (hx (Fin.last n)).1
      | cast j =>
        change 0 ≤ kuhnExtendedCoordinate x j.castSucc.succ.castSucc-
          kuhnExtendedCoordinate x j.succ.succ.castSucc
        rw [kuhnExtendedCoordinate_inner,kuhnExtendedCoordinate_inner]
        exact sub_nonneg.mpr (hmono (Fin.castSucc_le_succ j))

theorem kuhnReferenceSimplex_mem_of_ordered (x : SpatialCoordinates d)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hmono : Antitone (fun j => x j)) :
    x ∈ simplicialCell (kuhnReferenceSimplex d).points :=
  mem_convexHull_of_exists_fintype (kuhnBarycentricWeight x) (kuhnReferenceSimplex d).points
    (kuhnBarycentricWeight_nonneg x hx hmono) (kuhnBarycentricWeight_sum x)
    (fun k => mem_range_self k) (kuhnBarycentricWeight_reconstruct x)

end Carleman
