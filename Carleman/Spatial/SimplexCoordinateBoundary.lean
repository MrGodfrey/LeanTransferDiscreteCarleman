module

public import Carleman.Spatial.SimplexPositiveSupport
public import Carleman.Geometry.ClosedCoordinateFaces

/-! Positive barycentric vertices of a boundary point stay on its supporting
coordinate face. This proves actual boundary fitting without trace hypotheses. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem simplex_affine_min_eq_of_pos (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) (c : ℝ) (hv : ∀ i, c ≤ p (T.points i))
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points) (he : p x=c)
    (k : Fin (d+1)) (hk : 0 < simplexBarycentric T k x) : p (T.points k)=c := by
  have hm := congrArg (fun f : SpatialCoordinates d →ᵃ[ℝ] ℝ => f x)
    (simplexNodalInterpolant_reproduces T p)
  rw [simplexNodalInterpolant_apply,he] at hm
  have hs : (∑ i, (p (T.points i)-c)*simplexBarycentric T i x)=0 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,simplexBarycentric_sum,mul_one,hm,sub_self]
  have hn (i : Fin (d+1)) : 0 ≤ (p (T.points i)-c)*simplexBarycentric T i x :=
    mul_nonneg (sub_nonneg.mpr (hv i)) (simplexBarycentric_nonneg T hx i)
  have hl := Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ k)
  rw [hs] at hl
  nlinarith [hv k]

theorem simplex_coordinateBox_boundary_support (a b : Fin d → ℝ)
    (hab : ∀ j, a j < b j) (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (hT : simplicialCell T.points ⊆ closure (openCoordinateBox a b))
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points)
    (hfront : x ∈ frontier (openCoordinateBox a b)) (k : Fin (d+1))
    (hk : 0 < simplexBarycentric T k x) : T.points k ∈ frontier (openCoordinateBox a b) := by
  have hbox : simplicialCell T.points ⊆ closedCoordinateBox a b := by
    simpa only [closure_openCoordinateBox a b hab] using hT
  have hv (l : Fin (d+1)) : T.points l ∈ closedCoordinateBox a b :=
    hbox (subset_convexHull ℝ _ (mem_range_self l))
  have hn : x ∉ openCoordinateBox a b := by
    simpa only [(openCoordinateBox_isOpen a b).interior_eq] using hfront.2
  have hedge : ∃ j, x j=a j ∨ x j=b j := by
    by_contra he
    apply hn
    intro j
    have hj : x j ≠ a j ∧ x j ≠ b j := by simpa using (not_exists.mp he) j
    exact ⟨lt_of_le_of_ne ((hbox hx j).1) hj.1.symm,
      lt_of_le_of_ne ((hbox hx j).2) hj.2⟩
  obtain ⟨j,hj⟩ := hedge
  let p : SpatialCoordinates d →ᵃ[ℝ] ℝ := (EuclideanSpace.proj j).toLinearMap.toAffineMap
  have hvj : T.points k j=a j ∨ T.points k j=b j := by
    rcases hj with hlo | hup
    · exact Or.inl (simplex_affine_min_eq_of_pos T p
        (a j) (fun l => (hv l j).1) hx hlo k hk)
    · have he := simplex_affine_min_eq_of_pos T
        (-p) (-b j)
        (fun l => neg_le_neg (hv l j).2) hx (congrArg Neg.neg hup) k hk
      exact Or.inr (neg_injective he)
  refine ⟨hT (subset_convexHull ℝ _ (mem_range_self k)),?_⟩
  rw [(openCoordinateBox_isOpen a b).interior_eq]
  intro hin
  rcases hvj with hlo | hup
  · have hh := (hin j).1
    rw [hlo] at hh
    exact (lt_irrefl _ hh)
  · have hh := (hin j).2
    rw [hup] at hh
    exact (lt_irrefl _ hh)

end Carleman
