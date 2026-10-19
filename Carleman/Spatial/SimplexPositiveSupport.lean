module

public import Carleman.Spatial.SimplexNodalInterpolation

/-! Positive barycentric support and integral affine inequalities of width one.
These give a direct common-face criterion for actual lattice simplices. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman

theorem integer_weighted_le_of_pos {ι : Type*} [Fintype ι] (w : ι → ℝ) (g : ι → ℤ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1)
    (hwidth : ∀ i j, g i ≤ g j+1) (c : ℤ)
    (hm : ∑ i, w i*(g i:ℝ) ≤ (c:ℝ)) (k : ι) (hk : 0 < w k) : g k ≤ c := by
  classical
  by_contra hn
  have hg : c+1 ≤ g k := by omega
  have hall (i : ι) : c ≤ g i := by have hi := hwidth k i; omega
  have hnonneg (i : ι) : 0 ≤ w i*((g i:ℝ)-(c:ℝ)) :=
    mul_nonneg (hw i) (sub_nonneg.mpr (by exact_mod_cast hall i))
  have hp : 0 < w k*((g k:ℝ)-(c:ℝ)) := by
    apply mul_pos hk
    have hr : (c:ℝ)+1 ≤ (g k:ℝ) := by exact_mod_cast hg
    linarith
  have hle := Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ k)
  have he : (∑ i, w i*((g i:ℝ)-(c:ℝ)))=(∑ i, w i*(g i:ℝ))-(c:ℝ) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul]
  rw [he] at hle
  linarith

variable {d : ℕ}

theorem simplexBarycentric_reconstruct (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (x : SpatialCoordinates d) : ∑ i, simplexBarycentric T i x • T.points i=x := by
  have he := (simplexAffineBasis T).affineCombination_coord_eq_self x
  rw [Finset.univ.affineCombination_eq_linear_combination _ _
    ((simplexAffineBasis T).sum_coord_apply_eq_one x)] at he
  exact he

theorem simplex_mem_convexHull_positive_support (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points)
    (A : Set (SpatialCoordinates d))
    (hA : ∀ i, 0 < simplexBarycentric T i x → T.points i ∈ A) : x ∈ convexHull ℝ A := by
  classical
  let w := fun i => simplexBarycentric T i x
  let s := Finset.univ.filter (fun i => 0 < w i)
  have hz (i : Fin (d+1)) (hi : i ∉ s) : w i=0 := by
    have hn : ¬0 < w i := by simpa [s] using hi
    exact le_antisymm (le_of_not_gt hn) (simplexBarycentric_nonneg T hx i)
  have hs : ∑ i ∈ s, w i=1 := by
    rw [Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hz i hi)]
    exact simplexBarycentric_sum T x
  have he : ∑ i ∈ s, w i • T.points i=x := by
    rw [Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by rw [hz i hi,zero_smul])]
    exact simplexBarycentric_reconstruct T x
  rw [← he,← Finset.centerMass_eq_of_sum_1 _ _ hs]
  exact s.centerMass_mem_convexHull (fun i _ => simplexBarycentric_nonneg T hx i)
    (by rw [hs]; norm_num) (fun i hi => hA i (Finset.mem_filter.mp hi).2)

theorem simplex_integer_affine_le_of_pos (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) (g : Fin (d+1) → ℤ)
    (hg : ∀ i, p (T.points i)=(g i:ℝ)) (hwidth : ∀ i j, g i ≤ g j+1)
    (c : ℤ) {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points)
    (hp : p x ≤ (c:ℝ)) (k : Fin (d+1)) (hk : 0 < simplexBarycentric T k x) :
    g k ≤ c := by
  have he := congrArg (fun f : SpatialCoordinates d →ᵃ[ℝ] ℝ => f x)
    (simplexNodalInterpolant_reproduces T p)
  rw [simplexNodalInterpolant_apply] at he
  simp_rw [hg] at he
  apply integer_weighted_le_of_pos (fun i => simplexBarycentric T i x) g
    (simplexBarycentric_nonneg T hx) (simplexBarycentric_sum T x) hwidth c ?_ k hk
  simpa only [mul_comm,he] using hp

end Carleman
