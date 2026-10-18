module

public import Carleman.Spatial.SimplicialPartition
public import Mathlib.Analysis.Convex.Combination

/-! Actual barycentric nodal interpolation on a genuine Euclidean simplex.
Only pointwise functions are interpolated here; no L² class is evaluated at
vertices and no Sobolev embedding is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

def simplexAffineBasis : AffineBasis (Fin (d+1)) ℝ (SpatialCoordinates d) :=
  ⟨T.points,T.independent,T.affineSpan_eq_top (by simp [SpatialCoordinates])⟩

theorem simplexAffineBasis_apply (i : Fin (d+1)) : simplexAffineBasis T i = T.points i := rfl

def simplexBarycentric (i : Fin (d+1)) : SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  (simplexAffineBasis T).coord i

theorem simplexBarycentric_vertex (i j : Fin (d+1)) :
    simplexBarycentric T i (T.points j) = if i=j then 1 else 0 :=
  (simplexAffineBasis T).coord_apply i j

theorem simplexBarycentric_sum (x : SpatialCoordinates d) :
    ∑ i, simplexBarycentric T i x = 1 := (simplexAffineBasis T).sum_coord_apply_eq_one x

theorem simplexBarycentric_nonneg {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points)
    (i : Fin (d+1)) : 0 ≤ simplexBarycentric T i x := by
  have he := (simplexAffineBasis T).convexHull_eq_nonneg_coord
  change simplicialCell T.points = _ at he
  rw [he] at hx
  exact hx i

/-- An actual affine polynomial, linear in its nodal values. -/
def simplexNodalInterpolant (c : Fin (d+1) → ℝ) : SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  ∑ i, c i • simplexBarycentric T i

theorem simplexNodalInterpolant_apply (c : Fin (d+1) → ℝ) (x : SpatialCoordinates d) :
    simplexNodalInterpolant T c x = ∑ i, c i*simplexBarycentric T i x := by
  classical
  have hs (s : Finset (Fin (d+1))) : (∑ i ∈ s, c i • simplexBarycentric T i) x =
      ∑ i ∈ s, c i*simplexBarycentric T i x := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty,AffineMap.coe_zero,Pi.zero_apply]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi,AffineMap.coe_add,Pi.add_apply,
        AffineMap.coe_smul,Pi.smul_apply,smul_eq_mul,ih]
  exact hs Finset.univ

theorem simplexNodalInterpolant_vertex (c : Fin (d+1) → ℝ) (j : Fin (d+1)) :
    simplexNodalInterpolant T c (T.points j) = c j := by
  rw [simplexNodalInterpolant_apply]
  simp only [simplexBarycentric_vertex,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- Exact reproduction of every affine polynomial, throughout space. -/
theorem simplexNodalInterpolant_reproduces (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    simplexNodalInterpolant T (fun i => p (T.points i)) = p := by
  ext x
  rw [simplexNodalInterpolant_apply]
  have hs := (simplexAffineBasis T).sum_coord_apply_eq_one x
  have he := Finset.univ.map_affineCombination (simplexAffineBasis T)
    (fun i => (simplexAffineBasis T).coord i x) hs p
  rw [(simplexAffineBasis T).affineCombination_coord_eq_self x,
    Finset.univ.affineCombination_eq_linear_combination _ _ hs] at he
  simpa only [simplexBarycentric,smul_eq_mul,mul_comm,Function.comp_apply,simplexAffineBasis_apply] using he.symm

theorem simplexNodalInterpolant_abs_le (c : Fin (d+1) → ℝ) (C : ℝ)
    (hc : ∀ i, |c i| ≤ C) {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points) :
    |simplexNodalInterpolant T c x| ≤ C := by
  rw [simplexNodalInterpolant_apply]
  calc
    _ ≤ ∑ i, |c i*simplexBarycentric T i x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i| *simplexBarycentric T i x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul,abs_of_nonneg (simplexBarycentric_nonneg T hx i)]
    _ ≤ ∑ i, C*simplexBarycentric T i x := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hc i) (simplexBarycentric_nonneg T hx i)
    _ = C := by rw [← Finset.mul_sum,simplexBarycentric_sum,mul_one]

end Carleman
