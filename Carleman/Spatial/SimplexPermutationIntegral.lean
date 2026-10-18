module

public import Carleman.Spatial.SimplexSecondMoments
public import Carleman.Spatial.SimplexReferenceMap

/-! Genuine affine permutations of vertices preserve simplex integration. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
  (e : Equiv.Perm (Fin (d+1)))

def simplexPermutationLinear : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d :=
  simplexCoordinateLinearEquiv T (T.reindex e.symm)

def simplexPermutationShift : SpatialCoordinates d :=
  simplexCoordinateShift T (T.reindex e.symm)

theorem simplexPermutation_vertex (i : Fin (d+1)) :
    affineChange (simplexPermutationLinear T e) (simplexPermutationShift T e) (T.points i) =
      T.points (e i) := by
  rw [← affineSimplex_points]
  change (affineSimplex T (simplexCoordinateLinearEquiv T (T.reindex e.symm))
    (simplexCoordinateShift T (T.reindex e.symm))).points i = _
  rw [affineSimplex_coordinate_eq]
  rfl

theorem simplexPermutation_cell :
    affineChange (simplexPermutationLinear T e) (simplexPermutationShift T e) ''
      simplicialCell T.points = simplicialCell T.points := by
  rw [← affineSimplex_cell]
  change simplicialCell (affineSimplex T (simplexCoordinateLinearEquiv T (T.reindex e.symm))
    (simplexCoordinateShift T (T.reindex e.symm))).points = _
  rw [affineSimplex_coordinate_eq]
  exact congrArg (convexHull ℝ) (T.reindex_range_points e.symm)

theorem simplexPermutation_barycentric (i : Fin (d+1)) (x : SpatialCoordinates d) :
    simplexBarycentric T (e i)
      (affineChange (simplexPermutationLinear T e) (simplexPermutationShift T e) x) =
      simplexBarycentric T i x := by
  let p := (simplexBarycentric T (e i)).comp
    (affineChangeEquiv (simplexPermutationLinear T e) (simplexPermutationShift T e)).toAffineMap
  have hp : p = simplexBarycentric T i := by
    rw [← simplexNodalInterpolant_reproduces T p,
      ← simplexNodalInterpolant_reproduces T (simplexBarycentric T i)]
    congr 1
    funext j
    simp only [p,AffineMap.comp_apply,AffineEquiv.coe_toAffineMap,affineChangeEquiv_apply,
      simplexPermutation_vertex,simplexBarycentric_vertex,Equiv.apply_eq_iff_eq]
  simpa only [p,AffineMap.comp_apply,AffineEquiv.coe_toAffineMap,affineChangeEquiv_apply] using
    congrArg (fun q : SpatialCoordinates d →ᵃ[ℝ] ℝ => q x) hp

theorem simplexPermutation_jacobian : affineJacobian (simplexPermutationLinear T e) = 1 := by
  have h := integral_comp_affineChange (simplexPermutationLinear T e)
    (simplexPermutationShift T e) (simplicialCell T.points) (fun _ => (1:ℝ))
  rw [simplexPermutation_cell] at h
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one] at h
  have hv : 0 < volume.real (simplicialCell T.points) :=
    ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume
      (simplicialCell_interior_nonempty T)).ne' (simplicialCell_compact _).measure_ne_top
  have hi : (affineJacobian (simplexPermutationLinear T e))⁻¹ = 1 := by
    nlinarith
  exact inv_eq_one.mp hi

theorem integral_comp_simplexPermutation (f : SpatialCoordinates d → ℝ) :
    (∫ x in simplicialCell T.points,
      f (affineChange (simplexPermutationLinear T e) (simplexPermutationShift T e) x)) =
      ∫ x in simplicialCell T.points, f x := by
  rw [integral_comp_affineChange,simplexPermutation_cell,simplexPermutation_jacobian,inv_one,one_mul]

theorem integral_simplexBarycentric_mul_permutation (i j : Fin (d+1)) :
    (∫ x in simplicialCell T.points, simplexBarycentric T (e i) x * simplexBarycentric T (e j) x) =
      ∫ x in simplicialCell T.points, simplexBarycentric T i x * simplexBarycentric T j x := by
  rw [← integral_comp_simplexPermutation T e]
  simp only [simplexPermutation_barycentric]

end Carleman
