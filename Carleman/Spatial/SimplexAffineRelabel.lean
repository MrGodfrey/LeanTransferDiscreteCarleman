module

public import Carleman.Spatial.SimplexPositiveSupport

/-! Affine covariance of actual simplex cells and barycentric coordinates,
with an explicit permutation of the vertices. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem simplex_cell_affine_relabel (T U : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (A : SpatialCoordinates d ≃ᵃ[ℝ] SpatialCoordinates d) (e : Equiv.Perm (Fin (d+1)))
    (h : ∀ k, A (T.points k)=U.points (e k)) :
    A '' simplicialCell T.points=simplicialCell U.points := by
  rw [simplicialCell,simplicialCell]
  change A.toAffineMap '' convexHull ℝ (Set.range T.points)=_
  rw [A.toAffineMap.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨y,⟨k,rfl⟩,rfl⟩
    exact ⟨e k,(h k).symm⟩
  · rintro ⟨k,rfl⟩
    refine ⟨T.points (e.symm k),mem_range_self _,?_⟩
    change A (T.points (e.symm k))=U.points k
    simpa only [e.apply_symm_apply] using h (e.symm k)

theorem simplexBarycentric_affine_relabel (T U : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (A : SpatialCoordinates d ≃ᵃ[ℝ] SpatialCoordinates d) (e : Equiv.Perm (Fin (d+1)))
    (h : ∀ k, A (T.points k)=U.points (e k)) (k : Fin (d+1)) (x : SpatialCoordinates d) :
    simplexBarycentric U (e k) (A x)=simplexBarycentric T k x := by
  let p := (simplexBarycentric U (e k)).comp A.toAffineMap
  have hv : (fun l => p (T.points l))=(fun l => simplexBarycentric T k (T.points l)) := by
    funext l
    change simplexBarycentric U (e k) (A (T.points l))=simplexBarycentric T k (T.points l)
    simp only [h,simplexBarycentric_vertex,e.injective.eq_iff]
  have he : p=simplexBarycentric T k := calc
    p = simplexNodalInterpolant T (fun l => p (T.points l)) := (simplexNodalInterpolant_reproduces T p).symm
    _ = simplexNodalInterpolant T (fun l => simplexBarycentric T k (T.points l)) := by rw [hv]
    _ = simplexBarycentric T k := simplexNodalInterpolant_reproduces T _
  exact congrArg (fun q : SpatialCoordinates d →ᵃ[ℝ] ℝ => q x) he

end Carleman
