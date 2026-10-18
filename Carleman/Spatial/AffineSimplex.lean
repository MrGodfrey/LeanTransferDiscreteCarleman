module

public import Carleman.Spatial.AffineChangeVolume

/-! Actual affine images of simplices and their nodal polynomials. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
  (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d) (b : SpatialCoordinates d)

def affineChangeEquiv : SpatialCoordinates d ≃ᵃ[ℝ] SpatialCoordinates d :=
  AffineEquiv.ofLinearEquiv A.toLinearEquiv 0 b

theorem affineChangeEquiv_apply (x : SpatialCoordinates d) :
    affineChangeEquiv A b x = affineChange A b x := by
  simp [affineChangeEquiv,affineChange_apply]

def affineSimplex : Affine.Simplex ℝ (SpatialCoordinates d) d :=
  T.map (affineChangeEquiv A b).toAffineMap (affineChangeEquiv A b).injective

theorem affineSimplex_points (i : Fin (d+1)) :
    (affineSimplex T A b).points i = affineChange A b (T.points i) :=
  affineChangeEquiv_apply A b (T.points i)

theorem affineSimplex_cell :
    simplicialCell (affineSimplex T A b).points = affineChange A b '' simplicialCell T.points := by
  have h := (affineChangeEquiv A b).toAffineMap.image_convexHull (Set.range T.points)
  have hp : (affineSimplex T A b).points = (affineChange A b) ∘ T.points :=
    funext (affineSimplex_points T A b)
  rw [simplicialCell,hp,Set.range_comp]
  simpa only [simplicialCell,AffineEquiv.coe_toAffineMap,affineChangeEquiv_apply] using h.symm

theorem affineSimplex_nodal_comp (c : Fin (d+1) → ℝ) (x : SpatialCoordinates d) :
    simplexNodalInterpolant (affineSimplex T A b) c (affineChange A b x) =
      simplexNodalInterpolant T c x := by
  let p := (simplexNodalInterpolant (affineSimplex T A b) c).comp
    (affineChangeEquiv A b).toAffineMap
  have hp : (fun i => p (T.points i)) = c := by
    funext i
    change simplexNodalInterpolant (affineSimplex T A b) c
      (affineChangeEquiv A b (T.points i)) = c i
    rw [affineChangeEquiv_apply,← affineSimplex_points,simplexNodalInterpolant_vertex]
  have h := congrArg (fun q : SpatialCoordinates d →ᵃ[ℝ] ℝ => q x)
    (simplexNodalInterpolant_reproduces T p)
  rw [hp] at h
  simpa only [p,AffineMap.comp_apply,AffineEquiv.coe_toAffineMap,affineChangeEquiv_apply] using h.symm

theorem affineSimplex_derivative_comp (c : Fin (d+1) → ℝ) :
    (simplexNodalDerivativeLinear (affineSimplex T A b) c).comp A.toContinuousLinearMap =
      simplexNodalDerivativeLinear T c := by
  have hF : HasFDerivAt (affineChange A b) A.toContinuousLinearMap 0 := by
    change HasFDerivAt (fun x => A x+b) _ 0
    exact (A.hasFDerivAt (x := 0)).add_const b
  have h := (simplexNodalInterpolant_hasFDerivAt (affineSimplex T A b) c
    (affineChange A b 0)).comp 0 hF
  have he : ((simplexNodalInterpolant (affineSimplex T A b) c) ∘ affineChange A b) =
      simplexNodalInterpolant T c := funext (affineSimplex_nodal_comp T A b c)
  rw [he] at h
  exact h.unique (simplexNodalInterpolant_hasFDerivAt T c 0)

theorem affineSimplex_derivative (c : Fin (d+1) → ℝ) :
    simplexNodalDerivativeLinear (affineSimplex T A b) c =
      (simplexNodalDerivativeLinear T c).comp A.symm.toContinuousLinearMap := by
  ext x
  have h := congrArg (fun L : SpatialCoordinates d →L[ℝ] ℝ => L (A.symm x))
    (affineSimplex_derivative_comp T A b c)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using h

end Carleman
