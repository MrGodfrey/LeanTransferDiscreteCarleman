module

public import Carleman.Spatial.SimplexNodalRemainder

/-! Actual first-order Taylor polynomials yield quadratic value and linear
gradient nodal errors under a proved Lipschitz bound on the classical derivative. -/
@[expose] public noncomputable section
open Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

def affineFirstOrder (f : SpatialCoordinates d → ℝ) (a : SpatialCoordinates d) :
    SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ (SpatialCoordinates d) (f a-fderiv ℝ f a a) +
    (fderiv ℝ f a).toLinearMap.toAffineMap

theorem affineFirstOrder_apply (f : SpatialCoordinates d → ℝ) (a x : SpatialCoordinates d) :
    affineFirstOrder f a x = f a+fderiv ℝ f a (x-a) := by
  change f a-fderiv ℝ f a a+fderiv ℝ f a x = f a+fderiv ℝ f a (x-a)
  rw [map_sub]
  ring

theorem affineFirstOrder_derivative (f : SpatialCoordinates d → ℝ) (a : SpatialCoordinates d) :
    affineScalarDerivative (affineFirstOrder f a) = fderiv ℝ f a := by
  have hh : HasFDerivAt (affineFirstOrder f a) (fderiv ℝ f a) a := by
    convert (hasFDerivAt_const (f a-fderiv ℝ f a a) a).add (fderiv ℝ f a).hasFDerivAt using 1
    · rfl
    · simp
  exact (affineScalar_hasFDerivAt (affineFirstOrder f a) a).unique hh

theorem affineFirstOrder_remainder {K : Set (SpatialCoordinates d)} (hK : Convex ℝ K)
    (f : SpatialCoordinates d → ℝ) (hf : ∀ x ∈ K, DifferentiableAt ℝ f x)
    (L : ℝ≥0) (hL : LipschitzOnWith L (fderiv ℝ f) K)
    {a : SpatialCoordinates d} (ha : a ∈ K) {h : ℝ} (hh : 0 ≤ h)
    (hdiam : ∀ x ∈ K, dist x a ≤ h) {x : SpatialCoordinates d} (hx : x ∈ K) :
    |f x-affineFirstOrder f a x| ≤ L*h^2 ∧
      ‖fderiv ℝ f x-affineScalarDerivative (affineFirstOrder f a)‖ ≤ L*h := by
  have hb : ∀ y ∈ K, ‖fderiv ℝ f y-fderiv ℝ f a‖ ≤ L*h := by
    intro y hy
    have hd : ‖fderiv ℝ f y-fderiv ℝ f a‖ ≤ L*dist y a := by
      simpa only [dist_eq_norm] using hL.dist_le_mul y hy a ha
    exact hd.trans (mul_le_mul_of_nonneg_left (hdiam y hy) L.property)
  refine ⟨?_,by rw [affineFirstOrder_derivative]; exact hb x hx⟩
  have ht := hK.norm_image_sub_le_of_norm_fderiv_le' hf hb ha hx
  have he : f x-affineFirstOrder f a x = f x-f a-fderiv ℝ f a (x-a) := by
    rw [affineFirstOrder_apply]
    ring
  rw [he]
  calc
    _ ≤ L*h*‖x-a‖ := ht
    _ ≤ L*h*h := mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hdiam x hx)
      (mul_nonneg L.property hh)
    _ = L*h^2 := by ring

theorem simplexNodal_error_of_lipschitz_derivative
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ x ∈ simplicialCell T.points, DifferentiableAt ℝ f x)
    (L : ℝ≥0) (hL : LipschitzOnWith L (fderiv ℝ f) (simplicialCell T.points))
    {h : ℝ} (hh : 0 ≤ h)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points) :
    |f x-simplexNodalInterpolant T (fun i => f (T.points i)) x| ≤ 2*L*h^2 := by
  have ha : T.points 0 ∈ simplicialCell T.points := subset_convexHull ℝ _ (Set.mem_range_self 0)
  have hb := fun (y : SpatialCoordinates d) (hy : y ∈ simplicialCell T.points) => (affineFirstOrder_remainder (simplicialCell_convex T.points)
    f hf L hL ha hh (fun z hz => hdiam z hz _ ha) (x := y) hy).1
  simpa only [mul_assoc] using simplexNodal_error_of_affine_approximation T f
    (affineFirstOrder f (T.points 0)) hb hx

theorem simplexNodal_gradient_error_of_lipschitz_derivative
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ x ∈ simplicialCell T.points, DifferentiableAt ℝ f x)
    (L : ℝ≥0) (hL : LipschitzOnWith L (fderiv ℝ f) (simplicialCell T.points))
    {a : SpatialCoordinates d} {r h κ : ℝ} (hr : 0 < r) (hh : 0 ≤ h)
    (hball : Metric.ball a r ⊆ simplicialCell T.points) (hshape : h ≤ κ*r)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points) :
    ‖fderiv ℝ f x-affineScalarDerivative (simplexNodalInterpolant T (fun i => f (T.points i)))‖ ≤
      (1+4*κ)*L*h := by
  have ha : T.points 0 ∈ simplicialCell T.points := subset_convexHull ℝ _ (Set.mem_range_self 0)
  have hb := fun (y : SpatialCoordinates d) (hy : y ∈ simplicialCell T.points) => affineFirstOrder_remainder (simplicialCell_convex T.points)
    f hf L hL ha hh (fun z hz => hdiam z hz _ ha) (x := y) hy
  have he := simplexNodal_derivative_error_of_affine_approximation T f
    (affineFirstOrder f (T.points 0)) hr (by positivity : 0 ≤ (L:ℝ)*h^2) hball
    (fun y hy => (hb y hy).1) (hb x hx).2
  have hratio : 4*((L:ℝ)*h^2)/r ≤ 4*κ*L*h := by
    apply (div_le_iff₀ hr).mpr
    have hm := mul_le_mul_of_nonneg_left hshape (by positivity : 0 ≤ 4*(L:ℝ)*h)
    nlinarith only [hm]
  exact he.trans (by nlinarith only [hratio])

end Carleman
