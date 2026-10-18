module

public import Carleman.Spatial.SimplexTaylorInterpolation

/-! Nodal Taylor estimates from genuine derivatives within a closed simplex.
The derivative field is linked by HasFDerivWithinAt; no exterior extension is used. -/
@[expose] public noncomputable section
open Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

def affineJetPolynomial (v : ℝ) (A : SpatialCoordinates d →L[ℝ] ℝ) (a : SpatialCoordinates d) :
    SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ (SpatialCoordinates d) (v-A a)+A.toLinearMap.toAffineMap

theorem affineJetPolynomial_apply (v : ℝ) (A : SpatialCoordinates d →L[ℝ] ℝ) (a x : SpatialCoordinates d) :
    affineJetPolynomial v A a x=v+A (x-a) := by
  change v-A a+A x=v+A (x-a)
  rw [map_sub]
  ring

theorem affineJetPolynomial_derivative (v : ℝ) (A : SpatialCoordinates d →L[ℝ] ℝ) (a : SpatialCoordinates d) :
    affineScalarDerivative (affineJetPolynomial v A a)=A := by
  have hh : HasFDerivAt (affineJetPolynomial v A a) A a := by
    convert (hasFDerivAt_const (v-A a) a).add A.hasFDerivAt using 1
    · rfl
    · simp
  exact (affineScalar_hasFDerivAt (affineJetPolynomial v A a) a).unique hh

theorem withinFirstOrder_remainder {K : Set (SpatialCoordinates d)} (hK : Convex ℝ K)
    (f : SpatialCoordinates d → ℝ) (F : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] ℝ)
    (hf : ∀ x ∈ K, HasFDerivWithinAt f (F x) K x)
    (L : ℝ≥0) (hL : LipschitzOnWith L F K)
    {a : SpatialCoordinates d} (ha : a ∈ K) {h : ℝ} (hh : 0 ≤ h)
    (hdiam : ∀ x ∈ K, dist x a ≤ h) {x : SpatialCoordinates d} (hx : x ∈ K) :
    |f x-affineJetPolynomial (f a) (F a) a x| ≤ L*h^2 ∧
      ‖F x-affineScalarDerivative (affineJetPolynomial (f a) (F a) a)‖ ≤ L*h := by
  have hb : ∀ y ∈ K, ‖F y-F a‖ ≤ L*h := by
    intro y hy
    have hd : ‖F y-F a‖ ≤ L*dist y a := by simpa only [dist_eq_norm] using hL.dist_le_mul y hy a ha
    exact hd.trans (mul_le_mul_of_nonneg_left (hdiam y hy) L.property)
  refine ⟨?_,by rw [affineJetPolynomial_derivative]; exact hb x hx⟩
  have ht := hK.norm_image_sub_le_of_norm_hasFDerivWithin_le' hf hb ha hx
  have he : f x-affineJetPolynomial (f a) (F a) a x = f x-f a-F a (x-a) := by
    rw [affineJetPolynomial_apply]
    ring
  rw [he]
  calc
    _ ≤ L*h*‖x-a‖ := ht
    _ ≤ L*h*h := mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hdiam x hx)
      (mul_nonneg L.property hh)
    _ = L*h^2 := by ring

theorem simplexNodal_within_value_error
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (f : SpatialCoordinates d → ℝ)
    (F : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] ℝ)
    (hf : ∀ x ∈ simplicialCell T.points, HasFDerivWithinAt f (F x) (simplicialCell T.points) x)
    (L : ℝ≥0) (hL : LipschitzOnWith L F (simplicialCell T.points))
    {h : ℝ} (hh : 0 ≤ h)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points) :
    |f x-simplexNodalInterpolant T (fun i => f (T.points i)) x| ≤ 2*L*h^2 := by
  have ha : T.points 0 ∈ simplicialCell T.points := subset_convexHull ℝ _ (Set.mem_range_self 0)
  have hb := fun (y : SpatialCoordinates d) (hy : y ∈ simplicialCell T.points) =>
    (withinFirstOrder_remainder (simplicialCell_convex T.points) f F hf L hL ha hh
      (fun z hz => hdiam z hz _ ha) (x := y) hy).1
  simpa only [mul_assoc] using simplexNodal_error_of_affine_approximation T f
    (affineJetPolynomial (f (T.points 0)) (F (T.points 0)) (T.points 0)) hb hx

theorem simplexNodal_within_gradient_error
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (f : SpatialCoordinates d → ℝ)
    (F : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] ℝ)
    (hf : ∀ x ∈ simplicialCell T.points, HasFDerivWithinAt f (F x) (simplicialCell T.points) x)
    (L : ℝ≥0) (hL : LipschitzOnWith L F (simplicialCell T.points))
    {a : SpatialCoordinates d} {r h κ : ℝ} (hr : 0 < r) (hh : 0 ≤ h)
    (hball : Metric.ball a r ⊆ simplicialCell T.points) (hshape : h ≤ κ*r)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points) :
    ‖F x-affineScalarDerivative (simplexNodalInterpolant T (fun i => f (T.points i)))‖ ≤
      (1+4*κ)*L*h := by
  let p := affineJetPolynomial (f (T.points 0)) (F (T.points 0)) (T.points 0)
  let I := simplexNodalInterpolant T (fun i => f (T.points i))
  have ha : T.points 0 ∈ simplicialCell T.points := subset_convexHull ℝ _ (Set.mem_range_self 0)
  have hb := fun (y : SpatialCoordinates d) (hy : y ∈ simplicialCell T.points) =>
    withinFirstOrder_remainder (simplicialCell_convex T.points) f F hf L hL ha hh
      (fun z hz => hdiam z hz _ ha) (x := y) hy
  have hq : ∀ y ∈ Metric.ball a r, |(I-p) y| ≤ (L:ℝ)*h^2 := by
    intro y hy
    rw [← simplexNodalInterpolant_sub_affine]
    exact simplexNodalInterpolant_abs_le T _ ((L:ℝ)*h^2)
      (fun i => (hb _ (subset_convexHull ℝ _ (Set.mem_range_self i))).1) (hball hy)
  have he : affineScalarDerivative (I-p) = affineScalarDerivative I-affineScalarDerivative p :=
    (affineScalar_hasFDerivAt (I-p) x).unique
      ((affineScalar_hasFDerivAt I x).sub (affineScalar_hasFDerivAt p x))
  have hbound := affineScalarDerivative_inball_bound (I-p) hr (by positivity : 0 ≤ (L:ℝ)*h^2) hq
  rw [he] at hbound
  have hratio : 4*((L:ℝ)*h^2)/r ≤ 4*κ*L*h := by
    apply (div_le_iff₀ hr).mpr
    have hm := mul_le_mul_of_nonneg_left hshape (by positivity : 0 ≤ 4*(L:ℝ)*h)
    nlinarith only [hm]
  calc
    _ ≤ ‖F x-affineScalarDerivative p‖+‖affineScalarDerivative p-affineScalarDerivative I‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (L:ℝ)*h+4*((L:ℝ)*h^2)/r := add_le_add (hb x hx).2 (by simpa only [norm_sub_rev] using hbound)
    _ ≤ (1+4*κ)*L*h := by nlinarith only [hratio]

end Carleman
