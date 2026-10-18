module

public import Carleman.Spatial.AffineWeakGradient
public import Carleman.Spatial.SimplexNodalLp
public import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative nodal interpolation from an actual affine approximation.
All function values and derivatives are classical; no H² embedding is assumed. -/
@[expose] public noncomputable section
open Set
namespace Carleman
variable {d : ℕ}

theorem affineScalarDerivative_inball_bound (p : SpatialCoordinates d →ᵃ[ℝ] ℝ)
    {a : SpatialCoordinates d} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hb : ∀ x ∈ Metric.ball a r, |p x| ≤ R) : ‖affineScalarDerivative p‖ ≤ 4*R/r := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro x hx
  have ha := hb a (Metric.mem_ball_self hr)
  have hy : a+(r/2) • x ∈ Metric.ball a r := by
    rw [Metric.mem_ball,dist_eq_norm]
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hr),hx,mul_one]
    linarith
  have he : p (a+(r/2) • x)-p a = (r/2)*affineScalarDerivative p x := by
    have hv := p.linear_apply_vsub (a+(r/2) • x) a
    change p.linear (a+(r/2) • x-a) = p (a+(r/2) • x)-p a at hv
    rw [← hv]
    rw [add_sub_cancel_left,map_smul]
    rfl
  have hn : |p (a+(r/2) • x)-p a| ≤ 2*R :=
    (abs_sub _ _).trans (by linarith [hb _ hy])
  rw [he,abs_mul,abs_of_pos (half_pos hr)] at hn
  change ‖affineScalarDerivative p x‖ ≤ 4*R/r
  rw [Real.norm_eq_abs]
  apply (le_div_iff₀ hr).mpr
  nlinarith only [hn]

theorem simplexNodalInterpolant_sub_affine
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (f : SpatialCoordinates d → ℝ)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    simplexNodalInterpolant T (fun i => f (T.points i)-p (T.points i)) =
      simplexNodalInterpolant T (fun i => f (T.points i))-p := by
  have he := simplexNodalInterpolant_reproduces T p
  ext x
  change simplexNodalInterpolant T _ x = simplexNodalInterpolant T _ x-p x
  conv_rhs => rw [← he]
  simp only [simplexNodalInterpolant_apply,sub_mul,Finset.sum_sub_distrib]

theorem simplexNodal_error_of_affine_approximation
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (f : SpatialCoordinates d → ℝ)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) {R : ℝ}
    (hb : ∀ x ∈ simplicialCell T.points, |f x-p x| ≤ R)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points) :
    |f x-simplexNodalInterpolant T (fun i => f (T.points i)) x| ≤ 2*R := by
  have hi := simplexNodalInterpolant_abs_le T (fun i => f (T.points i)-p (T.points i)) R
    (fun i => hb _ (subset_convexHull ℝ _ (Set.mem_range_self i))) hx
  rw [simplexNodalInterpolant_sub_affine] at hi
  change |simplexNodalInterpolant T (fun i => f (T.points i)) x-p x| ≤ R at hi
  have he : f x-simplexNodalInterpolant T (fun i => f (T.points i)) x =
      (f x-p x)-(simplexNodalInterpolant T (fun i => f (T.points i)) x-p x) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hb x hx])

theorem simplexNodal_derivative_error_of_affine_approximation
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (f : SpatialCoordinates d → ℝ)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) {a : SpatialCoordinates d} {r R G : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hball : Metric.ball a r ⊆ simplicialCell T.points)
    (hb : ∀ x ∈ simplicialCell T.points, |f x-p x| ≤ R)
    {x : SpatialCoordinates d}
    (hg : ‖fderiv ℝ f x-affineScalarDerivative p‖ ≤ G) :
    ‖fderiv ℝ f x-affineScalarDerivative (simplexNodalInterpolant T (fun i => f (T.points i)))‖ ≤
      G+4*R/r := by
  let I := simplexNodalInterpolant T (fun i => f (T.points i))
  have hq : ∀ y ∈ Metric.ball a r, |(I-p) y| ≤ R := by
    intro y hy
    rw [← simplexNodalInterpolant_sub_affine]
    exact simplexNodalInterpolant_abs_le T _ R
      (fun i => hb _ (subset_convexHull ℝ _ (Set.mem_range_self i))) (hball hy)
  have he : affineScalarDerivative (I-p) = affineScalarDerivative I-affineScalarDerivative p :=
    (affineScalar_hasFDerivAt (I-p) x).unique
      ((affineScalar_hasFDerivAt I x).sub (affineScalar_hasFDerivAt p x))
  have hbound := affineScalarDerivative_inball_bound (I-p) hr hR hq
  rw [he] at hbound
  calc
    _ ≤ ‖fderiv ℝ f x-affineScalarDerivative p‖ +
        ‖affineScalarDerivative p-affineScalarDerivative I‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ G+4*R/r := add_le_add hg (by simpa only [norm_sub_rev] using hbound)

end Carleman
