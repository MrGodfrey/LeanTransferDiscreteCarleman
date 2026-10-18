module

public import Carleman.Weights.SquaredCellDerivatives

/-! Uniform closed-cell nodal errors for the actual squared allowed weight
multiplied by an arbitrary affine state. -/
@[expose] public noncomputable section
open Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

theorem allowedSquaredWeight_product_errors
    {S : Set (SpatialCoordinates d)} {ρ : SpatialCoordinates d → ℝ}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hρ : ContDiffOn ℝ 2 ρ (closure S)) :
    ∃ C > (0:ℝ), ∀ (T : Affine.Simplex ℝ (SpatialCoordinates d) d),
      simplicialCell T.points ⊆ closure S →
    ∀ q : ℝ, 1 ≤ q → ∀ τ η : ℝ, |η|=1 → ∀ h : ℝ,
      (∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h) → h*q ≤ 1 →
    ∀ (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) (P : ℝ≥0),
      (∀ x ∈ simplicialCell T.points, |p x| ≤ P) →
    ∀ x ∈ simplicialCell T.points,
      |allowedSquaredWeight ρ q τ η x*p x-
        simplexNodalInterpolant T (fun i => allowedSquaredWeight ρ q τ η (T.points i)*p (T.points i)) x| ≤
        2*C*allowedSquaredWeight ρ q τ η (T.points 0)*
          (q^2*P+2*q*‖affineScalarDerivative p‖)*h^2 ∧
      ∀ (a : SpatialCoordinates d) (r κ : ℝ), 0 < r →
        Metric.ball a r ⊆ simplicialCell T.points → h ≤ κ*r →
        ‖affineProductDerivative (allowedSquaredWeight ρ q τ η)
          (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) (closure S)) p x-
          affineScalarDerivative (simplexNodalInterpolant T
            (fun i => allowedSquaredWeight ρ q τ η (T.points i)*p (T.points i)))‖ ≤
          (1+4*κ)*C*allowedSquaredWeight ρ q τ η (T.points 0)*
            (q^2*P+2*q*‖affineScalarDerivative p‖)*h := by
  obtain ⟨C,hC,hdata⟩ := allowedSquaredWeight_local_derivative_data hS hc hcompact hρ
  refine ⟨C,hC,?_⟩
  intro T hT q hq τ η hη h hdiam hsmall p P hp x hx
  have hh : 0 ≤ h := (dist_nonneg (x := x) (y := x)).trans (hdiam x hx x hx)
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hb : 0 ≤ allowedSquaredWeight ρ q τ η (T.points 0) := sq_nonneg _
  have hL₁ : 0 ≤ C*q*allowedSquaredWeight ρ q τ η (T.points 0) := by positivity
  have hL₂ : 0 ≤ C*q^2*allowedSquaredWeight ρ q τ η (T.points 0) := by positivity
  obtain ⟨hfirst,hLip⟩ := hdata T hT q hq τ η hη h hdiam hsmall
  have hw (y : SpatialCoordinates d) (hy : y ∈ simplicialCell T.points) :=
    (allowedSquaredWeight_hasFDerivWithinAt hρ q τ η (hT hy)).mono hT
  have hW (y : SpatialCoordinates d) (hy : y ∈ simplicialCell T.points) :
      ‖fderivWithin ℝ (allowedSquaredWeight ρ q τ η) (closure S) y‖ ≤
        (Real.toNNReal (C*q*allowedSquaredWeight ρ q τ η (T.points 0)) : ℝ) := by
    rw [Real.coe_toNNReal _ hL₁]
    exact hfirst y hy
  constructor
  · have he := affineProduct_nodal_value_error T (allowedSquaredWeight ρ q τ η)
      (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) (closure S)) p hw P
      (Real.toNNReal (C*q*allowedSquaredWeight ρ q τ η (T.points 0)))
      (Real.toNNReal (C*q^2*allowedSquaredWeight ρ q τ η (T.points 0))) hp hW hLip hh hdiam hx
    rw [Real.coe_toNNReal _ hL₁,Real.coe_toNNReal _ hL₂] at he
    convert he using 1
    ring
  · intro a r κ hr hball hshape
    have he := affineProduct_nodal_gradient_error T (allowedSquaredWeight ρ q τ η)
      (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) (closure S)) p hw P
      (Real.toNNReal (C*q*allowedSquaredWeight ρ q τ η (T.points 0)))
      (Real.toNNReal (C*q^2*allowedSquaredWeight ρ q τ η (T.points 0))) hp hW hLip
      hr hh hball hshape hdiam hx
    rw [Real.coe_toNNReal _ hL₁,Real.coe_toNNReal _ hL₂] at he
    convert he using 1
    ring

end Carleman
