module

public import Carleman.Spatial.SimplexWithinInterpolation

/-! The actual derivative field of a smooth scalar times an affine function,
with a quantitative Lipschitz bound that retains both product-rule terms. -/
@[expose] public noncomputable section
open Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

def affineProductDerivative (w : SpatialCoordinates d → ℝ)
    (W : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] ℝ)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) (x : SpatialCoordinates d) : SpatialCoordinates d →L[ℝ] ℝ :=
  w x • affineScalarDerivative p+p x • W x

theorem affineProduct_hasFDerivWithinAt {K : Set (SpatialCoordinates d)}
    (w : SpatialCoordinates d → ℝ) (W : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] ℝ)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) {x : SpatialCoordinates d}
    (hw : HasFDerivWithinAt w (W x) K x) :
    HasFDerivWithinAt (fun y => w y*p y) (affineProductDerivative w W p x) K x := by
  convert hw.mul (affineScalar_hasFDerivAt p x).hasFDerivWithinAt using 1
  rfl

theorem affineProductDerivative_lipschitzOn {K : Set (SpatialCoordinates d)} (hK : Convex ℝ K)
    (w : SpatialCoordinates d → ℝ) (W : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] ℝ)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ)
    (hw : ∀ x ∈ K, HasFDerivWithinAt w (W x) K x)
    (P L₁ L₂ : ℝ≥0) (hp : ∀ x ∈ K, |p x| ≤ P)
    (hW : ∀ x ∈ K, ‖W x‖ ≤ L₁) (hLip : LipschitzOnWith L₂ W K) :
    LipschitzOnWith (P*L₂+2*‖affineScalarDerivative p‖₊*L₁) (affineProductDerivative w W p) K := by
  have hwLip : LipschitzOnWith L₁ w K :=
    hK.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hw hW
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hwxy : |w x-w y| ≤ L₁*dist x y := by
    simpa only [Real.dist_eq] using hwLip.dist_le_mul x hx y hy
  have hpxy : |p x-p y| ≤ ‖affineScalarDerivative p‖*dist x y := by
    simpa only [Real.dist_eq,coe_nnnorm] using (affineScalar_lipschitz p).dist_le_mul x y
  have hWxy : ‖W x-W y‖ ≤ L₂*dist x y := by
    simpa only [dist_eq_norm] using hLip.dist_le_mul x hx y hy
  have he : affineProductDerivative w W p x-affineProductDerivative w W p y =
      (w x-w y) • affineScalarDerivative p + p x • (W x-W y)+(p x-p y) • W y := by
    dsimp only [affineProductDerivative]
    module
  rw [dist_eq_norm,he]
  calc
    _ ≤ ‖(w x-w y) • affineScalarDerivative p‖+‖p x • (W x-W y)‖+‖(p x-p y) • W y‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = |w x-w y| *‖affineScalarDerivative p‖+|p x| *‖W x-W y‖+|p x-p y| *‖W y‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ (L₁*dist x y)*‖affineScalarDerivative p‖+(P*(L₂*dist x y))+
        (‖affineScalarDerivative p‖*dist x y)*L₁ := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hwxy (norm_nonneg _))
        (mul_le_mul (hp x hx) hWxy (norm_nonneg _) P.property))
        (mul_le_mul hpxy (hW y hy) (norm_nonneg _) (by positivity))
    _ = _ := by simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,coe_nnnorm]; ring

theorem affineProduct_nodal_value_error
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (w : SpatialCoordinates d → ℝ) (W : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] ℝ)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ)
    (hw : ∀ x ∈ simplicialCell T.points, HasFDerivWithinAt w (W x) (simplicialCell T.points) x)
    (P L₁ L₂ : ℝ≥0) (hp : ∀ x ∈ simplicialCell T.points, |p x| ≤ P)
    (hW : ∀ x ∈ simplicialCell T.points, ‖W x‖ ≤ L₁)
    (hLip : LipschitzOnWith L₂ W (simplicialCell T.points))
    {h : ℝ} (hh : 0 ≤ h)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points) :
    |w x*p x-simplexNodalInterpolant T (fun i => w (T.points i)*p (T.points i)) x| ≤
      2*(P*L₂+2*‖affineScalarDerivative p‖*L₁)*h^2 := by
  exact simplexNodal_within_value_error T (fun y => w y*p y) (affineProductDerivative w W p)
    (fun y hy => affineProduct_hasFDerivWithinAt w W p (hw y hy)) _
    (affineProductDerivative_lipschitzOn (simplicialCell_convex T.points) w W p hw P L₁ L₂ hp hW hLip)
    hh hdiam hx

theorem affineProduct_nodal_gradient_error
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (w : SpatialCoordinates d → ℝ) (W : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] ℝ)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ)
    (hw : ∀ x ∈ simplicialCell T.points, HasFDerivWithinAt w (W x) (simplicialCell T.points) x)
    (P L₁ L₂ : ℝ≥0) (hp : ∀ x ∈ simplicialCell T.points, |p x| ≤ P)
    (hW : ∀ x ∈ simplicialCell T.points, ‖W x‖ ≤ L₁)
    (hLip : LipschitzOnWith L₂ W (simplicialCell T.points))
    {a : SpatialCoordinates d} {r h κ : ℝ} (hr : 0 < r) (hh : 0 ≤ h)
    (hball : Metric.ball a r ⊆ simplicialCell T.points) (hshape : h ≤ κ*r)
    (hdiam : ∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h)
    {x : SpatialCoordinates d} (hx : x ∈ simplicialCell T.points) :
    ‖affineProductDerivative w W p x-
      affineScalarDerivative (simplexNodalInterpolant T (fun i => w (T.points i)*p (T.points i)))‖ ≤
      (1+4*κ)*(P*L₂+2*‖affineScalarDerivative p‖*L₁)*h := by
  exact simplexNodal_within_gradient_error T (fun y => w y*p y) (affineProductDerivative w W p)
    (fun y hy => affineProduct_hasFDerivWithinAt w W p (hw y hy)) _
    (affineProductDerivative_lipschitzOn (simplicialCell_convex T.points) w W p hw P L₁ L₂ hp hW hLip)
    hr hh hball hshape hdiam hx

theorem affineProduct_derivative_interior {K : Set (SpatialCoordinates d)}
    (w : SpatialCoordinates d → ℝ) (W : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] ℝ)
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) {x : SpatialCoordinates d} (hx : x ∈ interior K)
    (hw : HasFDerivWithinAt w (W x) K x) :
    fderiv ℝ (fun y => w y*p y) x=affineProductDerivative w W p x :=
  ((affineProduct_hasFDerivWithinAt w W p hw).hasFDerivAt (mem_interior_iff_mem_nhds.mp hx)).fderiv

theorem derivativeField_lipschitzOn_of_within_bound
    {K : Set (SpatialCoordinates d)} (hK : Convex ℝ K)
    (W : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] ℝ)
    (H : SpatialCoordinates d → SpatialCoordinates d →L[ℝ] (SpatialCoordinates d →L[ℝ] ℝ))
    (hH : ∀ x ∈ K, HasFDerivWithinAt W (H x) K x)
    (L : ℝ≥0) (hL : ∀ x ∈ K, ‖H x‖ ≤ L) : LipschitzOnWith L W K :=
  hK.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hH hL

end Carleman
