module

public import Carleman.Weights.SquaredCellIntegral
public import Carleman.Spatial.SimplicialLocalGradient

/-! The intrinsic product derivative equals the actual derivative of the
interpolation residual almost everywhere on the genuine closed cell. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem squaredNodalResidual_fderiv_ae
    {K : Set (SpatialCoordinates d)} {ρ : SpatialCoordinates d → ℝ}
    (hρ : ContDiffOn ℝ 2 ρ K)
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d) (hT : simplicialCell T.points ⊆ K)
    (q τ η : ℝ) (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    let w := allowedSquaredWeight ρ q τ η
    let I := simplexNodalInterpolant T (fun i => w (T.points i)*p (T.points i))
    ∀ᵐ x ∂volume.restrict (simplicialCell T.points),
      fderiv ℝ (fun y => w y*p y-I y) x =
        affineProductDerivative w (fderivWithin ℝ w K) p x-affineScalarDerivative I := by
  dsimp only
  rw [Measure.restrict_congr_set (simplexCell_ae_interior T)]
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with x hx
  have hw := (allowedSquaredWeight_hasFDerivWithinAt hρ q τ η (hT (interior_subset hx))).mono hT
  have hp := (affineProduct_hasFDerivWithinAt _ _ p hw).hasFDerivAt (mem_interior_iff_mem_nhds.mp hx)
  exact (hp.sub (affineScalar_hasFDerivAt _ x)).fderiv

theorem allowedSquaredWeight_local_residual_integrals
    {S : Set (SpatialCoordinates d)} {ρ : SpatialCoordinates d → ℝ}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hρ : ContDiffOn ℝ 2 ρ (closure S)) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C > (0:ℝ), ∀ (T : Affine.Simplex ℝ (SpatialCoordinates d) d),
      simplicialCell T.points ⊆ closure S →
    ∀ q : ℝ, 1 ≤ q → ∀ τ η : ℝ, |η|=1 → ∀ h : ℝ,
      (∀ x ∈ simplicialCell T.points, ∀ y ∈ simplicialCell T.points, dist x y ≤ h) → h*q ≤ 1 →
    ∀ (a : SpatialCoordinates d) (r : ℝ), 0 < r →
      Metric.ball a r ⊆ simplicialCell T.points → h ≤ κ*r →
    ∀ p : SpatialCoordinates d →ᵃ[ℝ] ℝ,
      let w := allowedSquaredWeight ρ q τ η
      let I := simplexNodalInterpolant T (fun i => w (T.points i)*p (T.points i))
      let e := fun x => w x*p x-I x
      let energy := q^4*(∫ x in simplicialCell T.points, w x*(p x)^2)+
        q^2*(∫ x in simplicialCell T.points, w x*‖derivativeOneFiber (fderiv ℝ p x)‖^2)
      (∫ x in simplicialCell T.points, (e x)^2/w x) ≤ C*h^4*energy ∧
      (∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ e x)‖^2/w x) ≤ C*h^2*energy := by
  obtain ⟨C,hC,hbound⟩ := allowedSquaredWeight_local_integral_errors hS hc hcompact hρ hκ
  refine ⟨C,hC,?_⟩
  intro T hT q hq τ η hη h hdiam hsmall a r hr hball hshape p
  have hb := hbound T hT q hq τ η hη h hdiam hsmall a r hr hball hshape p
  dsimp only at hb ⊢
  refine ⟨hb.1,?_⟩
  have he := squaredNodalResidual_fderiv_ae hρ T hT q τ η p
  calc
    _ = ∫ x in simplicialCell T.points,
        ‖derivativeOneFiber (affineProductDerivative (allowedSquaredWeight ρ q τ η)
          (fderivWithin ℝ (allowedSquaredWeight ρ q τ η) (closure S)) p x-
          affineScalarDerivative (simplexNodalInterpolant T
            (fun i => allowedSquaredWeight ρ q τ η (T.points i)*p (T.points i))))‖^2/
          allowedSquaredWeight ρ q τ η x := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    _ ≤ _ := hb.2

end Carleman
