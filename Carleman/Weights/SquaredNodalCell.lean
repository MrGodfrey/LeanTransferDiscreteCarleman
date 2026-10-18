module

public import Carleman.Weights.SquaredNodalIntegrability
public import Carleman.Spatial.SimplicialDiameter

/-! The local squared-weight estimate for the actual global nodal residual. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem allowedSquaredWeight_nodal_cell_integrals
    {S : Set (SpatialCoordinates d)} {ρ : SpatialCoordinates d → ℝ}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hρ : ContDiffOn ℝ 2 ρ (closure S)) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C > (0:ℝ), ∀ {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι), M.FaceMatching →
    ∀ q : ℝ, 1 ≤ q → ∀ τ η : ℝ, |η|=1 → M.maxDiameter*q ≤ 1 →
    ∀ (a : ι → SpatialCoordinates d) (r : ι → ℝ),
      (∀ i, 0 < r i) → (∀ i, Metric.ball (a i) (r i) ⊆ M.cell i) →
      (∀ i, M.cellDiameter i ≤ κ*r i) →
    ∀ (f : SpatialCoordinates d → ℝ) (i : ι),
      let w := allowedSquaredWeight ρ q τ η
      let u := M.nodalFunction f
      let e := M.nodalProductResidual w f
      let energy := q^4*(∫ x in M.cell i, w x*(u x)^2)+
        q^2*(∫ x in M.cell i, w x*‖derivativeOneFiber (fderiv ℝ u x)‖^2)
      (∫ x in M.cell i, (e x)^2/w x) ≤ C*(M.cellDiameter i)^4*energy ∧
      (∫ x in M.cell i, ‖derivativeOneFiber (fderiv ℝ e x)‖^2/w x) ≤ C*(M.cellDiameter i)^2*energy := by
  obtain ⟨C,hC,hbound⟩ := allowedSquaredWeight_local_residual_integrals hS hc hcompact hρ hκ
  refine ⟨C,hC,?_⟩
  intro ι _ M hM q hq τ η hη hsmall a r hr hball hshape f i
  let w := allowedSquaredWeight ρ q τ η
  let p := M.localNodal f i
  let I := simplexNodalInterpolant (M.simplex i) (fun k => w ((M.simplex i).points k)*p ((M.simplex i).points k))
  let e := fun x => w x*p x-I x
  have hlocal := hbound (M.simplex i) (M.inside i) q hq τ η hη (M.cellDiameter i)
    (fun _ hx _ hy => M.dist_le_cellDiameter i hx hy)
    ((mul_le_mul_of_nonneg_right (M.cellDiameter_le_max i) (zero_le_one.trans hq)).trans hsmall)
    (a i) (r i) (hr i) (hball i) (hshape i) p
  have hv : (∫ x in M.cell i, (M.nodalProductResidual w f x)^2/w x) =
      ∫ x in M.cell i, (e x)^2/w x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (simplicialCell_measurable _)] with x hx
    rw [M.nodalProductResidual_on_cell hM w f i hx]
  have hg : (∫ x in M.cell i, ‖derivativeOneFiber (fderiv ℝ (M.nodalProductResidual w f) x)‖^2/w x) =
      ∫ x in M.cell i, ‖derivativeOneFiber (fderiv ℝ e x)‖^2/w x := by
    apply integral_congr_ae
    filter_upwards [M.nodalProductResidual_fderiv_ae hM w f i] with x hx
    rw [hx]
  have hs : (∫ x in M.cell i, w x*(M.nodalFunction f x)^2) =
      ∫ x in M.cell i, w x*(p x)^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (simplicialCell_measurable _)] with x hx
    rw [M.nodalFunction_on_cell hM f i hx]
  have ht : (∫ x in M.cell i, w x*‖derivativeOneFiber (fderiv ℝ (M.nodalFunction f) x)‖^2) =
      ∫ x in M.cell i, w x*‖derivativeOneFiber (fderiv ℝ p x)‖^2 := by
    apply integral_congr_ae
    filter_upwards [M.nodalFunction_fderiv_on_cell_ae hM f i] with x hx
    rw [hx]
  change (∫ x in M.cell i, (M.nodalProductResidual w f x)^2/w x) ≤
      C*(M.cellDiameter i)^4*(q^4*(∫ x in M.cell i, w x*(M.nodalFunction f x)^2)+
        q^2*(∫ x in M.cell i, w x*‖derivativeOneFiber (fderiv ℝ (M.nodalFunction f) x)‖^2)) ∧ _
  rw [hv,hg,hs,ht]
  exact hlocal

end Carleman
