module

public import Carleman.Spatial.SimplicialProductResidual

/-! Integrability of the actual global nodal residual and its classical
derivative; the mesh skeleton is handled by genuine almost-everywhere identities. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : SimplicialPartition S ι)

theorem squaredNodal_integrability (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) {ρ : SpatialCoordinates d → ℝ}
    (hρ : ContDiffOn ℝ 2 ρ (closure S)) {q : ℝ} (hq : 0 < q) (τ η : ℝ)
    (f : SpatialCoordinates d → ℝ) :
    let w := allowedSquaredWeight ρ q τ η
    let u := M.nodalFunction f
    let e := M.nodalProductResidual w f
    IntegrableOn (fun x => (e x)^2/w x) S ∧
    IntegrableOn (fun x => ‖derivativeOneFiber (fderiv ℝ e x)‖^2/w x) S ∧
    IntegrableOn (fun x => w x*(u x)^2) S ∧
    IntegrableOn (fun x => w x*‖derivativeOneFiber (fderiv ℝ u x)‖^2) S := by
  let w := allowedSquaredWeight ρ q τ η
  let u := M.nodalFunction f
  let e := M.nodalProductResidual w f
  have hwpos (x : SpatialCoordinates d) : 0 < w x := by dsimp only [w,allowedSquaredWeight]; positivity
  have hw : ContinuousOn w (closure S) := (allowedSquaredWeight_contDiffOn hρ q τ η).continuousOn
  have hu : ContinuousOn u (closure S) := M.nodalFunction_continuousOn hM f
  have he : ContinuousOn e (closure S) :=
    (hw.mul hu).sub (M.nodalFunction_continuousOn hM (fun x => w x*f x))
  have hv : IntegrableOn (fun x => (e x)^2/w x) S := by
    apply M.integrable_of_cells
    intro i
    exact (((he.pow 2).div hw (fun x _ => (hwpos x).ne')).mono (M.inside i)).integrableOn_compact
      (simplicialCell_compact _)
  have hg : IntegrableOn (fun x => ‖derivativeOneFiber (fderiv ℝ e x)‖^2/w x) S := by
    apply M.integrable_of_cells
    intro i
    let p := M.localNodal f i
    let I := simplexNodalInterpolant (M.simplex i) (fun k => w ((M.simplex i).points k)*p ((M.simplex i).points k))
    let G := affineProductDerivative w (fderivWithin ℝ w (closure S)) p
    have hW : ContinuousOn (fderivWithin ℝ w (closure S)) (M.cell i) :=
      (((allowedSquaredWeight_contDiffOn hρ q τ η).fderivWithin
        (uniqueDiffOn_closure_open_convex hS hc) (m := 1) (by norm_num)).continuousOn).mono (M.inside i)
    have hG : ContinuousOn G (M.cell i) :=
      ((hw.mono (M.inside i)).smul continuous_const.continuousOn).add
        (p.continuous_of_finiteDimensional.continuousOn.smul hW)
    have hi := (((derivativeOneFiber (d := d)).continuous.comp_continuousOn
      (hG.sub (show ContinuousOn (fun _ => affineScalarDerivative I) (M.cell i) from
        continuous_const.continuousOn))).norm.pow 2).div
      (hw.mono (M.inside i)) (fun x _ => (hwpos x).ne')
    apply (hi.integrableOn_compact (simplicialCell_compact _)).congr_fun_ae
    filter_upwards [M.nodalProductResidual_fderiv_ae hM w f i,
      squaredNodalResidual_fderiv_ae hρ (M.simplex i) (M.inside i) q τ η p] with x hx hy
    change ‖derivativeOneFiber (G x-affineScalarDerivative I)‖^2/w x =
      ‖derivativeOneFiber (fderiv ℝ e x)‖^2/w x
    rw [hx,hy]
  have hs : IntegrableOn (fun x => w x*(u x)^2) S := by
    apply M.integrable_of_cells
    intro i
    exact ((hw.mul (hu.pow 2)).mono (M.inside i)).integrableOn_compact (simplicialCell_compact _)
  have ht : IntegrableOn (fun x => w x*‖derivativeOneFiber (fderiv ℝ u x)‖^2) S := by
    apply M.integrable_of_cells
    intro i
    have hi : ContinuousOn (fun x => w x*‖derivativeOneFiber (affineScalarDerivative (M.localNodal f i))‖^2)
        (M.cell i) := (hw.mono (M.inside i)).mul continuous_const.continuousOn
    apply (hi.integrableOn_compact (simplicialCell_compact _)).congr_fun_ae
    filter_upwards [M.nodalFunction_fderiv_on_cell_ae hM f i] with x hx
    rw [hx,(affineScalar_hasFDerivAt (M.localNodal f i) x).fderiv]
  exact ⟨hv,hg,hs,ht⟩

end Carleman.SimplicialPartition
