module

public import Carleman.Spatial.SimplicialIntegrals
public import Carleman.Spatial.SimplicialNodalDerivative
public import Carleman.Weights.SquaredCellGradient

/-! The actual global nodal product residual restricts to the local residual,
including the true derivative almost everywhere off the mesh skeleton. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} {S : Set (SpatialCoordinates d)} (M : SimplicialPartition S ι)

theorem integrable_of_cells [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    (f : SpatialCoordinates d → F) (hf : ∀ i, IntegrableOn f (M.cell i)) :
    IntegrableOn f S :=
  (integrableOn_finite_iUnion.mpr hf).mono_set M.cover

def nodalProductResidual (w f : SpatialCoordinates d → ℝ) : SpatialCoordinates d → ℝ :=
  fun x => w x*M.nodalFunction f x-M.nodalFunction (fun y => w y*f y) x

theorem localNodal_weighted_interpolant (w f : SpatialCoordinates d → ℝ) (i : ι) :
    simplexNodalInterpolant (M.simplex i)
      (fun k => w ((M.simplex i).points k)*M.localNodal f i ((M.simplex i).points k)) =
      M.localNodal (fun y => w y*f y) i := by
  simp only [M.localNodal_vertex]
  rfl

theorem nodalProductResidual_on_cell (hM : M.FaceMatching)
    (w f : SpatialCoordinates d → ℝ) (i : ι) {x : SpatialCoordinates d} (hx : x ∈ M.cell i) :
    M.nodalProductResidual w f x = w x*M.localNodal f i x-
      simplexNodalInterpolant (M.simplex i)
        (fun k => w ((M.simplex i).points k)*M.localNodal f i ((M.simplex i).points k)) x := by
  rw [nodalProductResidual,M.nodalFunction_on_cell hM f i hx,
    M.nodalFunction_on_cell hM (fun y => w y*f y) i hx,M.localNodal_weighted_interpolant]

theorem nodalProductResidual_fderiv_ae (hM : M.FaceMatching)
    (w f : SpatialCoordinates d → ℝ) (i : ι) :
    ∀ᵐ x ∂volume.restrict (M.cell i),
      fderiv ℝ (M.nodalProductResidual w f) x =
      fderiv ℝ (fun y => w y*M.localNodal f i y-
        simplexNodalInterpolant (M.simplex i)
          (fun k => w ((M.simplex i).points k)*M.localNodal f i ((M.simplex i).points k)) y) x := by
  rw [Measure.restrict_congr_set (simplexCell_ae_interior (M.simplex i))]
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with x hx
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset] with y hy
  exact M.nodalProductResidual_on_cell hM w f i hy

theorem nodalFunction_fderiv_on_cell_ae (hM : M.FaceMatching)
    (f : SpatialCoordinates d → ℝ) (i : ι) :
    ∀ᵐ x ∂volume.restrict (M.cell i),
      fderiv ℝ (M.nodalFunction f) x = fderiv ℝ (M.localNodal f i) x := by
  rw [Measure.restrict_congr_set (simplexCell_ae_interior (M.simplex i))]
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with x hx
  rw [(M.nodalFunction_hasFDerivAt_on_interior hM f i hx).fderiv,
    (M.localNodal_hasFDerivAt f i x).fderiv]

end Carleman.SimplicialPartition
