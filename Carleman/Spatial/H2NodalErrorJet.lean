module

public import Carleman.Spatial.DirichletContinuousBoundary
public import Carleman.Spatial.WeakH2NodalGradient
public import Carleman.Spatial.NodalDirichletMembership
public import Carleman.Spatial.SimplicialNodalSobolev
public import Carleman.Spatial.SimplicialLocalGradient
public import Carleman.Spatial.SobolevTruncation

/-! The actual H¹ nodal error of every original weak H² state with a
boundary-zero continuous representative. Local fields are identified with
the same pointwise nodal polynomials used in the analytic estimates. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι) [IsFiniteMeasure (volume.restrict S)]

theorem nodalSobolevJet_mem_dirichlet (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) :
    M.nodalSobolevJet hS hM hB f hf ∈ dirichletJetSpace S := by
  apply (mem_dirichletJetSpace_iff S hS _).mpr
  rw [M.nodalSobolevJet_value]
  exact M.nodalLp_mem_dirichletSubspace hS hc hM hB f hf

def nodalH2ErrorJet (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) :
    WeakSobolevJet d 1 (volume.restrict S) S :=
  WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-M.nodalSobolevJet hS hM hB f hf

theorem nodalH2ErrorJet_value (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) :
    WeakSobolevJet.value (M.nodalH2ErrorJet hS hM hB u f hf)=
      WeakSobolevJet.value u-M.nodalLp hS.measurableSet hM f := by
  rw [nodalH2ErrorJet,map_sub,WeakSobolevJet.truncate_value,M.nodalSobolevJet_value]

theorem nodalH2ErrorJet_mem_dirichlet (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (hu : WeakSobolevJet.value u ∈ dirichletSubspace S) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) :
    M.nodalH2ErrorJet hS hM hB u f hf ∈ dirichletJetSpace S := by
  apply (dirichletJetSpace S).sub_mem _ (M.nodalSobolevJet_mem_dirichlet hS hc hM hB f hf)
  apply (mem_dirichletJetSpace_iff S hS _).mpr
  rw [WeakSobolevJet.truncate_value]
  exact hu

theorem nodalH2ErrorJet_value_on_cell (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0)
    (hfu : f =ᵐ[volume.restrict S] WeakSobolevJet.value u) (i : ι) :
    WeakSobolevJet.value (M.nodalH2ErrorJet hS hM hB u f hf) =ᵐ[volume.restrict (M.cell i)]
      (fun x => f x-M.localNodal f i x) := by
  rw [M.nodalH2ErrorJet_value]
  filter_upwards [(Lp.coeFn_sub (WeakSobolevJet.value u) (M.nodalLp hS.measurableSet hM f)).filter_mono
      (ae_mono (M.cell_measure_le_domain hS hc i)),
    hfu.filter_mono (ae_mono (M.cell_measure_le_domain hS hc i)),
    (M.nodalLp_ae hS.measurableSet hM f).filter_mono (ae_mono (M.cell_measure_le_domain hS hc i)),
    ae_restrict_mem (simplicialCell_measurable (M.simplex i).points)] with x he hu hI hx
  rw [he,Pi.sub_apply,← hu,hI,M.nodalFunction_on_cell hM f i hx]

theorem nodalH2ErrorJet_gradient_on_cell (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (u : WeakSobolevJet d 2 (volume.restrict S) S) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k)=0) (i : ι) :
    WeakSobolevJet.field 1 (M.nodalH2ErrorJet hS hM hB u f hf) =ᵐ[volume.restrict (M.cell i)]
      (fun x => WeakSobolevJet.field ⟨1,by omega⟩ u x-
        derivativeOneFiber (affineScalarDerivative (M.localNodal f i))) := by
  have hn := M.gradient_on_cell hS hc (M.nodalSobolevJet hS hM hB f hf) i (M.localNodal f i) (by
    rw [M.nodalSobolevJet_value]
    filter_upwards [M.nodalLp_ae hS.measurableSet hM f] with x hx
    intro hi
    exact hx.trans (M.nodalFunction_on_cell hM f i hi))
  change (WeakSobolevJet.field 1 (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
    M.nodalSobolevJet hS hM hB f hf)) =ᵐ[volume.restrict (M.cell i)] _
  rw [map_sub]
  filter_upwards [(Lp.coeFn_sub (WeakSobolevJet.field 1 (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u))
      (WeakSobolevJet.field 1 (M.nodalSobolevJet hS hM hB f hf))).filter_mono
        (ae_mono (M.cell_measure_le_domain hS hc i)),hn] with x he hi
  rw [he,Pi.sub_apply,hi,(affineScalar_hasFDerivAt (M.localNodal f i) x).fderiv]
  rfl

end Carleman.SimplicialPartition
