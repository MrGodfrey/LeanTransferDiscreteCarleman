module

public import Carleman.Spatial.SimplicialNodalSobolev

/-! Classical derivatives and L² fields for the actual global zero extension.
The same local affine derivatives are used; no extension is postulated. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

theorem nodalDerivativeFunction_zero_outside (f : SpatialCoordinates d → ℝ)
    {x : SpatialCoordinates d} (hx : x ∉ closure S) : M.nodalDerivativeFunction f x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact indicator_of_notMem (fun hh => hx (M.inside i (interior_subset hh))) _

theorem nodalFunction_hasFDerivAt_global_ae (hM : M.FaceMatching)
    (f : SpatialCoordinates d → ℝ) :
    ∀ᵐ x ∂volume, HasFDerivAt (M.nodalFunction f) (M.nodalDerivativeFunction f x) x := by
  have hn (i : ι) : ∀ᵐ x ∂volume, x ∉ frontier (M.cell i) := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using simplicialCell_frontier_null (M.simplex i).points
  filter_upwards [ae_all_iff.mpr hn] with x hfront
  by_cases hc : x ∈ closure S
  · rw [← M.cells_union] at hc
    obtain ⟨i,hi⟩ := mem_iUnion.mp hc
    have hint := (mem_interior_iff_notMem_frontier hi).mpr (hfront i)
    rw [M.nodalDerivativeFunction_on_interior f i hint]
    exact M.nodalFunction_hasFDerivAt_on_interior hM f i hint
  · rw [M.nodalDerivativeFunction_zero_outside f hc]
    apply (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
    exact M.nodalFunction_zero_outside f hy

theorem nodalDerivativeFunction_global_memLp (f : SpatialCoordinates d → ℝ) :
    MemLp (M.nodalDerivativeFunction f) 2 volume := by
  unfold nodalDerivativeFunction
  apply memLp_finsetSum (f := fun i => (interior (M.cell i)).indicator (fun _ => M.localNodalDerivative f i)) Finset.univ
  intro i _
  apply memLp_indicator_const _ isOpen_interior.measurableSet.nullMeasurableSet _
  right
  exact (measure_mono interior_subset |>.trans_lt (simplicialCell_compact (M.simplex i).points).measure_lt_top).ne

def nodalGlobalDerivativeLp (f : SpatialCoordinates d → ℝ) :
    Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 (volume : Measure (SpatialCoordinates d)) :=
  (M.nodalDerivativeFunction_global_memLp f).toLp (M.nodalDerivativeFunction f)

theorem nodalGlobalDerivativeLp_ae (f : SpatialCoordinates d → ℝ) :
    M.nodalGlobalDerivativeLp f =ᵐ[volume] M.nodalDerivativeFunction f := MemLp.coeFn_toLp _

theorem nodalFunction_global_memLp (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    MemLp (M.nodalFunction f) 2 volume :=
  (M.nodalFunction_continuous_of_boundary hS hM hB f hf).memLp_of_hasCompactSupport
    (M.nodalFunction_hasCompactSupport f)

def nodalGlobalLp (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) :=
  (M.nodalFunction_global_memLp hS hM hB f hf).toLp (M.nodalFunction f)

theorem nodalGlobalLp_ae (hS : IsOpen S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    M.nodalGlobalLp hS hM hB f hf =ᵐ[volume] M.nodalFunction f := MemLp.coeFn_toLp _

end Carleman.SimplicialPartition
