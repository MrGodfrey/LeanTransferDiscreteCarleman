module

public import Carleman.Spatial.SimplicialNodalOperator
public import Mathlib.Analysis.Calculus.FDeriv.Affine

/-! The actual classical derivative off the mesh skeleton. Its L² existence
is proved, but the distributional identity is a separate obligation. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def localNodalDerivative (f : SpatialCoordinates d → ℝ) (i : ι) :
    SpatialCoordinates d →L[ℝ] ℝ :=
  (⟨M.localNodal f i,(M.localNodal f i).continuous_of_finiteDimensional⟩ :
    SpatialCoordinates d →ᴬ[ℝ] ℝ).contLinear

theorem localNodalDerivative_apply (f : SpatialCoordinates d → ℝ) (i : ι)
    (e : SpatialCoordinates d) :
    M.localNodalDerivative f i e = (M.localNodal f i).linear e := rfl

theorem localNodal_hasFDerivAt (f : SpatialCoordinates d → ℝ) (i : ι)
    (x : SpatialCoordinates d) :
    HasFDerivAt (M.localNodal f i) (M.localNodalDerivative f i) x :=
  (⟨M.localNodal f i,(M.localNodal f i).continuous_of_finiteDimensional⟩ :
    SpatialCoordinates d →ᴬ[ℝ] ℝ).hasFDerivAt

theorem nodalFunction_hasFDerivAt_on_interior (hM : M.FaceMatching)
    (f : SpatialCoordinates d → ℝ) (i : ι) {x : SpatialCoordinates d}
    (hx : x ∈ interior (M.cell i)) :
    HasFDerivAt (M.nodalFunction f) (M.localNodalDerivative f i) x := by
  apply (M.localNodal_hasFDerivAt f i x).congr_of_eventuallyEq
  filter_upwards [mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset] with y hy
  exact M.nodalFunction_on_cell hM f i hy

variable [Fintype ι]

theorem ae_mem_cell_interior (hS : MeasurableSet S) :
    ∀ᵐ x ∂(volume.restrict S), ∃ i, x ∈ interior (M.cell i) := by
  have hn (i : ι) : ∀ᵐ x ∂(volume.restrict S), x ∉ frontier (M.cell i) := by
    apply ae_restrict_of_ae
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using simplicialCell_frontier_null (M.simplex i).points
  filter_upwards [M.ae_partition hS,ae_all_iff.mpr hn] with x hx hfront
  obtain ⟨i,hi,_⟩ := hx
  exact ⟨i,(mem_interior_iff_notMem_frontier hi).mpr (hfront i)⟩

/-- The open cells are disjoint, so this is the local derivative on each
interior, with a chosen zero value on the skeleton and outside the cover. -/
def nodalDerivativeFunction (f : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) :
    SpatialCoordinates d →L[ℝ] ℝ :=
  ∑ i, (interior (M.cell i)).indicator (fun _ => M.localNodalDerivative f i) x

theorem nodalDerivativeFunction_on_interior (f : SpatialCoordinates d → ℝ) (i : ι)
    {x : SpatialCoordinates d} (hx : x ∈ interior (M.cell i)) :
    M.nodalDerivativeFunction f x = M.localNodalDerivative f i := by
  classical
  rw [nodalDerivativeFunction,Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    exact Set.disjoint_left.mp (M.disjoint hji) hj hx
  · simp

theorem nodalFunction_hasFDerivAt_ae (hS : MeasurableSet S) (hM : M.FaceMatching)
    (f : SpatialCoordinates d → ℝ) :
    ∀ᵐ x ∂(volume.restrict S), HasFDerivAt (M.nodalFunction f) (M.nodalDerivativeFunction f x) x := by
  filter_upwards [M.ae_mem_cell_interior hS] with x hx
  obtain ⟨i,hi⟩ := hx
  rw [M.nodalDerivativeFunction_on_interior f i hi]
  exact M.nodalFunction_hasFDerivAt_on_interior hM f i hi

variable [IsFiniteMeasure (volume.restrict S)]

theorem nodalDerivativeFunction_memLp (f : SpatialCoordinates d → ℝ) :
    MemLp (M.nodalDerivativeFunction f) 2 (volume.restrict S) :=
  by
    unfold nodalDerivativeFunction
    apply memLp_finsetSum (f := fun i => (interior (M.cell i)).indicator (fun _ => M.localNodalDerivative f i)) Finset.univ
    intro i _
    exact (memLp_const (μ := volume.restrict S) (p := 2) (M.localNodalDerivative f i)).indicator
      (s := interior (M.cell i)) isOpen_interior.measurableSet.nullMeasurableSet

def nodalDerivativeLp (f : SpatialCoordinates d → ℝ) :
    Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 (volume.restrict S) :=
  (M.nodalDerivativeFunction_memLp f).toLp (M.nodalDerivativeFunction f)

theorem nodalDerivativeLp_ae (f : SpatialCoordinates d → ℝ) :
    M.nodalDerivativeLp f =ᵐ[volume.restrict S] M.nodalDerivativeFunction f := MemLp.coeFn_toLp _

theorem nodalFunction_fderiv_memLp (hS : MeasurableSet S) (hM : M.FaceMatching)
    (f : SpatialCoordinates d → ℝ) :
    MemLp (fderiv ℝ (M.nodalFunction f)) 2 (volume.restrict S) := by
  refine MemLp.ae_eq ?_ (M.nodalDerivativeFunction_memLp f)
  filter_upwards [M.nodalFunction_hasFDerivAt_ae hS hM f] with x hx
  exact hx.fderiv.symm

end Carleman.SimplicialPartition
