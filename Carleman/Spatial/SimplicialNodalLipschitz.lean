module

public import Carleman.Spatial.FiniteLipschitzSelection
public import Carleman.Spatial.SimplicialNodalDerivative
public import Carleman.Spatial.SimplicialNodalBoundary

/-! A genuine global Lipschitz bound for the zero extension of a boundary-zero
nodal function. The explicit constant may depend on the nodal values and
mesh; it is used for weak-derivative membership, not a uniform inverse bound. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators
namespace Carleman.SimplicialPartition
variable {d : ℕ} {ι : Type*} [Fintype ι] {S : Set (SpatialCoordinates d)}
  (M : Carleman.SimplicialPartition S ι)

def nodalLipschitzConstant (f : SpatialCoordinates d → ℝ) : ℝ≥0 :=
  ∑ i, ‖M.localNodalDerivative f i‖₊

theorem localNodal_lipschitzWith (f : SpatialCoordinates d → ℝ) (i : ι) :
    LipschitzWith (M.nodalLipschitzConstant f) (M.localNodal f i) := by
  have hi : LipschitzWith ‖M.localNodalDerivative f i‖₊ (M.localNodal f i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,dist_eq_norm]
    have he : M.localNodal f i x - M.localNodal f i y = M.localNodalDerivative f i (x-y) := by
      exact ((M.localNodal f i).linear_apply_vsub x y).symm
    rw [he]
    exact (M.localNodalDerivative f i).le_opNorm (x-y)
  apply hi.weaken
  unfold nodalLipschitzConstant
  exact Finset.single_le_sum (f := fun j => ‖M.localNodalDerivative f j‖₊) (fun _ _ => bot_le) (Finset.mem_univ i)

theorem nodalFunction_lipschitzWith (hS : IsOpen S) (hM : M.FaceMatching)
    (hB : M.BoundaryFitted) (f : SpatialCoordinates d → ℝ)
    (hf : ∀ i k, (M.simplex i).points k ∈ frontier S → f ((M.simplex i).points k) = 0) :
    LipschitzWith (M.nodalLipschitzConstant f) (M.nodalFunction f) := by
  classical
  let g : Option ι → SpatialCoordinates d → ℝ := fun o =>
    match o with | none => 0 | some i => M.localNodal f i
  apply lipschitzWith_finite_selection g (M.nodalFunction_continuous_of_boundary hS hM hB f hf)
  · intro o
    cases o with
    | none => exact (LipschitzWith.const (0 : ℝ)).weaken (bot_le)
    | some i => exact M.localNodal_lipschitzWith f i
  · intro x
    by_cases hx : ∃ i, x ∈ M.cell i
    · obtain ⟨i,hi⟩ := hx
      exact ⟨some i,M.nodalFunction_on_cell hM f i hi⟩
    · refine ⟨none,?_⟩
      exact dite_eq_right hx

end Carleman.SimplicialPartition
