module

public import Carleman.Spatial.P1InitialDataApproximation
public import Carleman.Spatial.SimplexTaylorInterpolation
public import Carleman.Control.DirichletTimeWeakCompactness

/-! The original smooth test and its actual nodal interpolant in H¹₀, with a derivative error bound. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict S)]
namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι)

omit [IsFiniteMeasure (volume.restrict S)] in
theorem nodal_lipschitz_derivative_error (f : SpatialCoordinates d → ℝ)
    (hf : Differentiable ℝ f) {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f))
    {κ : ℝ} (hκ : 0 ≤ κ) (a : ι → SpatialCoordinates d) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hball : ∀ i, Metric.ball (a i) (r i) ⊆ M.cell i)
    (hshape : ∀ i, M.cellDiameter i ≤ κ*r i)
    (i : ι) {x : SpatialCoordinates d} (hx : x ∈ M.cell i) :
    ‖fderiv ℝ f x-M.localNodalDerivative f i‖ ≤ (1+4*κ)*L*M.maxDiameter := by
  have hh := simplexNodal_gradient_error_of_lipschitz_derivative (M.simplex i) f
    (fun x _ => hf x) L hL.lipschitzOnWith (hr i) (M.cellDiameter_nonneg i)
      (hball i) (hshape i) (fun _ hx _ hy => M.dist_le_cellDiameter i hx hy) hx
  change ‖fderiv ℝ f x-M.localNodalDerivative f i‖ ≤ (1+4*κ)*L*M.cellDiameter i at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (M.cellDiameter_le_max i) (by positivity))

theorem test_nodal_derivative_L2_error (hS : IsOpen S)
    (φ : SpatialTest S) {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ φ.value))
    {κ : ℝ} (hκ : 0 ≤ κ) (a : ι → SpatialCoordinates d) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hball : ∀ i, Metric.ball (a i) (r i) ⊆ M.cell i)
    (hshape : ∀ i, M.cellDiameter i ≤ κ*r i) :
    ‖φ.fderivLp-M.nodalDerivativeLp φ.value‖ ≤
      (measureUnivNNReal (volume.restrict S) : ℝ)^((2:ENNReal).toReal⁻¹)*
        ((1+4*κ)*L*M.maxDiameter) := by
  apply Lp.norm_le_of_ae_bound (by positivity [M.maxDiameter_nonneg])
  filter_upwards [φ.fderivLp_ae,M.nodalDerivativeLp_ae φ.value,
    Lp.coeFn_sub φ.fderivLp (M.nodalDerivativeLp φ.value),M.ae_mem_cell_interior hS.measurableSet]
    with x hφx hIx hsub hx
  rw [hsub,Pi.sub_apply,hφx,hIx]
  obtain ⟨i,hi⟩ := hx
  rw [M.nodalDerivativeFunction_on_interior φ.value i hi]
  exact M.nodal_lipschitz_derivative_error φ.value (φ.smooth.differentiable (by simp))
    hL hκ a r hr hball hshape i (interior_subset hi)

omit [IsFiniteMeasure (volume.restrict S)] [Fintype ι] in
theorem test_nodal_zero_boundary (hS : IsOpen S) (φ : SpatialTest S) :
    ∀ i k, (M.simplex i).points k ∈ frontier S → φ.value ((M.simplex i).points k)=0 := by
  intro i k hk
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  exact hk.2 (hS.interior_eq.symm ▸ φ.support hx)

def testDirichletState (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted) (φ : SpatialTest S) : DirichletEnergyState S :=
  ⟨SobolevHilbert.ofJet (M.nodalSobolevJet hS hM hB φ.value (M.test_nodal_zero_boundary hS φ)), by
    change WeakSobolevJet.value (M.nodalSobolevJet hS hM hB φ.value (M.test_nodal_zero_boundary hS φ)) ∈ dirichletSubspace S
    rw [M.nodalSobolevJet_value]
    exact M.nodalLp_mem_dirichletSubspace hS hc hM hB φ.value (M.test_nodal_zero_boundary hS φ)⟩

theorem testDirichletState_value (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted) (φ : SpatialTest S) :
    dirichletStateValue S (M.testDirichletState hS hc hM hB φ)=M.nodalLp hS.measurableSet hM φ.value :=
  M.nodalSobolevJet_value hS hM hB φ.value (M.test_nodal_zero_boundary hS φ)

theorem testDirichletState_gradient (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted) (φ : SpatialTest S) :
    dirichletStateGradient S (M.testDirichletState hS hc hM hB φ)=
      (OperatorMultiplier.const derivativeOneFiber).map (M.nodalDerivativeLp φ.value) := rfl

end SimplicialPartition

namespace SpatialTest

def dirichletState (φ : SpatialTest S) : DirichletEnergyState S :=
  ⟨SobolevHilbert.ofJet φ.sobolevJet,by
    change WeakSobolevJet.value φ.sobolevJet ∈ dirichletSubspace S
    rw [φ.sobolevJet_value]
    exact test_mem_dirichletSubspace S φ⟩

omit [IsFiniteMeasure (volume.restrict S)] in
theorem dirichletState_value (φ : SpatialTest S) :
    dirichletStateValue S φ.dirichletState=φ.toLp (volume.restrict S) := φ.sobolevJet_value

omit [IsFiniteMeasure (volume.restrict S)] in
theorem dirichletState_gradient (φ : SpatialTest S) :
    dirichletStateGradient S φ.dirichletState=(OperatorMultiplier.const derivativeOneFiber).map φ.fderivLp := rfl

end SpatialTest

end Carleman
