module

public import Carleman.Control.P1TestStrongConvergence
public import Carleman.Control.TensorTimeTests

/-! The original finite P1 tensor tests: joint time-space strong consistency and fixed endpoints. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict S)]
namespace SimplicialPartition
variable {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι)

theorem testDirichletState_finite_value (hS : IsOpen S) (hc : Convex ℝ S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted) {L : Type*} [Fintype L]
    (ψ : L → SpatialTest S) (c : L → ℝ) :
    dirichletStateValue S (∑ l, c l • M.testDirichletState hS hc hM hB (ψ l))=
      M.nodalLp hS.measurableSet hM (fun x => ∑ l, c l*(ψ l).value x) := by
  calc
    _ = ∑ l, c l • M.nodalLp hS.measurableSet hM (ψ l).value := by
      simp only [map_sum,map_smul,testDirichletState_value]
    _ = M.nodalLpLinearMap hS.measurableSet hM (∑ l, c l • (ψ l).value) := by
      simp only [map_sum,map_smul]
      rfl
    _ = _ := by
      change M.nodalLp hS.measurableSet hM (∑ l, c l • (ψ l).value)=_
      congr 1
      funext x
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

end SimplicialPartition

theorem full_p1_finite_time_test_consistency (hS : IsOpen S) (hc : Convex ℝ S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (M : ∀ n, SimplicialPartition S (ι n))
    (hM : ∀ n, (M n).FaceMatching) (hB : ∀ n, (M n).BoundaryFitted)
    {κ : ℝ} (hκ : 0 ≤ κ) (a : ∀ n, ι n → SpatialCoordinates d) (r : ∀ n, ι n → ℝ)
    (hr : ∀ n i, 0 < r n i) (hball : ∀ n i, Metric.ball (a n i) (r n i) ⊆ (M n).cell i)
    (hshape : ∀ n i, (M n).cellDiameter i ≤ κ*r n i)
    (hlim : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0))
    (T : ℝ) (hTpos : 0 ≤ T) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    {L : Type*} [Fintype L] (η f : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T)) (hf : ∀ l, ContinuousOn (f l) (Icc 0 T))
    (hd : ∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) :
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => ∑ l, η l ((g n).nodeTime i) • (M n).testDirichletState hS hc (hM n) (hB n) (ψ l)))
      atTop (𝓝 (∑ l, timeTensor T (ψ l).dirichletState ((continuous_time_memLp T (η l) (hη l)).toLp (η l)))) ∧
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => (g n).dt⁻¹ • ((∑ l, η l (((i.val:ℝ)+1)*(g n).dt) • (M n).testDirichletState hS hc (hM n) (hB n) (ψ l))-
        ∑ l, η l ((i.val:ℝ)*(g n).dt) • (M n).testDirichletState hS hc (hM n) (hB n) (ψ l))))
      atTop (𝓝 (∑ l, timeTensor T (ψ l).dirichletState ((continuous_time_memLp T (f l) (hf l)).toLp (f l)))) := by
  exact finite_tensor_time_test_consistency T hTpos g hT htlim η f hη hf hd
    (fun l n => (M n).testDirichletState hS hc (hM n) (hB n) (ψ l)) (fun l => (ψ l).dirichletState)
    (fun l => full_p1_test_H1_strong_convergence hS hc M hM hB hκ a r hr hball hshape hlim (ψ l))

theorem full_p1_finite_test_endpoint_consistency (hS : IsOpen S) (hc : Convex ℝ S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (M : ∀ n, SimplicialPartition S (ι n))
    (hM : ∀ n, (M n).FaceMatching) (hB : ∀ n, (M n).BoundaryFitted)
    {κ : ℝ} (hκ : 0 ≤ κ) (a : ∀ n, ι n → SpatialCoordinates d) (r : ∀ n, ι n → ℝ)
    (hr : ∀ n i, 0 < r n i) (hball : ∀ n i, Metric.ball (a n i) (r n i) ⊆ (M n).cell i)
    (hshape : ∀ n i, (M n).cellDiameter i ≤ κ*r n i)
    (hlim : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0))
    {L : Type*} [Fintype L] (η : L → ℝ → ℝ) (ψ : L → SpatialTest S) (τ : ℝ) :
    Tendsto (fun n => ∑ l, η l τ • (M n).testDirichletState hS hc (hM n) (hB n) (ψ l))
      atTop (𝓝 (∑ l, η l τ • (ψ l).dirichletState)) := by
  exact finite_tensor_test_endpoint_consistency η
    (fun l n => (M n).testDirichletState hS hc (hM n) (hB n) (ψ l)) (fun l => (ψ l).dirichletState)
    (fun l => full_p1_test_H1_strong_convergence hS hc M hM hB hκ a r hr hball hshape hlim (ψ l)) τ

end Carleman
