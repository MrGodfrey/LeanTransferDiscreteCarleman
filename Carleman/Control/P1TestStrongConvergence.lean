module

public import Carleman.Control.P1TestInterpolation

/-! Strong H¹₀ convergence of the actual full P1 nodal interpolants on uniformly shape-regular meshes. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict S)]
theorem test_nodal_value_strong_convergence (hS : IsOpen S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (M : ∀ n, SimplicialPartition S (ι n))
    (hM : ∀ n, (M n).FaceMatching)
    (hlim : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0)) (φ : SpatialTest S) :
    Tendsto (fun n => (M n).nodalLp hS.measurableSet (hM n) φ.value) atTop
      (𝓝 (φ.toLp (volume.restrict S))) := by
  obtain ⟨C,hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.compact φ.smooth (by simp)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (norm_sub_rev _ _).trans_le ((M n).test_nodal_L2_error hS (hM n) φ hC))
  simpa only [mul_zero] using tendsto_const_nhds.mul ((tendsto_const_nhds (x := 2*(C:ℝ))).mul hlim)

theorem test_nodal_derivative_strong_convergence (hS : IsOpen S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (M : ∀ n, SimplicialPartition S (ι n))
    {κ : ℝ} (hκ : 0 ≤ κ) (a : ∀ n, ι n → SpatialCoordinates d) (r : ∀ n, ι n → ℝ)
    (hr : ∀ n i, 0 < r n i) (hball : ∀ n i, Metric.ball (a n i) (r n i) ⊆ (M n).cell i)
    (hshape : ∀ n i, (M n).cellDiameter i ≤ κ*r n i)
    (hlim : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0)) (φ : SpatialTest S) :
    Tendsto (fun n => (M n).nodalDerivativeLp φ.value) atTop (𝓝 φ.fderivLp) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ φ.value) := φ.smooth.fderiv_right (by simp)
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (φ.compact.fderiv ℝ) hdf (by simp)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (norm_sub_rev _ _).trans_le ((M n).test_nodal_derivative_L2_error hS φ hL
      hκ (a n) (r n) (hr n) (hball n) (hshape n)))
  simpa only [mul_zero] using tendsto_const_nhds.mul
    ((tendsto_const_nhds (x := (1+4*κ)*(L:ℝ))).mul hlim)

omit [IsFiniteMeasure (volume.restrict S)] in
theorem dirichletEnergyState_tendsto_of_fields (u : ℕ → DirichletEnergyState S)
    (u₀ : DirichletEnergyState S)
    (hv : Tendsto (fun n => dirichletStateValue S (u n)) atTop (𝓝 (dirichletStateValue S u₀)))
    (hg : Tendsto (fun n => dirichletStateGradient S (u n)) atTop (𝓝 (dirichletStateGradient S u₀))) :
    Tendsto u atTop (𝓝 u₀) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he n := dirichletEnergyState_norm_sq (u n-u₀)
  simp only [map_sub] at he
  have hb n : ‖u n-u₀‖ ≤
      ‖dirichletStateValue S (u n)-dirichletStateValue S u₀‖+
      ‖dirichletStateGradient S (u n)-dirichletStateGradient S u₀‖ := by
    have hn := norm_nonneg (u n-u₀)
    have ha := norm_nonneg (dirichletStateValue S (u n)-dirichletStateValue S u₀)
    have hb := norm_nonneg (dirichletStateGradient S (u n)-dirichletStateGradient S u₀)
    have hm := mul_nonneg ha hb
    nlinarith [he n]
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa only [add_zero] using (tendsto_iff_norm_sub_tendsto_zero.mp hv).add
    (tendsto_iff_norm_sub_tendsto_zero.mp hg)

theorem full_p1_test_H1_strong_convergence (hS : IsOpen S) (hc : Convex ℝ S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (M : ∀ n, SimplicialPartition S (ι n))
    (hM : ∀ n, (M n).FaceMatching) (hB : ∀ n, (M n).BoundaryFitted)
    {κ : ℝ} (hκ : 0 ≤ κ) (a : ∀ n, ι n → SpatialCoordinates d) (r : ∀ n, ι n → ℝ)
    (hr : ∀ n i, 0 < r n i) (hball : ∀ n i, Metric.ball (a n i) (r n i) ⊆ (M n).cell i)
    (hshape : ∀ n i, (M n).cellDiameter i ≤ κ*r n i)
    (hlim : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0)) (φ : SpatialTest S) :
    Tendsto (fun n => (M n).testDirichletState hS hc (hM n) (hB n) φ)
      atTop (𝓝 φ.dirichletState) := by
  apply dirichletEnergyState_tendsto_of_fields
  · simp only [SimplicialPartition.testDirichletState_value,SpatialTest.dirichletState_value]
    exact test_nodal_value_strong_convergence hS M hM hlim φ
  · simp only [SimplicialPartition.testDirichletState_gradient,SpatialTest.dirichletState_gradient]
    exact (((OperatorMultiplier.const (ν := volume.restrict S) (derivativeOneFiber (d := d))).continuousLinearMap).continuous.tendsto _).comp
      (test_nodal_derivative_strong_convergence hS M hκ a r hr hball hshape hlim φ)

end Carleman
