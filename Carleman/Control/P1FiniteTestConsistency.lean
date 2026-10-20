module

public import Carleman.Control.P1GalerkinTests
public import Carleman.Control.CartesianWeakLimitTests

/-! Strong consistency of actual full P1 Galerkin test sequences, including both endpoints. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} [IsFiniteMeasure (volume.restrict S)]

def p1FiniteTestSequence {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι)
    (hS : IsOpen S) (hc : Convex ℝ S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (g : TimeGrid) {L : Type*} [Fintype L] (η : L → ℝ → ℝ) (ψ : L → SpatialTest S) :
    Fin (g.steps+1) → M.conformingSpace (dirichletSubspace S) :=
  fun k => ∑ l, η l ((k.val:ℝ)*g.dt) • M.testGalerkinState hS hc hM hB (ψ l)

theorem p1FiniteTestSequence_lift {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι)
    (hS : IsOpen S) (hc : Convex ℝ S) (hd : 0 < d) (hSb : Bornology.IsBounded S)
    (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (g : TimeGrid) {L : Type*} [Fintype L] (η : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (k : Fin (g.steps+1)) :
    dirichletGalerkinState hS hd hSb (M.conformingSpace (dirichletSubspace S))
      (M.conformingSpace_le (dirichletSubspace S)) (p1FiniteTestSequence M hS hc hM hB g η ψ k)=
        ∑ l, η l ((k.val:ℝ)*g.dt) • M.testDirichletState hS hc hM hB (ψ l) :=
  M.testGalerkinState_finite_lift hS hc hd hSb hM hB ψ _

theorem p1FiniteTestSequence_value {ι : Type*} [Fintype ι] (M : SimplicialPartition S ι)
    (hS : IsOpen S) (hc : Convex ℝ S) (hM : M.FaceMatching) (hB : M.BoundaryFitted)
    (g : TimeGrid) {L : Type*} [Fintype L] (η : L → ℝ → ℝ) (ψ : L → SpatialTest S)
    (k : Fin (g.steps+1)) :
    (p1FiniteTestSequence M hS hc hM hB g η ψ k : Lp ℝ 2 (volume.restrict S))=
      ∑ l, η l ((k.val:ℝ)*g.dt) • M.nodalLp hS.measurableSet hM (ψ l).value := by
  change (M.conformingSpace (dirichletSubspace S)).subtypeL (∑ l, _)=_
  simp only [map_sum,map_smul,Submodule.subtypeL_apply,SimplicialPartition.testGalerkinState_value]

theorem full_p1_galerkin_finite_test_endpoint_consistency (hS : IsOpen S) (hc : Convex ℝ S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (M : ∀ n, SimplicialPartition S (ι n))
    (hM : ∀ n, (M n).FaceMatching) (hB : ∀ n, (M n).BoundaryFitted)
    (hlim : Tendsto (fun n => (M n).maxDiameter) atTop (𝓝 0))
    (T : ℝ) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    {L : Type*} [Fintype L] (η : L → ℝ → ℝ) (ψ : L → SpatialTest S) :
    Tendsto (fun n => (p1FiniteTestSequence (M n) hS hc (hM n) (hB n) (g n) η ψ 0 :
      Lp ℝ 2 (volume.restrict S))) atTop (𝓝 (∑ l, η l 0 • (ψ l).toLp (volume.restrict S))) ∧
    Tendsto (fun n => (p1FiniteTestSequence (M n) hS hc (hM n) (hB n) (g n) η ψ (Fin.last (g n).steps) :
      Lp ℝ 2 (volume.restrict S))) atTop (𝓝 (∑ l, η l T • (ψ l).toLp (volume.restrict S))) := by
  have hh τ := finite_tensor_test_endpoint_consistency η
    (fun l n => (M n).nodalLp hS.measurableSet (hM n) (ψ l).value)
    (fun l => (ψ l).toLp (volume.restrict S))
    (fun l => test_nodal_value_strong_convergence hS M hM hlim (ψ l)) τ
  constructor
  · simpa only [p1FiniteTestSequence_value,Fin.val_zero,Nat.cast_zero,zero_mul] using hh 0
  · have ht n : ((g n).steps:ℝ)*(g n).dt=T := hT n
    simpa only [p1FiniteTestSequence_value,Fin.val_last,ht] using hh T

theorem full_p1_galerkin_finite_time_test_consistency (hS : IsOpen S) (hc : Convex ℝ S)
    (hdim : 0 < d) (hSb : Bornology.IsBounded S)
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
    let φ := fun n => p1FiniteTestSequence (M n) hS hc (hM n) (hB n) (g n) η ψ;
    let G := fun n => (dirichletStateGradient S).comp
      (dirichletGalerkinState hS hdim hSb ((M n).conformingSpace (dirichletSubspace S))
        ((M n).conformingSpace_le (dirichletSubspace S)));
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => (φ n i.castSucc : Lp ℝ 2 (volume.restrict S))))
      atTop (𝓝 (∑ l, timeTensor T ((ψ l).toLp (volume.restrict S))
        ((continuous_time_memLp T (η l) (hη l)).toLp (η l)))) ∧
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => ((g n).dt⁻¹ • (φ n i.succ-φ n i.castSucc) : Lp ℝ 2 (volume.restrict S))))
      atTop (𝓝 (∑ l, timeTensor T ((ψ l).toLp (volume.restrict S))
        ((continuous_time_memLp T (f l) (hf l)).toLp (f l)))) ∧
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n) (fun i => G n (φ n i.castSucc)))
      atTop (𝓝 (∑ l, timeTensor T (dirichletStateGradient S (ψ l).dirichletState)
        ((continuous_time_memLp T (η l) (hη l)).toLp (η l)))) := by
  intro φ G
  have hh := full_p1_finite_time_test_consistency hS hc M hM hB hκ a r hr hball hshape hlim
    T hTpos g hT htlim η f ψ hη hf hd
  have hv := (((dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T))).continuous.tendsto _).comp hh.1
  have hdf := (((dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T))).continuous.tendsto _).comp hh.2
  have hg := (((dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T))).continuous.tendsto _).comp hh.1
  refine ⟨?_,?_,?_⟩
  · simpa only [Function.comp_def,φ,p1FiniteTestSequence_value,Fin.val_castSucc,TimeGrid.nodeTime,
      fixedTimeCellReconstruction_map,map_sum,map_smul,timeTensor_map,
      SimplicialPartition.testDirichletState_value,SpatialTest.dirichletState_value] using hv
  · simpa only [Function.comp_def,φ,p1FiniteTestSequence,Submodule.coe_smul,Submodule.coe_sub,Submodule.coe_sum,
      SimplicialPartition.testGalerkinState_value,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one,
      fixedTimeCellReconstruction_map,map_smul,map_sub,map_sum,timeTensor_map,
      SimplicialPartition.testDirichletState_value,SpatialTest.dirichletState_value] using hdf
  · simpa only [Function.comp_def,G,φ,ContinuousLinearMap.comp_apply,p1FiniteTestSequence_lift,Fin.val_castSucc,
      TimeGrid.nodeTime,fixedTimeCellReconstruction_map,map_sum,map_smul,timeTensor_map] using hg

end Carleman
