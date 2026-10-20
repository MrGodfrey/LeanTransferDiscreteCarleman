module

public import Carleman.Control.P1WeakLimitIdentity
public import Carleman.Control.RegionalTimeControl
public import Carleman.Control.ConformingStateWeakCompactness
public import Carleman.Control.DirichletNullControlState

/-! Every given weak P1 control limit has the original energy state and continuous null trace. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} [IsFiniteMeasure (volume.restrict S)]

theorem full_p1_weak_control_limit_null_state (hS : IsOpen S) (hc : Convex ℝ S)
    (hdim : 0 < d) (hSb : Bornology.IsBounded S)
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] (mesh : ∀ n, SimplicialPartition S (ι n))
    (hmesh : ∀ n, (mesh n).FaceMatching) (hboundary : ∀ n, (mesh n).BoundaryFitted)
    {κ : ℝ} (hκ : 0 ≤ κ) (a : ∀ n, ι n → SpatialCoordinates d) (r : ∀ n, ι n → ℝ)
    (hr : ∀ n i, 0 < r n i) (hball : ∀ n i, Metric.ball (a n i) (r n i) ⊆ (mesh n).cell i)
    (hshape : ∀ n i, (mesh n).cellDiameter i ≤ κ*r n i)
    (hlim : Tendsto (fun n => (mesh n).maxDiameter) atTop (𝓝 0))
    (T M CU : ℝ) (hM : 0 ≤ M) (hCU : 0 ≤ CU) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (hsmall : ∀ n, (g n).dt*M ≤ 1/2)
    (ω : Set (SpatialCoordinates d)) (hω : MeasurableSet ω)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (hb : b.bound ≤ M)
    (u : ∀ n, Fin (g n).steps → Lp ℝ 2 ((volume.restrict S).restrict ω))
    (y : ∀ n, Fin ((g n).steps+1) → (mesh n).conformingSpace (dirichletSubspace S))
    (hy : ∀ n, Physical.ForwardEquation (g n).dt
      (fun i => Physical.galerkinStiffness (boundedDirichletOriginalForm hS hdim hSb)
        ((mesh n).conformingSpace (dirichletSubspace S)) ((mesh n).conformingSpace_le (dirichletSubspace S))+
        Physical.conformingPotential ((mesh n).conformingSpace (dirichletSubspace S))
          (fixedTimeCellPotential T (g n) (hT n) b i))
      (Physical.conformingRegionControl ((mesh n).conformingSpace (dirichletSubspace S)) ω) (u n) (y n))
    (y0 : Lp ℝ 2 (volume.restrict S))
    (hy0 : ∀ n, y n 0=((mesh n).conformingSpace (dirichletSubspace S)).orthogonalProjectionOnto y0)
    (hu : ∀ n, Physical.controlNorm (g n).dt (u n) ≤ CU)
    (hyN : Tendsto (fun n => ‖y n (Fin.last (g n).steps)‖) atTop (𝓝 0))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T)))
    (hU : ∀ w, Tendsto (fun n => inner ℝ (fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => (Physical.restrictRegionCLM (ν := volume.restrict S) ω).adjoint (u n i))) w)
        atTop (𝓝 (inner ℝ U w))) :
    ∃ Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)),
      ‖Y‖ ≤ stateTimeEnergyBound T M ‖y0‖ CU ∧
      FiniteDirichletControlIdentity T S b y0 Y U ∧ DirichletNullControlState T S hS b y0 Y U := by
  let X n := (mesh n).conformingSpace (dirichletSubspace S)
  let hX n := (mesh n).conformingSpace_le (dirichletSubspace S)
  let R n := dirichletGalerkinState hS hdim hSb (X n) (hX n)
  let bg n := fixedTimeCellPotential T (g n) (hT n) b
  have hbg n i : (bg n i).bound ≤ M := by
    simpa only [bg,fixedTimeCellPotential_bound] using hb
  have hy0n n : ‖y n 0‖ ≤ ‖y0‖ := by
    rw [hy0]
    exact (X n).norm_orthogonalProjectionOnto_apply_le y0
  let z n := fixedTimeCellReconstruction T (g n) (hT n) (fun i => R n (y n i.succ))
  have hz n : ‖z n‖ ≤ stateTimeEnergyBound T M ‖y0‖ CU :=
    conforming_state_dirichlet_time_uniform hS hdim hSb (X n) (hX n) T M ‖y0‖ CU hM (norm_nonneg _) hCU
      (g n) (hT n) ω hω (bg n) (hbg n) (hsmall n) (u n) (y n) (hy n) (hy0n n) (hu n)
  obtain ⟨Y,hY,χ,hχ,hw,hwv,hwg⟩ := conforming_controlled_states_weak_subsequence hS hdim hSb X hX
    T M ‖y0‖ CU hM (norm_nonneg _) hCU g hT ω hω bg hbg hsmall u y hy hy0n hu
  have hid : FiniteDirichletControlIdentity T S b y0 Y U := by
    intro q η f ψ hη hf hd
    apply full_p1_finite_test_weak_limit_identity hS hc hdim hSb
      (fun n => mesh (χ n)) (fun n => hmesh (χ n)) (fun n => hboundary (χ n)) hκ
      (fun n => a (χ n)) (fun n => r (χ n)) (fun n => hr (χ n)) (fun n => hball (χ n))
      (fun n => hshape (χ n)) (hlim.comp hχ.tendsto_atTop) T (fun n => g (χ n)) (fun n => hT (χ n))
      (htlim.comp hχ.tendsto_atTop) ω b (fun n => u (χ n)) (fun n => y (χ n)) (fun n => hy (χ n))
      Y U y0 η f ψ hη hf hd
      (CE := ‖(dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T))‖*stateTimeEnergyBound T M ‖y0‖ CU)
      (CG := ‖(dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T))‖*stateTimeEnergyBound T M ‖y0‖ CU)
      (CU := CU)
    · intro n
      have he := ((dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T))).le_opNorm (z (χ n))
      have he' := he.trans (mul_le_mul_of_nonneg_left (hz (χ n)) (norm_nonneg _))
      simpa only [z,R,fixedTimeCellReconstruction_map,dirichletGalerkinState_value] using he'
    · intro n
      have he := ((dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T))).le_opNorm (z (χ n))
      have he' := he.trans (mul_le_mul_of_nonneg_left (hz (χ n)) (norm_nonneg _))
      simpa only [z,R,fixedTimeCellReconstruction_map] using he'
    · intro n
      rw [regional_time_control_norm T (g (χ n)) (hT (χ n)) ω hω]
      exact hu (χ n)
    · exact hwv
    · exact hwg
    · intro w
      exact (hU w).comp hχ.tendsto_atTop
    · simp only [hy0]
      exact (full_p1_initial_projection_strong_convergence hS hc mesh hmesh hboundary hlim y0).comp hχ.tendsto_atTop
    · exact hyN.comp hχ.tendsto_atTop
  exact ⟨Y,hY,hid,hid.null_control_state (hT 0 ▸ (g 0).period_pos) hS⟩

end Carleman
