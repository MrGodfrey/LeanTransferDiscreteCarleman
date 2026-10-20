module

public import Carleman.Control.CartesianStateTimeEnergy

/-! Original controlled states have a common weakly convergent subsequence in the actual energy space. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 5000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem cartesian_controlled_states_weak_subsequence
    (T M Y U : ℝ) (hM : 0 ≤ M) (hY : 0 ≤ Y) (hU : 0 ≤ U)
    (lo hi : Fin d → ℝ) (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j)
    (N : ℕ → Fin d → ℕ) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 ≤ h n) (hstep : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0)) (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (ω : Set (SpatialCoordinates d))
    (b : ∀ n, BoundedMultiplier ((volume.restrict (Ioc 0 (g n).period)).prod
      (volume.restrict (openCoordinateBox lo (fun j => lo j+(N n j:ℝ)*δ n j)))))
    (hb : ∀ n, (b n).bound ≤ M) (hsmall : ∀ n, (g n).dt*M ≤ 1/2)
    (u : ∀ n, Fin (g n).steps → CartesianPhysicalControl lo (δ n) (hδ n) (N n) ω)
    (y : ∀ n, Fin ((g n).steps+1) → CartesianPhysicalState (δ n) (hδ n) (N n))
    (hy : ∀ n, Physical.ForwardEquation (g n).dt
      (fun i => cartesianPhysicalLaplacian lo (δ n) (hδ n) (N n)+
        PhysicalFiniteSpace.multiplier (cartesianAveragedPotential lo (δ n) (N n) (g n) (b n) i))
      (cartesianPhysicalControlExtension lo (δ n) (hδ n) (N n) ω) (u n) (y n))
    (hy0 : ∀ n, ‖y n 0‖ ≤ Y) (hu : ∀ n, Physical.controlNorm (g n).dt (u n) ≤ U) :
    ∃ v : Lp (DirichletEnergyState (openCoordinateBox lo hi)) 2 (volume.restrict (Ioc 0 T)),
      ‖v‖ ≤ stateTimeEnergyBound T M Y U ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ w, Tendsto (fun n => inner ℝ
        (fixedTimeCellReconstruction T (g (φ n)) (hT (φ n))
          (fun i => cartesianBoxDirichletState lo hi (δ (φ n)) (hδ (φ n)) (N (φ n))
            (hbox (φ n)) (y (φ n) i.succ))) w) atTop (𝓝 (inner ℝ v w))) ∧
      (∀ w, Tendsto (fun n => inner ℝ
        (fixedTimeCellReconstruction T (g (φ n)) (hT (φ n))
          (fun i => WeakSobolevJet.value (cartesianBoxKuhnReconstructionJet lo hi (δ (φ n))
            (hδ (φ n)) (N (φ n)) (hbox (φ n)) (y (φ n) i.succ)))) w) atTop
        (𝓝 (inner ℝ ((dirichletStateValue (openCoordinateBox lo hi)).compLpL 2
          (volume.restrict (Ioc 0 T)) v) w))) ∧
      (∀ w, Tendsto (fun n => inner ℝ
        (fixedTimeCellReconstruction T (g (φ n)) (hT (φ n))
          (fun i => WeakSobolevJet.field 1 (cartesianBoxKuhnReconstructionJet lo hi (δ (φ n))
            (hδ (φ n)) (N (φ n)) (hbox (φ n)) (y (φ n) i.succ)))) w) atTop
        (𝓝 (inner ℝ ((dirichletStateGradient (openCoordinateBox lo hi)).compLpL 2
          (volume.restrict (Ioc 0 T)) v) w))) ∧
      (∀ w, Tendsto (fun n => inner ℝ
        (fixedTimeCellReconstruction T (g (φ n)) (hT (φ n))
          (fun i => cartesianBoxCellIsometry lo hi (δ (φ n)) (hδ (φ n)) (N (φ n))
            (hbox (φ n)) (y (φ n) i.succ))) w) atTop
        (𝓝 (inner ℝ ((dirichletStateValue (openCoordinateBox lo hi)).compLpL 2
          (volume.restrict (Ioc 0 T)) v) w))) := by
  let r := fun n => fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => cartesianBoxDirichletState lo hi (δ n) (hδ n) (N n) (hbox n) (y n i.succ))
  have hr n : ‖r n‖ ≤ stateTimeEnergyBound T M Y U :=
    cartesian_state_dirichlet_time_uniform T M Y U hM hY hU lo hi (δ n) (hδ n) (N n) (hbox n)
      ω (g n) (hT n) (b n) (hb n) (hsmall n) (u n) (y n) (hy n) (hy0 n) (hu n)
  obtain ⟨v,hv,φ,hφ,ht,hvweak,hgweak⟩ :=
    exists_dirichlet_time_weak_subsequence (openCoordinateBox_isOpen lo hi) T r hr
  have hvweak' := hvweak
  simp only [r,fixedTimeCellReconstruction_map,cartesianBoxDirichletState_value] at hvweak'
  have hgweak' := hgweak
  simp only [r,fixedTimeCellReconstruction_map,cartesianBoxDirichletState_gradient] at hgweak'
  refine ⟨v,hv,φ,hφ,ht,hvweak',hgweak',?_⟩
  exact cartesian_controlled_states_same_weak_limit T M Y U hM hY hU lo hi
    (fun n => δ (φ n)) (fun n => hδ (φ n)) (fun n => N (φ n)) (fun n => hbox (φ n))
    (fun n => h (φ n)) (fun n => hh (φ n)) (fun n => hstep (φ n))
    (hlim.comp hφ.tendsto_atTop) (fun n => g (φ n)) (fun n => hT (φ n)) ω
    (fun n => b (φ n)) (fun n => hb (φ n)) (fun n => hsmall (φ n))
    (fun n => u (φ n)) (fun n => y (φ n)) (fun n => hy (φ n))
    (fun n => hy0 (φ n)) (fun n => hu (φ n)) _ hvweak'

end Carleman
