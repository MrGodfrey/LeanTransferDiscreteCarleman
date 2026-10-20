module

public import Carleman.Control.ConformingStateTimeEnergy

/-! Actual conforming controlled states have one full energy weak limit with both original spatial fields. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem conforming_controlled_states_weak_subsequence
    (hS : IsOpen S) (hd : 0 < d) (hSb : Bornology.IsBounded S)
    (X : ℕ → Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [∀ n, FiniteDimensional ℝ (X n)]
    (hX : ∀ n, X n ≤ dirichletSubspace S)
    (T M Y U : ℝ) (hM : 0 ≤ M) (hY : 0 ≤ Y) (hU : 0 ≤ U)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (ω : Set (SpatialCoordinates d)) (hω : MeasurableSet ω)
    (b : ∀ n, Fin (g n).steps → BoundedMultiplier (volume.restrict S))
    (hb : ∀ n i, (b n i).bound ≤ M) (hsmall : ∀ n, (g n).dt*M ≤ 1/2)
    (u : ∀ n, Fin (g n).steps → Lp ℝ 2 ((volume.restrict S).restrict ω))
    (y : ∀ n, Fin ((g n).steps+1) → X n)
    (hy : ∀ n, Physical.ForwardEquation (g n).dt
      (fun i => Physical.galerkinStiffness (boundedDirichletOriginalForm hS hd hSb) (X n) (hX n)+
        Physical.conformingPotential (X n) (b n i)) (Physical.conformingRegionControl (X n) ω) (u n) (y n))
    (hy0 : ∀ n, ‖y n 0‖ ≤ Y) (hu : ∀ n, Physical.controlNorm (g n).dt (u n) ≤ U) :
    ∃ v : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)),
      ‖v‖ ≤ stateTimeEnergyBound T M Y U ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ w, Tendsto (fun n => inner ℝ (fixedTimeCellReconstruction T (g (φ n)) (hT (φ n))
        (fun i => dirichletGalerkinState hS hd hSb (X (φ n)) (hX (φ n)) (y (φ n) i.succ))) w)
          atTop (𝓝 (inner ℝ v w))) ∧
      (∀ w, Tendsto (fun n => inner ℝ (fixedTimeCellReconstruction T (g (φ n)) (hT (φ n))
        (fun i => (y (φ n) i.succ : Lp ℝ 2 (volume.restrict S)))) w) atTop
          (𝓝 (inner ℝ ((dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) v) w))) ∧
      (∀ w, Tendsto (fun n => inner ℝ (fixedTimeCellReconstruction T (g (φ n)) (hT (φ n))
        (fun i => dirichletStateGradient S
          (dirichletGalerkinState hS hd hSb (X (φ n)) (hX (φ n)) (y (φ n) i.succ)))) w) atTop
          (𝓝 (inner ℝ ((dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) v) w))) := by
  let z n := fixedTimeCellReconstruction T (g n) (hT n)
    (fun i => dirichletGalerkinState hS hd hSb (X n) (hX n) (y n i.succ))
  have hz n : ‖z n‖ ≤ stateTimeEnergyBound T M Y U :=
    conforming_state_dirichlet_time_uniform hS hd hSb (X n) (hX n) T M Y U hM hY hU
      (g n) (hT n) ω hω (b n) (hb n) (hsmall n) (u n) (y n) (hy n) (hy0 n) (hu n)
  obtain ⟨v,hv,φ,hφ,hw,hvv,hgg⟩ := exists_dirichlet_time_weak_subsequence hS T z hz
  refine ⟨v,hv,φ,hφ,hw,?_,?_⟩
  · simpa only [z,fixedTimeCellReconstruction_map,dirichletGalerkinState_value] using hvv
  · simpa only [z,fixedTimeCellReconstruction_map] using hgg

end Carleman
