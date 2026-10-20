module

public import Carleman.Control.CartesianWeakLimitIdentity
public import Carleman.Control.FixedBoxControlData
public import Carleman.Spatial.CartesianCellStrongConvergence

/-! An arbitrary given weak control limit has one energy state satisfying all original finite tests. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

def FiniteDirichletControlIdentity (T : ℝ) (S : Set (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict S)]
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)))
    (y0 : Lp ℝ 2 (volume.restrict S))
    (Y : Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T)))
    (U : Lp (Lp ℝ 2 (volume.restrict S)) 2 (volume.restrict (Ioc 0 T))) : Prop :=
  ∀ (r : ℕ) (η f : Fin r → ℝ → ℝ) (ψ : Fin r → SpatialTest S)
    (hη : ∀ l, ContinuousOn (η l) (Icc 0 T))
    (hf : ∀ l, ContinuousOn (f l) (Icc 0 T)),
    (∀ l t, t ∈ Icc 0 T → HasDerivWithinAt (η l) (f l t) (Icc 0 T) t) →
    let Yv := (dirichletStateValue S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Yg := (dirichletStateGradient S).compLpL 2 (volume.restrict (Ioc 0 T)) Y;
    let Φ := ∑ l, timeTensor T ((ψ l).toLp (volume.restrict S))
      ((continuous_time_memLp T (η l) (hη l)).toLp (η l));
    let Φd := ∑ l, timeTensor T ((ψ l).toLp (volume.restrict S))
      ((continuous_time_memLp T (f l) (hf l)).toLp (f l));
    let Φg := ∑ l, timeTensor T (dirichletStateGradient S (ψ l).dirichletState)
      ((continuous_time_memLp T (η l) (hη l)).toLp (η l));
    let Φ0 := ∑ l, η l 0 • (ψ l).toLp (volume.restrict S);
    -inner ℝ Yv Φd+inner ℝ Yg Φg+
      inner ℝ (b.map (bochnerL2ProductIsometry Yv)) (finiteTensorTestMultiplier T η ψ hη).toL2=
      inner ℝ y0 Φ0+inner ℝ U Φ

set_option maxHeartbeats 2200000 in
theorem cartesian_weak_control_limit_finite_identity (lo hi : Fin d → ℝ)
    (δ : ℕ → Fin d → ℝ) (hδ : ∀ n j, 0 < δ n j) (N : ℕ → Fin d → ℕ)
    (hN : ∀ n j, 0 < N n j) (hbox : ∀ n j, lo j+(N n j:ℝ)*δ n j=hi j)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) {ratio : ℝ} (hratio : 0 < ratio)
    (hlower : ∀ n j, h n/ratio ≤ δ n j) (hupper : ∀ n j, δ n j ≤ h n)
    (hlim : Tendsto h atTop (𝓝 0))
    (T M CU : ℝ) (hM : 0 ≤ M) (hCU : 0 ≤ CU)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0)) (hsmall : ∀ n, (g n).dt*M ≤ 1/2)
    (ωobs : Set (SpatialCoordinates d))
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict (openCoordinateBox lo hi))))
    (hb : b.bound ≤ M) (y0 : Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi)))
    (u : ∀ n, Fin (g n).steps → CartesianPhysicalControl lo (δ n) (hδ n) (N n) ωobs)
    (y : ∀ n, Fin ((g n).steps+1) → CartesianPhysicalState (δ n) (hδ n) (N n))
    (hy : ∀ n, Physical.ForwardEquation (g n).dt
      (fun i => cartesianPhysicalLaplacian lo (δ n) (hδ n) (N n)+
        PhysicalFiniteSpace.multiplier (cartesianAveragedPotential lo (δ n) (N n) (g n)
          (cartesianGridPotential T lo hi (δ n) (N n) (hbox n) (g n) (hT n) b) i))
      (cartesianPhysicalControlExtension lo (δ n) (hδ n) (N n) ωobs) (u n) (y n))
    (hy0 : ∀ n, y n 0=(cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n)).toContinuousLinearMap.adjoint y0)
    (hu : ∀ n, Physical.controlNorm (g n).dt (u n) ≤ CU)
    (hyN : Tendsto (fun n => ‖y n (Fin.last (g n).steps)‖) atTop (𝓝 0))
    (U : Lp (Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) 2 (volume.restrict (Ioc 0 T)))
    (hU : ∀ w, Tendsto (fun n => inner ℝ (fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => cartesianBoxCellControl lo hi (δ n) (hδ n) (N n) (hbox n) ωobs (u n i))) w)
        atTop (𝓝 (inner ℝ U w))) :
    ∃ Y : Lp (DirichletEnergyState (openCoordinateBox lo hi)) 2 (volume.restrict (Ioc 0 T)),
      ‖Y‖ ≤ stateTimeEnergyBound T M ‖y0‖ CU ∧
      FiniteDirichletControlIdentity T (openCoordinateBox lo hi) b y0 Y U := by
  let bg n := cartesianGridPotential T lo hi (δ n) (N n) (hbox n) (g n) (hT n) b
  have hbg n : (bg n).bound ≤ M := by simpa only [bg,cartesianGridPotential_bound] using hb
  have hy0n n : ‖y n 0‖ ≤ ‖y0‖ := by
    rw [hy0]
    exact cartesianBoxCellIsometry_average_norm lo hi (δ n) (hδ n) (N n) (hbox n) y0
  obtain ⟨Y,hY,φ,hφ,hwR,hwv,hwg,hwe⟩ := cartesian_controlled_states_weak_subsequence
    T M ‖y0‖ CU hM (norm_nonneg _) hCU lo hi δ hδ N hbox h (fun n => (hh n).le)
    hupper hlim g hT ωobs bg hbg hsmall u y hy hy0n hu
  refine ⟨Y,hY,?_⟩
  intro r η f ψ hη hf hd
  apply cartesian_finite_test_weak_limit_identity lo hi
    (fun n => δ (φ n)) (fun n => hδ (φ n)) (fun n => N (φ n)) (fun n => hN (φ n))
    (fun n => hbox (φ n)) (fun n => h (φ n)) (fun n => hh (φ n)) hratio
    (fun n => hlower (φ n)) (fun n => hupper (φ n)) (hlim.comp hφ.tendsto_atTop)
    T (fun n => g (φ n)) (fun n => hT (φ n)) (htlim.comp hφ.tendsto_atTop) ωobs b
    (fun n => u (φ n)) (fun n => y (φ n)) (fun n => hy (φ n)) Y U y0 η f ψ hη hf hd
    (CE := Real.sqrt (T*(Physical.energyConstant T M*(‖y0‖+CU))^2))
    (CG := Real.sqrt (‖y0‖^2+CU^2+(1+2*M)*T*(Physical.energyConstant T M*(‖y0‖+CU))^2)) (CU := CU)
  · intro n
    have ht : 0 ≤ T := hT 0 ▸ (g 0).period_pos.le
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    apply fixedTimeCellReconstruction_norm_sq_le T (g (φ n)) (hT (φ n)) _
      (mul_nonneg (Physical.energyConstant_pos T M).le (add_nonneg (norm_nonneg _) hCU))
    intro i
    rw [LinearIsometry.norm_map]
    exact cartesian_state_node_uniform T M ‖y0‖ CU hM lo (δ (φ n)) (hδ (φ n)) (N (φ n))
      ωobs (g (φ n)) (hT (φ n)) (bg (φ n)) (hbg (φ n)) (hsmall (φ n))
      (u (φ n)) (y (φ n)) (hy (φ n)) (hy0n (φ n)) (hu (φ n)) i.succ
  · intro n
    exact cartesian_state_fixed_gradient_uniform T M ‖y0‖ CU hM (norm_nonneg _) hCU
      lo hi (δ (φ n)) (hδ (φ n)) (N (φ n)) (hbox (φ n)) ωobs (g (φ n)) (hT (φ n))
      (bg (φ n)) (hbg (φ n)) (hsmall (φ n)) (u (φ n)) (y (φ n)) (hy (φ n)) (hy0n (φ n)) (hu (φ n))
  · intro n
    rw [cartesianBoxTimeControl_norm]
    exact hu (φ n)
  · exact hwe
  · exact hwg
  · intro w
    exact (hU w).comp hφ.tendsto_atTop
  · simp only [hy0]
    exact (cartesianBoxCell_average_strong_convergence lo hi δ hδ N hN hbox h (fun n => (hh n).le)
      hupper hlim y0).comp hφ.tendsto_atTop
  · exact hyN.comp hφ.tendsto_atTop

end Carleman
