module

public import Carleman.Control.CartesianStateWeakConsistency
public import Carleman.Control.CartesianStateEnergy

/-! For actual controlled solutions, the state equation supplies the reconstruction-error budget. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem cartesian_state_fixed_gradient_uniform
    (T M Y U : ℝ) (hM : 0 ≤ M) (hY : 0 ≤ Y) (hU : 0 ≤ U)
    (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (ω : Set (SpatialCoordinates d)) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox lo (fun j => lo j+(N j:ℝ)*δ j)))))
    (hb : b.bound ≤ M) (hsmall : g.dt*M ≤ 1/2)
    (u : Fin g.steps → CartesianPhysicalControl lo δ hδ N ω)
    (y : Fin (g.steps+1) → CartesianPhysicalState δ hδ N)
    (hy : Physical.ForwardEquation g.dt
      (fun i => cartesianPhysicalLaplacian lo δ hδ N+
        PhysicalFiniteSpace.multiplier (cartesianAveragedPotential lo δ N g b i))
      (cartesianPhysicalControlExtension lo δ hδ N ω) u y)
    (hy0 : ‖y 0‖ ≤ Y) (hu : Physical.controlNorm g.dt u ≤ U) :
    ‖fixedTimeCellReconstruction T g hT (fun i => WeakSobolevJet.field 1
      (cartesianBoxKuhnReconstructionJet lo hi δ hδ N hbox (y i.succ)))‖ ≤
      Real.sqrt (Y^2+U^2+(1+2*M)*T*(Physical.energyConstant T M*(Y+U))^2) := by
  have he := funext hbox
  subst hi
  subst T
  exact cartesian_state_gradient_uniform g.period M Y U hM hY hU lo δ hδ N ω g rfl b hb hsmall u y hy hy0 hu

theorem cartesian_controlled_states_same_weak_limit
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
    (hy0 : ∀ n, ‖y n 0‖ ≤ Y) (hu : ∀ n, Physical.controlNorm (g n).dt (u n) ≤ U)
    (z : Lp (Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) 2 (volume.restrict (Ioc 0 T)))
    (hweak : ∀ w : Lp (Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) 2 (volume.restrict (Ioc 0 T)),
      Tendsto (fun n => inner ℝ
        (fixedTimeCellReconstruction T (g n) (hT n) (fun i => WeakSobolevJet.value
          (cartesianBoxKuhnReconstructionJet lo hi (δ n) (hδ n) (N n) (hbox n) (y n i.succ)))) w)
        atTop (𝓝 (inner ℝ z w))) :
    ∀ w : Lp (Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi))) 2 (volume.restrict (Ioc 0 T)),
      Tendsto (fun n => inner ℝ
        (fixedTimeCellReconstruction T (g n) (hT n)
          (fun i => cartesianBoxCellIsometry lo hi (δ n) (hδ n) (N n) (hbox n) (y n i.succ))) w)
        atTop (𝓝 (inner ℝ z w)) := by
  apply cartesianBoxCell_kuhn_same_weak_limit lo hi δ hδ N hbox h hh hstep hlim T g hT
    (fun n i => y n i.succ) (B := Real.sqrt (Y^2+U^2+(1+2*M)*T*(Physical.energyConstant T M*(Y+U))^2)) _ z hweak
  intro n
  exact cartesian_state_fixed_gradient_uniform T M Y U hM hY hU lo hi (δ n) (hδ n) (N n) (hbox n)
    ω (g n) (hT n) (b n) (hb n) (hsmall n) (u n) (y n) (hy n) (hy0 n) (hu n)

end Carleman
