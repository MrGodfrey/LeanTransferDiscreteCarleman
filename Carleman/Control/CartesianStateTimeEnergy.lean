module

public import Carleman.Control.CartesianDirichletReconstruction
public import Carleman.Control.CartesianEquationWeakConsistency

/-! A uniform bound in the true L²(0,T;H¹₀) energy norm, derived from the original controlled equation. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem cartesian_state_node_uniform
    (T M Y U : ℝ) (hM : 0 ≤ M)
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))))
    (hb : b.bound ≤ M) (hsmall : g.dt*M ≤ 1/2)
    (u : Fin g.steps → CartesianPhysicalControl o δ hδ N ω)
    (y : Fin (g.steps+1) → CartesianPhysicalState δ hδ N)
    (hy : Physical.ForwardEquation g.dt
      (fun i => cartesianPhysicalLaplacian o δ hδ N+
        PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i))
      (cartesianPhysicalControlExtension o δ hδ N ω) u y)
    (hy0 : ‖y 0‖ ≤ Y) (hu : Physical.controlNorm g.dt u ≤ U) (k : Fin (g.steps+1)) :
    ‖y k‖ ≤ Physical.energyConstant T M*(Y+U) := by
  have hB : ‖cartesianPhysicalControlExtension o δ hδ N ω‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    rw [cartesianPhysicalControlExtension_norm,one_mul]
  have hV i (v : CartesianPhysicalState δ hδ N) :
      ‖PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i) v‖ ≤ M*‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right ((cartesianAveragedPotential_operator_norm o δ hδ N g b i).trans hb) (norm_nonneg v))
  have hL (i : Fin g.steps) (v : CartesianPhysicalState δ hδ N) : -M*‖v‖^2 ≤ inner ℝ
      ((cartesianPhysicalLaplacian o δ hδ N+
        PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i) :
          CartesianPhysicalState δ hδ N →L[ℝ] CartesianPhysicalState δ hδ N) v) v :=
    Physical.stiffness_potential_lower (cartesianPhysicalLaplacian o δ hδ N).toLinearMap
      (PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i)).toLinearMap M
      (cartesianPhysicalLaplacian_nonneg o δ hδ N) (hV i) v
  have he := Physical.forward_energy g.dt M g.dt_pos.le hM hsmall
    (fun i => (cartesianPhysicalLaplacian o δ hδ N+
      PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i)).toLinearMap)
    hL (cartesianPhysicalControlExtension o δ hδ N ω) hB u y
    ((Physical.forward_equation_iff g.dt_pos.ne' _ _ u y).mp hy) k
  change ‖y k‖ ≤ Physical.energyConstant g.period M*(‖y 0‖+Physical.controlNorm g.dt u) at he
  rw [hT] at he
  exact he.trans (mul_le_mul_of_nonneg_left (add_le_add hy0 hu) (Physical.energyConstant_pos T M).le)


def stateTimeEnergyBound (T M Y U : ℝ) : ℝ :=
  Real.sqrt (T*(Physical.energyConstant T M*(Y+U))^2+
    (Y^2+U^2+(1+2*M)*T*(Physical.energyConstant T M*(Y+U))^2))

theorem cartesian_state_dirichlet_time_uniform
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
    ‖fixedTimeCellReconstruction T g hT
      (fun i => cartesianBoxDirichletState lo hi δ hδ N hbox (y i.succ))‖ ≤
      stateTimeEnergyBound T M Y U := by
  let S := openCoordinateBox lo hi
  let : CompleteSpace (DirichletEnergyState S) :=
    dirichletEnergyState_complete (openCoordinateBox_isOpen _ _)
  let r := fun i : Fin g.steps => cartesianBoxDirichletState lo hi δ hδ N hbox (y i.succ)
  have hT0 : 0 ≤ T := hT ▸ g.period_pos.le
  have hnode i : ‖dirichletStateValue S (r i)‖ ≤ Physical.energyConstant T M*(Y+U) := by
    apply (cartesianBoxDirichletState_value_norm_le lo hi δ hδ N hbox (y i.succ)).trans
    exact cartesian_state_node_uniform T M Y U hM lo δ hδ N ω g hT b hb hsmall u y hy hy0 hu i.succ
  have hv := fixedTimeCellReconstruction_norm_sq_le T g hT (fun i => dirichletStateValue S (r i))
    (mul_nonneg (Physical.energyConstant_pos T M).le (add_nonneg hY hU)) hnode
  have hg := cartesian_state_fixed_gradient_uniform T M Y U hM hY hU lo hi δ hδ N hbox
    ω g hT b hb hsmall u y hy hy0 hu
  have hgs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hg
  rw [Real.sq_sqrt (show 0 ≤ Y^2+U^2+(1+2*M)*T*(Physical.energyConstant T M*(Y+U))^2 by positivity)] at hgs
  have he : ‖fixedTimeCellReconstruction T g hT r‖^2=
      ‖fixedTimeCellReconstruction T g hT (fun i => dirichletStateValue S (r i))‖^2+
      ‖fixedTimeCellReconstruction T g hT (fun i => dirichletStateGradient S (r i))‖^2 := by
    subst T
    exact dirichlet_time_norm_sq (openCoordinateBox_isOpen _ _) g r
  change ‖fixedTimeCellReconstruction T g hT r‖ ≤ _
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  rw [he]
  exact add_le_add hv hgs

end Carleman
