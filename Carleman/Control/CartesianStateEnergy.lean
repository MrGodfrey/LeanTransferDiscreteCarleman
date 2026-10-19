module

public import Carleman.Control.PhysicalStiffnessEnergy
public import Carleman.Control.CartesianAveragedPotential
public import Carleman.Control.TimeCellReconstruction
public import Carleman.Spatial.CartesianPhysicalStiffness

/-! Actual averaged potentials and the full Cartesian state equation give the true gradient budget. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem cartesianPhysicalLaplacian_gradient_sq (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianPhysicalState δ hδ N) :
    inner ℝ (cartesianPhysicalLaplacian o δ hδ N f) f=
      ‖WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f)‖^2 := by
  rw [cartesianPhysicalState_inner]
  change cartesianPhysicalInner δ N (cartesianFiniteDifferenceLaplacian o δ N f) f=_
  rw [cartesianFiniteDifferenceLaplacian_weak_stiffness,weakGradientPairing_apply,real_inner_self_eq_norm_sq]

theorem cartesian_state_gradient_budget
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))))
    (M : ℝ) (hM : 0 ≤ M) (hb : b.bound ≤ M) (hsmall : g.dt*M ≤ 1/2)
    (u : Fin g.steps → CartesianPhysicalControl o δ hδ N ω)
    (y : Fin (g.steps+1) → CartesianPhysicalState δ hδ N)
    (hy : Physical.ForwardEquation g.dt
      (fun i => cartesianPhysicalLaplacian o δ hδ N+
        PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i))
      (cartesianPhysicalControlExtension o δ hδ N ω) u y) :
    2*‖timeCellReconstruction g (fun i => WeakSobolevJet.field 1
      (cartesianKuhnReconstructionJet o δ hδ N (y i.succ)))‖^2 ≤
      ‖y 0‖^2+(Physical.controlNorm g.dt u)^2+(1+2*M)*g.period*
        (Physical.energyConstant g.period M*(‖y 0‖+Physical.controlNorm g.dt u))^2 := by
  have hB : ‖cartesianPhysicalControlExtension o δ hδ N ω‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    rw [cartesianPhysicalControlExtension_norm,one_mul]
  have hV i (v : CartesianPhysicalState δ hδ N) :
      ‖PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i) v‖ ≤ M*‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right ((cartesianAveragedPotential_operator_norm o δ hδ N g b i).trans hb) (norm_nonneg v))
  have hbudget := Physical.forward_stiffness_budget g.dt M g.dt_pos.le hM hsmall
    (cartesianPhysicalLaplacian o δ hδ N).toLinearMap (cartesianPhysicalLaplacian_nonneg o δ hδ N)
    (fun i => (PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i)).toLinearMap)
    hV (cartesianPhysicalControlExtension o δ hδ N ω) hB u y
    ((Physical.forward_equation_iff g.dt_pos.ne' _ _ u y).mp hy)
  have he : ‖timeCellReconstruction g (fun i => WeakSobolevJet.field 1
      (cartesianKuhnReconstructionJet o δ hδ N (y i.succ)))‖^2=
      g.dt*∑ i : Fin g.steps, ‖WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N (y i.succ))‖^2 := by
    rw [← real_inner_self_eq_norm_sq,timeCellReconstruction_inner]
    simp only [real_inner_self_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe,cartesianPhysicalLaplacian_gradient_sq] at hbudget
  change 2*g.dt*(∑ i : Fin g.steps, ‖WeakSobolevJet.field 1
    (cartesianKuhnReconstructionJet o δ hδ N (y i.succ))‖^2) ≤ _ at hbudget
  rw [he]
  simpa only [TimeGrid.period,mul_assoc] using hbudget

theorem cartesian_state_gradient_uniform
    (T M Y U : ℝ) (hM : 0 ≤ M) (hY : 0 ≤ Y) (hU : 0 ≤ U)
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
    (hy0 : ‖y 0‖ ≤ Y) (hu : Physical.controlNorm g.dt u ≤ U) :
    ‖timeCellReconstruction g (fun i => WeakSobolevJet.field 1
      (cartesianKuhnReconstructionJet o δ hδ N (y i.succ)))‖ ≤
      Real.sqrt (Y^2+U^2+(1+2*M)*T*(Physical.energyConstant T M*(Y+U))^2) := by
  have he := cartesian_state_gradient_budget o δ hδ N ω g b M hM hb hsmall u y hy
  conv at he => rhs; rw [hT]
  have hT0 : 0 ≤ T := hT ▸ g.period_pos.le
  have hcu : 0 ≤ Physical.controlNorm g.dt u := Real.sqrt_nonneg _
  have hys := (sq_le_sq₀ (norm_nonneg _) hY).mpr hy0
  have hus := (sq_le_sq₀ hcu hU).mpr hu
  have hb' : (Physical.energyConstant T M*(‖y 0‖+Physical.controlNorm g.dt u))^2 ≤
      (Physical.energyConstant T M*(Y+U))^2 := by
    apply (sq_le_sq₀
      (mul_nonneg (Physical.energyConstant_pos T M).le (add_nonneg (norm_nonneg _) hcu))
      (mul_nonneg (Physical.energyConstant_pos T M).le (add_nonneg hY hU))).mpr
    exact mul_le_mul_of_nonneg_left (add_le_add hy0 hu) (Physical.energyConstant_pos T M).le
  have hm := mul_le_mul_of_nonneg_left hb' (show 0 ≤ (1+2*M)*T by positivity)
  have hsq : ‖timeCellReconstruction g (fun i => WeakSobolevJet.field 1
      (cartesianKuhnReconstructionJet o δ hδ N (y i.succ)))‖^2 ≤
      Y^2+U^2+(1+2*M)*T*(Physical.energyConstant T M*(Y+U))^2 := by
    nlinarith [sq_nonneg ‖timeCellReconstruction g (fun i => WeakSobolevJet.field 1
      (cartesianKuhnReconstructionJet o δ hδ N (y i.succ)))‖]
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hsq

end Carleman
