module

public import Carleman.Control.ConformingDirichletState
public import Carleman.Control.ConformingRegionControl
public import Carleman.Control.CartesianStateTimeEnergy

/-! The original conforming controlled equation supplies a uniform full time-energy bound. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem conforming_state_node_uniform (hS : IsOpen S) (hd : 0 < d) (hSb : Bornology.IsBounded S)
    (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
    (hX : X ≤ dirichletSubspace S)
    (T M Y U : ℝ) (hM : 0 ≤ M) (g : TimeGrid) (hT : g.period=T)
    (ω : Set (SpatialCoordinates d)) (hω : MeasurableSet ω)
    (b : Fin g.steps → BoundedMultiplier (volume.restrict S)) (hb : ∀ i, (b i).bound ≤ M)
    (hsmall : g.dt*M ≤ 1/2)
    (u : Fin g.steps → Lp ℝ 2 ((volume.restrict S).restrict ω)) (y : Fin (g.steps+1) → X)
    (hy : Physical.ForwardEquation g.dt
      (fun i => Physical.galerkinStiffness (boundedDirichletOriginalForm hS hd hSb) X hX+
        Physical.conformingPotential X (b i)) (Physical.conformingRegionControl X ω) u y)
    (hy0 : ‖y 0‖ ≤ Y) (hu : Physical.controlNorm g.dt u ≤ U) (k : Fin (g.steps+1)) :
    ‖y k‖ ≤ Physical.energyConstant T M*(Y+U) := by
  let a := boundedDirichletOriginalForm hS hd hSb
  have hV i (x : X) : ‖Physical.conformingPotential X (b i) x‖ ≤ M*‖x‖ :=
    (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right ((Physical.conformingPotential_norm X (b i)).trans (hb i)) (norm_nonneg x))
  have hL i x : -M*‖x‖^2 ≤ inner ℝ ((Physical.galerkinStiffness a X hX+
      Physical.conformingPotential X (b i)) x) x :=
    Physical.stiffness_potential_lower (Physical.galerkinStiffness a X hX).toLinearMap
      (Physical.conformingPotential X (b i)).toLinearMap M (Physical.galerkinStiffness_nonneg a X hX) (hV i) x
  have he := Physical.forward_energy g.dt M g.dt_pos.le hM hsmall
    (fun i => (Physical.galerkinStiffness a X hX+Physical.conformingPotential X (b i)).toLinearMap)
    hL (Physical.conformingRegionControl X ω) (Physical.conformingRegionControl_norm X ω hω) u y
    ((Physical.forward_equation_iff g.dt_pos.ne' _ _ u y).mp hy) k
  change ‖y k‖ ≤ Physical.energyConstant g.period M*(‖y 0‖+Physical.controlNorm g.dt u) at he
  rw [hT] at he
  exact he.trans (mul_le_mul_of_nonneg_left (add_le_add hy0 hu) (Physical.energyConstant_pos T M).le)

theorem conforming_state_dirichlet_time_uniform
    (hS : IsOpen S) (hd : 0 < d) (hSb : Bornology.IsBounded S)
    (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
    (hX : X ≤ dirichletSubspace S)
    (T M Y U : ℝ) (hM : 0 ≤ M) (hY : 0 ≤ Y) (hU : 0 ≤ U)
    (g : TimeGrid) (hT : g.period=T) (ω : Set (SpatialCoordinates d)) (hω : MeasurableSet ω)
    (b : Fin g.steps → BoundedMultiplier (volume.restrict S)) (hb : ∀ i, (b i).bound ≤ M)
    (hsmall : g.dt*M ≤ 1/2)
    (u : Fin g.steps → Lp ℝ 2 ((volume.restrict S).restrict ω)) (y : Fin (g.steps+1) → X)
    (hy : Physical.ForwardEquation g.dt
      (fun i => Physical.galerkinStiffness (boundedDirichletOriginalForm hS hd hSb) X hX+
        Physical.conformingPotential X (b i)) (Physical.conformingRegionControl X ω) u y)
    (hy0 : ‖y 0‖ ≤ Y) (hu : Physical.controlNorm g.dt u ≤ U) :
    ‖fixedTimeCellReconstruction T g hT
      (fun i => dirichletGalerkinState hS hd hSb X hX (y i.succ))‖ ≤ stateTimeEnergyBound T M Y U := by
  subst T
  let := dirichletEnergyState_complete hS
  let a := boundedDirichletOriginalForm hS hd hSb
  let A := Physical.galerkinStiffness a X hX
  let B := Physical.energyConstant g.period M*(Y+U)
  have hBpos : 0 ≤ B := mul_nonneg (Physical.energyConstant_pos _ _).le (add_nonneg hY hU)
  have hnode (k : Fin (g.steps+1)) : ‖y k‖ ≤ B :=
    conforming_state_node_uniform hS hd hSb X hX g.period M Y U hM g rfl ω hω b hb hsmall u y hy hy0 hu k
  have hV i (x : X) : ‖Physical.conformingPotential X (b i) x‖ ≤ M*‖x‖ :=
    (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right ((Physical.conformingPotential_norm X (b i)).trans (hb i)) (norm_nonneg x))
  have hf := (Physical.forward_equation_iff g.dt_pos.ne'
    (fun i => A+Physical.conformingPotential X (b i))
    (Physical.conformingRegionControl X ω) u y).mp hy
  simp only [ContinuousLinearMap.toLinearMap_add] at hf
  have hs := Physical.forward_stiffness_budget_of_state_bound g.dt M B g.dt_pos.le hM hBpos
    A.toLinearMap (fun i => (Physical.conformingPotential X (b i)).toLinearMap) hV
    (Physical.conformingRegionControl X ω) (Physical.conformingRegionControl_norm X ω hω) u y
    hf hnode
  change 2*g.dt*(∑ i : Fin g.steps, inner ℝ (A (y i.succ)) (y i.succ)) ≤
    ‖y 0‖^2+(Physical.controlNorm g.dt u)^2+(1+2*M)*g.period*B^2 at hs
  have hys := (sq_le_sq₀ (norm_nonneg _) hY).mpr hy0
  have hus := (sq_le_sq₀ (Real.sqrt_nonneg _) hU).mpr hu
  change (Physical.controlNorm g.dt u)^2 ≤ U^2 at hus
  have hv := fixedTimeCellReconstruction_norm_sq_le g.period g rfl (fun i => y i.succ)
    hBpos (fun i => hnode i.succ)
  change ‖timeCellReconstruction g (fun i => y i.succ)‖^2 ≤ g.period*B^2 at hv
  have hvnorm : ‖timeCellReconstruction g (fun i => y i.succ)‖^2=
      g.dt*∑ i : Fin g.steps, ‖y i.succ‖^2 := by
    rw [← real_inner_self_eq_norm_sq,timeCellReconstruction_inner]
    simp only [real_inner_self_eq_norm_sq]
  have hfull : ‖timeCellReconstruction g
      (fun i => dirichletGalerkinState hS hd hSb X hX (y i.succ))‖^2=
      ‖timeCellReconstruction g (fun i => y i.succ)‖^2+
        g.dt*(∑ i : Fin g.steps, inner ℝ (A (y i.succ)) (y i.succ)) := by
    rw [← real_inner_self_eq_norm_sq,timeCellReconstruction_inner,hvnorm]
    simp only [real_inner_self_eq_norm_sq,dirichletGalerkinState_norm_sq,Finset.sum_add_distrib,mul_add]
    rfl
  have hspos : 0 ≤ g.dt*(∑ i : Fin g.steps, inner ℝ (A (y i.succ)) (y i.succ)) :=
    mul_nonneg g.dt_pos.le (Finset.sum_nonneg (fun i _ => Physical.galerkinStiffness_nonneg a X hX (y i.succ)))
  change ‖timeCellReconstruction g
    (fun i => dirichletGalerkinState hS hd hSb X hX (y i.succ))‖ ≤
      Real.sqrt (g.period*B^2+(Y^2+U^2+(1+2*M)*g.period*B^2))
  apply (Real.le_sqrt (norm_nonneg _) (by have hTpos := g.period_pos; positivity)).mpr
  rw [hfull]
  nlinarith

end Carleman
