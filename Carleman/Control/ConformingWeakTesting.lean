module

public import Carleman.Control.ConformingDirichletState
public import Carleman.Control.ConformingRegionControl
public import Carleman.Control.PhysicalWeakTesting
public import Carleman.Control.TimeWeakTesting

/-! Every term of the original conforming equation in the actual time reconstruction spaces. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem conforming_forward_reconstructed_weak_identity
    (hS : IsOpen S) (hd : 0 < d) (hSb : Bornology.IsBounded S)
    (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
    (hX : X ≤ dirichletSubspace S)
    (ω : Set (SpatialCoordinates d)) (g : TimeGrid)
    (b : Fin g.steps → BoundedMultiplier (volume.restrict S))
    (u : Fin g.steps → Lp ℝ 2 ((volume.restrict S).restrict ω))
    (y φ : Fin (g.steps+1) → X)
    (hy : Physical.ForwardEquation g.dt
      (fun i => Physical.galerkinStiffness (boundedDirichletOriginalForm hS hd hSb) X hX+
        Physical.conformingPotential X (b i)) (Physical.conformingRegionControl X ω) u y) :
    let E := X.subtypeₗᵢ;
    let G := (dirichletStateGradient S).comp (dirichletGalerkinState hS hd hSb X hX);
    let K := (Physical.restrictRegionCLM (E := ℝ) (ν := volume.restrict S) ω).adjoint;
    -inner ℝ (timeCellReconstruction g (fun i => E (y i.succ)))
        (timeCellReconstruction g (fun i => E (g.dt⁻¹ • (φ i.succ-φ i.castSucc))))+
      inner ℝ (timeCellReconstruction g (fun i => G (y i.succ)))
        (timeCellReconstruction g (fun i => G (φ i.castSucc)))+
      inner ℝ (timeCellReconstruction g (fun i => (b i).map (E (y i.succ))))
        (timeCellReconstruction g (fun i => E (φ i.castSucc)))=
      inner ℝ (E (y 0)) (E (φ 0))+
        inner ℝ (timeCellReconstruction g (fun i => K (u i)))
          (timeCellReconstruction g (fun i => E (φ i.castSucc)))-
        inner ℝ (E (y (Fin.last g.steps))) (E (φ (Fin.last g.steps))) := by
  dsimp only
  rw [timeCellReconstruction_difference_inner]
  simp only [timeCellReconstruction_inner,LinearIsometry.inner_map_map,ContinuousLinearMap.comp_apply,
    ← dirichletGalerkinState_stiffness]
  have hpot i : inner ℝ ((b i).map (X.subtypeₗᵢ (y i.succ))) (X.subtypeₗᵢ (φ i.castSucc))=
      inner ℝ (Physical.conformingPotential X (b i) (y i.succ)) (φ i.castSucc) := by
    rw [Physical.conformingPotential_apply,X.inner_orthogonalProjectionOnto_eq_of_mem_right]
    rfl
  have hcontrol i : inner ℝ ((Physical.restrictRegionCLM (E := ℝ) (ν := volume.restrict S) ω).adjoint (u i))
      (X.subtypeₗᵢ (φ i.castSucc))=inner ℝ (Physical.conformingRegionControl X ω (u i)) (φ i.castSucc) := by
    change _=inner ℝ (X.orthogonalProjectionOnto _) (φ i.castSucc)
    rw [X.inner_orthogonalProjectionOnto_eq_of_mem_right]
    rfl
  simp only [hpot,hcontrol]
  have hw := Physical.forward_equation_weak_identity g.dt_pos.ne'
    (fun i => Physical.galerkinStiffness (boundedDirichletOriginalForm hS hd hSb) X hX+
      Physical.conformingPotential X (b i)) (Physical.conformingRegionControl X ω) u y φ hy
  simp only [add_apply,inner_add_left,Finset.sum_add_distrib,mul_add] at hw
  linarith only [hw]

theorem conforming_fixed_forward_reconstructed_weak_identity
    (hS : IsOpen S) (hd : 0 < d) (hSb : Bornology.IsBounded S)
    (X : Submodule ℝ (Lp ℝ 2 (volume.restrict S))) [FiniteDimensional ℝ X]
    (hX : X ≤ dirichletSubspace S)
    (T : ℝ) (ω : Set (SpatialCoordinates d)) (g : TimeGrid) (hT : g.period=T)
    (b : Fin g.steps → BoundedMultiplier (volume.restrict S))
    (u : Fin g.steps → Lp ℝ 2 ((volume.restrict S).restrict ω))
    (y φ : Fin (g.steps+1) → X)
    (hy : Physical.ForwardEquation g.dt
      (fun i => Physical.galerkinStiffness (boundedDirichletOriginalForm hS hd hSb) X hX+
        Physical.conformingPotential X (b i)) (Physical.conformingRegionControl X ω) u y) :
    let E := X.subtypeₗᵢ;
    let G := (dirichletStateGradient S).comp (dirichletGalerkinState hS hd hSb X hX);
    let K := (Physical.restrictRegionCLM (E := ℝ) (ν := volume.restrict S) ω).adjoint;
    -inner ℝ (fixedTimeCellReconstruction T g hT (fun i => E (y i.succ)))
        (fixedTimeCellReconstruction T g hT (fun i => E (g.dt⁻¹ • (φ i.succ-φ i.castSucc))))+
      inner ℝ (fixedTimeCellReconstruction T g hT (fun i => G (y i.succ)))
        (fixedTimeCellReconstruction T g hT (fun i => G (φ i.castSucc)))+
      inner ℝ (fixedTimeCellReconstruction T g hT (fun i => (b i).map (E (y i.succ))))
        (fixedTimeCellReconstruction T g hT (fun i => E (φ i.castSucc)))=
      inner ℝ (E (y 0)) (E (φ 0))+
        inner ℝ (fixedTimeCellReconstruction T g hT (fun i => K (u i)))
          (fixedTimeCellReconstruction T g hT (fun i => E (φ i.castSucc)))-
        inner ℝ (E (y (Fin.last g.steps))) (E (φ (Fin.last g.steps))) := by
  subst T
  exact conforming_forward_reconstructed_weak_identity hS hd hSb X hX ω g b u y φ hy

end Carleman
