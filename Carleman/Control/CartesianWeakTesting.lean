module

public import Carleman.Control.PhysicalWeakTesting
public import Carleman.Control.TimeWeakTesting
public import Carleman.Control.CartesianPotentialReconstruction
public import Carleman.Spatial.CartesianPhysicalStiffness

/-! The complete original finite-difference equation tested against arbitrary physical states,
with every term identified in the actual Bochner reconstruction spaces. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem cartesianPhysicalLaplacian_gradient_pairing
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (f z : CartesianPhysicalState δ hδ N) :
    inner ℝ (cartesianPhysicalLaplacian o δ hδ N f) z=
      inner ℝ (WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f))
        (WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N z)) := by
  rw [cartesianPhysicalState_inner]
  change cartesianPhysicalInner δ N (cartesianFiniteDifferenceLaplacian o δ N f) z=_
  rw [cartesianFiniteDifferenceLaplacian_weak_stiffness,weakGradientPairing_apply]

theorem cartesian_forward_reconstructed_weak_identity
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))))
    (u : Fin g.steps → CartesianPhysicalControl o δ hδ N ω)
    (y φ : Fin (g.steps+1) → CartesianPhysicalState δ hδ N)
    (hy : Physical.ForwardEquation g.dt
      (fun i => cartesianPhysicalLaplacian o δ hδ N+
        PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i))
      (cartesianPhysicalControlExtension o δ hδ N ω) u y) :
    let E := cartesianCellIsometry o δ hδ N;
    let G := fun f : CartesianPhysicalState δ hδ N =>
      WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f);
    let K := cartesianCellControl o δ hδ N ω;
    let P := cartesianReconstructedPotential o δ hδ N g b;
    -inner ℝ (timeCellReconstruction g (fun i => E (y i.succ)))
        (timeCellReconstruction g (fun i => E (g.dt⁻¹ • (φ i.succ-φ i.castSucc))))+
      inner ℝ (timeCellReconstruction g (fun i => G (y i.succ)))
        (timeCellReconstruction g (fun i => G (φ i.castSucc)))+
      inner ℝ (timeCellReconstruction g (fun i => (P i).map (E (y i.succ))))
        (timeCellReconstruction g (fun i => E (φ i.castSucc)))=
      inner ℝ (E (y 0)) (E (φ 0))+
        inner ℝ (timeCellReconstruction g (fun i => K (u i)))
          (timeCellReconstruction g (fun i => E (φ i.castSucc)))-
        inner ℝ (E (y (Fin.last g.steps))) (E (φ (Fin.last g.steps))) := by
  dsimp only
  rw [timeCellReconstruction_difference_inner]
  simp only [timeCellReconstruction_inner,cartesianCellIsometry_inner,
    ← cartesianPhysicalLaplacian_gradient_pairing,← cartesianReconstructedPotential_pairing]
  have hcontrol i : inner ℝ (cartesianCellControl o δ hδ N ω (u i))
      (cartesianCellIsometry o δ hδ N (φ i.castSucc))=
        inner ℝ (cartesianPhysicalControlExtension o δ hδ N ω (u i)) (φ i.castSucc) :=
    (cartesianCellIsometry o δ hδ N).inner_map_map _ _
  simp only [hcontrol]
  have hw := Physical.forward_equation_weak_identity g.dt_pos.ne'
    (fun i => cartesianPhysicalLaplacian o δ hδ N+
      PhysicalFiniteSpace.multiplier (cartesianAveragedPotential o δ N g b i))
    (cartesianPhysicalControlExtension o δ hδ N ω) u y φ hy
  simp only [add_apply,inner_add_left,Finset.sum_add_distrib,mul_add] at hw
  linarith only [hw]

end Carleman
