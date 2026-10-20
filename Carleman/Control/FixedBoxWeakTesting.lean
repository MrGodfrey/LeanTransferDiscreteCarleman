module

public import Carleman.Control.CartesianWeakTesting
public import Carleman.Spatial.FixedBoxKuhnConsistency

/-! The original reconstructed weak identity in one fixed physical space and time interval. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

def cartesianBoxCellControl (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (ω : Set (SpatialCoordinates d)) : CartesianPhysicalControl lo δ hδ N ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (openCoordinateBox lo hi)) :=
  (cartesianBoxCellIsometry lo hi δ hδ N hbox).toContinuousLinearMap.comp
    (cartesianPhysicalControlExtension lo δ hδ N ω)

def cartesianBoxReconstructedPotential (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox lo (fun j => lo j+(N j:ℝ)*δ j)))))
    (i : Fin g.steps) : BoundedMultiplier (volume.restrict (openCoordinateBox lo hi)) :=
  (funext hbox) ▸ cartesianReconstructedPotential lo δ hδ N g b i

theorem cartesianBoxReconstructedPotential_commute
    (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j) (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox lo (fun j => lo j+(N j:ℝ)*δ j)))))
    (i : Fin g.steps) (z : CartesianPhysicalState δ hδ N) :
    (cartesianBoxReconstructedPotential lo hi δ hδ N hbox g b i).map
      (cartesianBoxCellIsometry lo hi δ hδ N hbox z)=
      cartesianBoxCellIsometry lo hi δ hδ N hbox
        (PhysicalFiniteSpace.multiplier (cartesianAveragedPotential lo δ N g b i) z) := by
  have he := funext hbox
  subst hi
  exact cartesianReconstructedPotential_commute lo δ hδ N g b i z

theorem cartesian_fixed_forward_reconstructed_weak_identity
    (T : ℝ) (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (ω : Set (SpatialCoordinates d)) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod
      (volume.restrict (openCoordinateBox lo (fun j => lo j+(N j:ℝ)*δ j)))))
    (u : Fin g.steps → CartesianPhysicalControl lo δ hδ N ω)
    (y φ : Fin (g.steps+1) → CartesianPhysicalState δ hδ N)
    (hy : Physical.ForwardEquation g.dt
      (fun i => cartesianPhysicalLaplacian lo δ hδ N+
        PhysicalFiniteSpace.multiplier (cartesianAveragedPotential lo δ N g b i))
      (cartesianPhysicalControlExtension lo δ hδ N ω) u y) :
    let E := cartesianBoxCellIsometry lo hi δ hδ N hbox;
    let G := fun f : CartesianPhysicalState δ hδ N =>
      WeakSobolevJet.field 1 (cartesianBoxKuhnReconstructionJet lo hi δ hδ N hbox f);
    let K := cartesianBoxCellControl lo hi δ hδ N hbox ω;
    let P := cartesianBoxReconstructedPotential lo hi δ hδ N hbox g b;
    -inner ℝ (fixedTimeCellReconstruction T g hT (fun i => E (y i.succ)))
        (fixedTimeCellReconstruction T g hT (fun i => E (g.dt⁻¹ • (φ i.succ-φ i.castSucc))))+
      inner ℝ (fixedTimeCellReconstruction T g hT (fun i => G (y i.succ)))
        (fixedTimeCellReconstruction T g hT (fun i => G (φ i.castSucc)))+
      inner ℝ (fixedTimeCellReconstruction T g hT (fun i => (P i).map (E (y i.succ))))
        (fixedTimeCellReconstruction T g hT (fun i => E (φ i.castSucc)))=
      inner ℝ (E (y 0)) (E (φ 0))+
        inner ℝ (fixedTimeCellReconstruction T g hT (fun i => K (u i)))
          (fixedTimeCellReconstruction T g hT (fun i => E (φ i.castSucc)))-
        inner ℝ (E (y (Fin.last g.steps))) (E (φ (Fin.last g.steps))) := by
  have he := funext hbox
  subst hi
  subst T
  exact cartesian_forward_reconstructed_weak_identity lo δ hδ N ω g b u y φ hy

end Carleman
