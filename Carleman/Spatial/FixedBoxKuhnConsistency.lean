module

public import Carleman.Spatial.CartesianCellKuhnConsistency
public import Carleman.Spatial.FixedBoxCellReconstruction

/-! The same actual Kuhn jet and cell error on a fixed physical box. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def cartesianBoxKuhnReconstructionJet (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (f : CartesianInteriorIndex N → ℝ) :
    WeakSobolevJet d 1 (volume.restrict (openCoordinateBox lo hi)) (openCoordinateBox lo hi) :=
  (funext hbox) ▸ cartesianKuhnReconstructionJet lo δ hδ N f

theorem cartesianBoxCell_kuhn_L2_consistency : ∃ C > (0:ℝ),
    ∀ (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
      (h : ℝ) (_hh : 0 ≤ h) (_hstep : ∀ j, δ j ≤ h) (f : CartesianPhysicalState δ hδ N),
      ‖cartesianBoxCellIsometry lo hi δ hδ N hbox f-
        WeakSobolevJet.value (cartesianBoxKuhnReconstructionJet lo hi δ hδ N hbox f)‖ ≤
        C*h*‖WeakSobolevJet.field 1 (cartesianBoxKuhnReconstructionJet lo hi δ hδ N hbox f)‖ := by
  obtain ⟨C,hC,hbound⟩ := cartesianCell_kuhn_L2_consistency (d := d)
  refine ⟨C,hC,?_⟩
  intro lo hi δ hδ N hbox h hh hstep f
  have he := funext hbox
  subst hi
  change ‖cartesianCellIsometry lo δ hδ N f-WeakSobolevJet.value (cartesianKuhnReconstructionJet lo δ hδ N f)‖ ≤ _
  rw [cartesianKuhnReconstructionJet_value]
  exact hbound lo δ hδ N h hh hstep f

end Carleman
