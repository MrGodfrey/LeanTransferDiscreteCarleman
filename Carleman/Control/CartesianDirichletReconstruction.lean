module

public import Carleman.Control.DirichletTimeWeakCompactness
public import Carleman.Spatial.FixedBoxKuhnConsistency
public import Carleman.Spatial.CartesianPhysicalStability

/-! The original Kuhn state, as an element of the actual fixed-box H¹₀ energy space. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

def cartesianBoxDirichletState (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (f : CartesianPhysicalState δ hδ N) : DirichletEnergyState (openCoordinateBox lo hi) :=
  ⟨SobolevHilbert.ofJet (cartesianBoxKuhnReconstructionJet lo hi δ hδ N hbox f), by
    have he := funext hbox
    subst hi
    change WeakSobolevJet.value (cartesianKuhnReconstructionJet lo δ hδ N f) ∈
      dirichletSubspace (openCoordinateBox lo (fun j => lo j+(N j:ℝ)*δ j))
    rw [cartesianKuhnReconstructionJet_value]
    exact cartesianKuhnReconstructionLp_mem_dirichlet lo δ hδ N f⟩

theorem cartesianBoxDirichletState_value (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (f : CartesianPhysicalState δ hδ N) :
    dirichletStateValue (openCoordinateBox lo hi) (cartesianBoxDirichletState lo hi δ hδ N hbox f)=
      WeakSobolevJet.value (cartesianBoxKuhnReconstructionJet lo hi δ hδ N hbox f) := rfl

theorem cartesianBoxDirichletState_gradient (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (f : CartesianPhysicalState δ hδ N) :
    dirichletStateGradient (openCoordinateBox lo hi) (cartesianBoxDirichletState lo hi δ hδ N hbox f)=
      WeakSobolevJet.field 1 (cartesianBoxKuhnReconstructionJet lo hi δ hδ N hbox f) := rfl

theorem cartesianBoxDirichletState_value_norm_le (lo hi δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (hbox : ∀ j, lo j+(N j:ℝ)*δ j=hi j)
    (f : CartesianPhysicalState δ hδ N) :
    ‖dirichletStateValue (openCoordinateBox lo hi) (cartesianBoxDirichletState lo hi δ hδ N hbox f)‖ ≤ ‖f‖ := by
  have he := funext hbox
  subst hi
  rw [cartesianBoxDirichletState_value]
  change ‖WeakSobolevJet.value (cartesianKuhnReconstructionJet lo δ hδ N f)‖ ≤ ‖f‖
  rw [cartesianKuhnReconstructionJet_value]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hh := (cartesianReconstruction_norm_sq_bounds lo δ hδ N f).2
  rwa [cartesianReconstruction_RH] at hh

theorem timeCellReconstruction_norm_sq_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : TimeGrid) (u : Fin g.steps → H) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ‖u i‖ ≤ B) :
    ‖timeCellReconstruction g u‖^2 ≤ g.period*B^2 := by
  rw [← real_inner_self_eq_norm_sq,timeCellReconstruction_inner]
  simp only [real_inner_self_eq_norm_sq]
  calc
    _ ≤ g.dt*∑ _i : Fin g.steps, B^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb i))) g.dt_pos.le
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,TimeGrid.period]; ring

theorem fixedTimeCellReconstruction_norm_sq_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : ℝ) (g : TimeGrid) (hT : g.period=T) (u : Fin g.steps → H)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ‖u i‖ ≤ B) :
    ‖fixedTimeCellReconstruction T g hT u‖^2 ≤ T*B^2 := by
  subst T
  exact timeCellReconstruction_norm_sq_le g u hB hb

end Carleman
