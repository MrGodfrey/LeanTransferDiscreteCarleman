module

public import Carleman.Spatial.KuhnNodalGradient
public import Carleman.Spatial.CartesianKuhnReconstructionJet
public import Carleman.Spatial.DirichletScalarForm

/-! The original Dirichlet form of the actual reconstruction is exactly a
sum of physical cell volumes times adjacent-node difference products.
The remaining edge enumeration and discrete summation by parts are separate. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianKuhnCellDifference (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (f : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N) (k : Fin d) : ℝ :=
  (cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k.succ)-
    cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k.castSucc))/δ (i.2 k)

theorem cartesianKuhnReconstructionJet_coordinate_on_cell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N) (k : Fin d) :
    (fun x => WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f) x
      (Sym.oneEquiv (i.2 k))) =ᵐ[volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)]
      (fun _ => cartesianKuhnCellDifference o δ hδ N f i k) := by
  filter_upwards [cartesianKuhnReconstructionJet_gradient_on_cell o δ hδ N f i] with x hx
  rw [hx]
  change fderiv ℝ (simplexNodalInterpolant (cartesianFiniteSimplex o δ hδ N i)
    (fun l => cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points l))) x
      (EuclideanSpace.basisFun (Fin d) ℝ (Sym.oneEquiv.symm (Sym.oneEquiv (i.2 k))))=_
  rw [Equiv.symm_apply_apply]
  exact cartesianKuhnNodalDerivative_basis o δ hδ _ i.2 _ x k

theorem cartesianKuhnReconstructionJet_cell_energy (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f g : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N) :
    (∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
      inner ℝ (WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f) x)
        (WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N g) x))=
      volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)*
        ∑ k : Fin d, cartesianKuhnCellDifference o δ hδ N f i k*cartesianKuhnCellDifference o δ hδ N g i k := by
  calc
    _ = ∫ _x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
        ∑ k : Fin d, cartesianKuhnCellDifference o δ hδ N f i k*cartesianKuhnCellDifference o δ hδ N g i k := by
      apply integral_congr_ae
      filter_upwards [cartesianKuhnReconstructionJet_gradient_on_cell o δ hδ N f i,
        cartesianKuhnReconstructionJet_gradient_on_cell o δ hδ N g i] with x hf hg
      rw [hf,hg]
      exact cartesianKuhnNodalGradient_inner o δ hδ _ i.2 _ _ x
    _ = _ := by simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]

theorem cartesianKuhnReconstruction_weakGradientPairing_cells (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f g : CartesianInteriorIndex N → ℝ) :
    weakGradientPairing (cartesianKuhnReconstructionJet o δ hδ N f) (cartesianKuhnReconstructionJet o δ hδ N g)=
      ∑ i : CartesianCellIndex N, volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)*
        ∑ k : Fin d, cartesianKuhnCellDifference o δ hδ N f i k*cartesianKuhnCellDifference o δ hδ N g i k := by
  rw [weakGradientPairing_apply,L2.inner_def,
    (cartesianKuhnPartition o δ hδ N).integral_eq_sum_cells (openCoordinateBox_isOpen _ _)
      (openCoordinateBox_convex _ _) _ (L2.integrable_inner _ _)]
  exact Finset.sum_congr rfl (fun i _ => cartesianKuhnReconstructionJet_cell_energy o δ hδ N f g i)

theorem cartesianKuhnReconstruction_scalarForm_cells (hd : 0 < d)
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (f g : CartesianInteriorIndex N → ℝ) :
    (boundedDirichletOriginalForm (openCoordinateBox_isOpen _ _) hd
      (openCoordinateBox_isBounded o (fun j => o j+(N j:ℝ)*δ j))).scalarForm
      ⟨cartesianKuhnReconstructionLp o δ hδ N f,cartesianKuhnReconstructionLp_mem_dirichlet o δ hδ N f⟩
      ⟨cartesianKuhnReconstructionLp o δ hδ N g,cartesianKuhnReconstructionLp_mem_dirichlet o δ hδ N g⟩=
      ∑ i : CartesianCellIndex N, volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)*
        ∑ k : Fin d, cartesianKuhnCellDifference o δ hδ N f i k*cartesianKuhnCellDifference o δ hδ N g i k := by
  refine (dirichlet_scalarForm_eq (openCoordinateBox_isOpen _ _) hd (openCoordinateBox_isBounded _ _) _ _
    (cartesianKuhnReconstructionJet o δ hδ N f) (cartesianKuhnReconstructionJet o δ hδ N g)
    (cartesianKuhnReconstructionJet_value o δ hδ N f) (cartesianKuhnReconstructionJet_value o δ hδ N g)).trans ?_
  exact cartesianKuhnReconstruction_weakGradientPairing_cells o δ hδ N f g

end Carleman
