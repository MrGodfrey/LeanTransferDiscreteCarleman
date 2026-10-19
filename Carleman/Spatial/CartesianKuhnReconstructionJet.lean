module

public import Carleman.Spatial.CartesianKuhnLpNorm
public import Carleman.Spatial.SimplicialLocalGradient

/-! The actual Cartesian reconstruction belongs to the original H¹₀
closure and has the actual polynomial weak gradient on each physical cell. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnReconstruction_eq_nodal (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnReconstruction o δ hδ N f=
      (cartesianKuhnPartition o δ hδ N).nodalFunction (cartesianInteriorData o δ N f) := by
  classical
  funext x
  by_cases hx : ∃ i : CartesianCellIndex N, x ∈ simplicialCell (cartesianFiniteSimplex o δ hδ N i).points
  · obtain ⟨i,hi⟩ := hx
    rw [cartesianKuhnReconstruction_on_cell o δ hδ N f i hi,
      (cartesianKuhnPartition o δ hδ N).nodalFunction_on_cell (cartesianKuhnPartition_faceMatching o δ hδ N)
        (cartesianInteriorData o δ N f) i hi]
    rfl
  · have hn : x ∉ closure (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) := by
      rw [← (cartesianKuhnPartition o δ hδ N).cells_union]
      intro hm
      exact hx (mem_iUnion.mp hm)
    rw [(cartesianKuhnPartition o δ hδ N).nodalFunction_zero_outside _ hn]
    apply Finset.sum_eq_zero
    intro a _
    rw [cartesianKuhnHat,(cartesianKuhnPartition o δ hδ N).nodalFunction_zero_outside _ hn,mul_zero]

theorem cartesianKuhnReconstructionLp_eq_nodal (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnReconstructionLp o δ hδ N f=
      (cartesianKuhnPartition o δ hδ N).nodalLp (openCoordinateBox_isOpen _ _).measurableSet
        (cartesianKuhnPartition_faceMatching o δ hδ N) (cartesianInteriorData o δ N f) := by
  apply Lp.ext
  exact (cartesianKuhnReconstructionLp_ae o δ hδ N f).trans
    ((cartesianKuhnReconstruction_eq_nodal o δ hδ N f) ▸
      ((cartesianKuhnPartition o δ hδ N).nodalLp_ae (openCoordinateBox_isOpen _ _).measurableSet
        (cartesianKuhnPartition_faceMatching o δ hδ N) (cartesianInteriorData o δ N f)).symm)

theorem cartesianKuhnReconstructionLp_mem_dirichlet (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnReconstructionLp o δ hδ N f ∈
      dirichletSubspace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) := by
  rw [cartesianKuhnReconstructionLp_eq_nodal]
  apply (cartesianKuhnPartition o δ hδ N).nodalLp_mem_dirichletSubspace
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _)
    (cartesianKuhnPartition_faceMatching o δ hδ N) (cartesianKuhnPartition_boundaryFitted o δ hδ N)
  intro i k hk
  apply cartesianInteriorData_zero_compl o δ hδ N f
  exact fun hi => hk.2 ((openCoordinateBox_isOpen _ _).interior_eq.symm ▸ hi)

def cartesianKuhnReconstructionJet (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    WeakSobolevJet d 1 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
      (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :=
  (cartesianKuhnReconstructionLp_mem_dirichlet o δ hδ N f).choose

theorem cartesianKuhnReconstructionJet_value (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    WeakSobolevJet.value (cartesianKuhnReconstructionJet o δ hδ N f)=cartesianKuhnReconstructionLp o δ hδ N f :=
  (cartesianKuhnReconstructionLp_mem_dirichlet o δ hδ N f).choose_spec.2

theorem cartesianKuhnReconstructionJet_mem_dirichlet (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnReconstructionJet o δ hδ N f ∈
      dirichletJetSpace (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :=
  (cartesianKuhnReconstructionLp_mem_dirichlet o δ hδ N f).choose_spec.1

theorem cartesianKuhnReconstructionJet_gradient_on_cell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N) :
    WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f)
      =ᵐ[volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)]
      (fun x => derivativeOneFiber (fderiv ℝ (simplexNodalInterpolant (cartesianFiniteSimplex o δ hδ N i)
        (fun k => cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))) x)) := by
  apply (cartesianKuhnPartition o δ hδ N).gradient_on_cell
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _)
  rw [cartesianKuhnReconstructionJet_value]
  filter_upwards [cartesianKuhnReconstructionLp_ae o δ hδ N f] with x hx
  intro hi
  rw [hx,cartesianKuhnReconstruction_on_cell o δ hδ N f i hi]

end Carleman
