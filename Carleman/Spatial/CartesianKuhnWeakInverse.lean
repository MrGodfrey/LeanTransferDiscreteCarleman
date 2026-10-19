module

public import Carleman.Spatial.CartesianKuhnInverse
public import Carleman.Spatial.CartesianKuhnReconstructionJet
public import Carleman.Spatial.CartesianKuhnPatchProjection
public import Carleman.Continuous.BochnerNormAlgebra
public import Carleman.Continuous.NormDomination

/-! The actual weak gradient of R_h obeys the mesh-uniform inverse
estimate; the original Q_h then has a genuine local gradient stability bound. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnReconstruction_cell_norm (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N) :
    bochnerL2Norm (volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points))
      (cartesianKuhnReconstruction o δ hδ N f)=
      ‖simplexNodalLp (cartesianFiniteSimplex o δ hδ N i)
        (fun k => cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))‖ := by
  apply (bochnerL2Norm_congr_ae ?_).trans (bochnerL2Norm_coe _)
  filter_upwards [ae_restrict_mem (simplicialCell_measurable (cartesianFiniteSimplex o δ hδ N i).points),
    simplexNodalLp_ae (cartesianFiniteSimplex o δ hδ N i)
      (fun k => cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))] with x hx hp
  exact (cartesianKuhnReconstruction_on_cell o δ hδ N f i hx).trans hp.symm

theorem cartesianKuhnReconstructionJet_cell_gradient_norm (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N) :
    bochnerL2Norm (volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points))
      (WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f))=
      ‖simplexNodalGradientLp (cartesianFiniteSimplex o δ hδ N i)
        (fun k => cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))‖ :=
  (bochnerL2Norm_congr_ae ((cartesianKuhnReconstructionJet_gradient_on_cell o δ hδ N f i).trans
    (simplexNodalGradientLp_ae (cartesianFiniteSimplex o δ hδ N i)
      (fun k => cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))).symm)).trans
    (bochnerL2Norm_coe _)

theorem cartesianKuhnReconstruction_weak_inverse (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C > (0:ℝ), ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (i : CartesianCellIndex N) (h : ℝ), 0 < h → (∀ j, h/κ ≤ δ j) →
      ∀ f : CartesianInteriorIndex N → ℝ,
      bochnerL2Norm (volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points))
        (WeakSobolevJet.field 1 (cartesianKuhnReconstructionJet o δ hδ N f)) ≤
      (C/h)*bochnerL2Norm (volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points))
        (cartesianKuhnReconstruction o δ hδ N f) := by
  obtain ⟨C,hC,hbound⟩ := cartesianFiniteSimplex_uniform_inverse d κ hκ
  refine ⟨C,hC,?_⟩
  intro o δ hδ N i h hh hlower f
  rw [cartesianKuhnReconstructionJet_cell_gradient_norm,cartesianKuhnReconstruction_cell_norm]
  exact hbound o δ hδ N i h hh hlower _

def cartesianKuhnProjectionJet (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    WeakSobolevJet d 1 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))
      (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :=
  cartesianKuhnReconstructionJet o δ hδ N (cartesianKuhnMoment o δ hδ N u)

theorem cartesianKuhnProjectionJet_value (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)))) :
    WeakSobolevJet.value (cartesianKuhnProjectionJet o δ hδ N u)=cartesianKuhnProjectionLp o δ hδ N u :=
  cartesianKuhnReconstructionJet_value o δ hδ N _

theorem cartesianKuhnProjection_local_gradient_bound (d : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C > (0:ℝ), ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (i : CartesianCellIndex N) (h : ℝ), 0 < h → (∀ j, h/κ ≤ δ j) →
      ∀ u : Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))),
      bochnerL2Norm (volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points))
        (WeakSobolevJet.field 1 (cartesianKuhnProjectionJet o δ hδ N u)) ≤
      (C/h)*bochnerL2Norm (volume.restrict (cartesianClippedPatch o δ N i)) u := by
  obtain ⟨C,hC,hbound⟩ := cartesianKuhnReconstruction_weak_inverse d κ hκ
  refine ⟨C,hC,?_⟩
  intro o δ hδ N i h hh hlower u
  exact (hbound o δ hδ N i h hh hlower (cartesianKuhnMoment o δ hδ N u)).trans
    (mul_le_mul_of_nonneg_left (cartesianKuhnProjection_patch_norm_bound o δ hδ N u i) (div_nonneg hC.le hh.le))

end Carleman
