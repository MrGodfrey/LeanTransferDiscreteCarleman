module

public import Carleman.Spatial.CartesianKuhnNormBounds
public import Carleman.Spatial.AffineSimplexNorm

/-! The actual L² reconstruction and load satisfy the original diagonal
mass estimates with constants depending only on the fixed dimension. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianKuhnReconstructionLp (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    Lp ℝ 2 (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) :=
  ((cartesianKuhnReconstruction_memLp o δ hδ N f).mono_measure Measure.restrict_le_self).toLp
    (cartesianKuhnReconstruction o δ hδ N f)

theorem cartesianKuhnReconstructionLp_ae (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianKuhnReconstructionLp o δ hδ N f
      =ᵐ[volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))]
        cartesianKuhnReconstruction o δ hδ N f :=
  ((cartesianKuhnReconstruction_memLp o δ hδ N f).mono_measure Measure.restrict_le_self).coeFn_toLp

theorem cartesianKuhnReconstructionLp_norm_sq (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    ‖cartesianKuhnReconstructionLp o δ hδ N f‖^2=
      ∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j), (cartesianKuhnReconstruction o δ hδ N f x)^2 := by
  rw [lp_two_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [cartesianKuhnReconstructionLp_ae o δ hδ N f] with x hx
  rw [hx,Real.norm_eq_abs,sq_abs]

theorem cartesianKuhnReconstructionLp_norm_sq_bounds (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    (d+2:ℝ)⁻¹*((∏ j, δ j)*(∑ a, (f a)^2)) ≤ ‖cartesianKuhnReconstructionLp o δ hδ N f‖^2 ∧
    ‖cartesianKuhnReconstructionLp o δ hδ N f‖^2 ≤ (∏ j, δ j)*(∑ a, (f a)^2) := by
  rw [cartesianKuhnReconstructionLp_norm_sq]
  exact cartesianKuhnReconstruction_sq_bounds o δ hδ N f

theorem cartesianKuhnLoadLiftLp_norm_sq_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    ‖cartesianKuhnLoadLiftLp o δ hδ N f‖^2 ≤ (d+2:ℝ)*((∏ j, δ j)*(∑ a, (f a)^2)) := by
  rw [lp_two_norm_sq_integral]
  have he : (∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j),
      ‖cartesianKuhnLoadLiftLp o δ hδ N f x‖^2)=
      (∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j), (cartesianKuhnLoadLift o δ hδ N f x)^2) := by
    apply integral_congr_ae
    filter_upwards [cartesianKuhnLoadLiftLp_ae o δ hδ N f] with x hx
    rw [hx,Real.norm_eq_abs,sq_abs]
  rw [he]
  exact cartesianKuhnLoadLift_sq_bound o δ hδ N f

end Carleman
