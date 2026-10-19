module

public import Carleman.Spatial.CartesianKuhnWeightedCell
public import Carleman.Spatial.CartesianKuhnLpNorm
public import Carleman.Spatial.WeightedScalarRepresentative

/-! Actual global weighted L² stability assembled through the exact
weighted diagonal mass, with one uniform cell comparison factor. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhn_weighted_norm_bounds (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ)
    (w : BoundedMultiplier (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))))
    (W : ℝ) (hW : 0 < W) (s : CartesianCellIndex N → ℝ) (hs : ∀ i, 0 < s i)
    (hω : ∀ i k, 0 ≤ w.value ((cartesianFiniteSimplex o δ hδ N i).points k))
    (hb : ∀ i k, w.value ((cartesianFiniteSimplex o δ hδ N i).points k) ≤ W*s i ∧
      s i ≤ W*w.value ((cartesianFiniteSimplex o δ hδ N i).points k))
    (hw : ∀ i, ∀ᵐ x ∂volume.restrict (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points),
      |w.value x| ≤ W*s i ∧ s i ≤ W*|w.value x|)
    (f : CartesianInteriorIndex N → ℝ) :
    let E := (∏ j, δ j)*(∑ a, (w.value (cartesianInteriorPoint o δ N a)*f a)^2)
    E ≤ W^4*(d+2:ℝ)*(w.seminorm (cartesianKuhnReconstructionLp o δ hδ N f))^2 ∧
    (w.seminorm (cartesianKuhnReconstructionLp o δ hδ N f))^2 ≤ W^4*E ∧
    (w.seminorm (cartesianKuhnLoadLiftLp o δ hδ N f))^2 ≤ W^4*(d+2:ℝ)*E := by
  dsimp only
  rw [w.seminorm_sq_scalar_ae _ _ (cartesianKuhnReconstructionLp_ae o δ hδ N f),
    w.seminorm_sq_scalar_ae _ _ (cartesianKuhnLoadLiftLp_ae o δ hδ N f)]
  have hiR := w.integrable_scalar_density_ae _ _ (cartesianKuhnReconstructionLp_ae o δ hδ N f)
  have hiL := w.integrable_scalar_density_ae _ _ (cartesianKuhnLoadLiftLp_ae o δ hδ N f)
  let M := cartesianKuhnPartition o δ hδ N
  rw [M.integral_eq_sum_cells (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) _ hiR,
    M.integral_eq_sum_cells (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) _ hiL]
  have hl := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (CartesianCellIndex N))) =>
    (cartesianKuhn_weighted_reconstruction_cell_bounds o δ hδ N f w i W (s i) hW (hs i) (hω i) (hb i) (hw i)).1)
  have hu := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (CartesianCellIndex N))) =>
    (cartesianKuhn_weighted_reconstruction_cell_bounds o δ hδ N f w i W (s i) hW (hs i) (hω i) (hb i) (hw i)).2)
  rw [cartesianKuhn_weighted_mass_assembly,← Finset.mul_sum] at hl
  rw [← Finset.mul_sum,cartesianKuhn_weighted_mass_assembly] at hu
  have hload := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (CartesianCellIndex N))) =>
    cartesianKuhn_weighted_load_cell_bound o δ hδ N f w i W (s i) hW (hs i) (hω i) (hb i) (hw i))
  have hr (i : CartesianCellIndex N) :
      W^4*(d+2:ℝ)*(volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ))*
        (∑ k, (w.value ((cartesianFiniteSimplex o δ hδ N i).points k)*
          cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))^2)=
      (W^4*(d+2:ℝ))*((volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ))*
        (∑ k, (w.value ((cartesianFiniteSimplex o δ hδ N i).points k)*
          cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))^2)) := by ring
  simp_rw [hr] at hload
  rw [← Finset.mul_sum,cartesianKuhn_weighted_mass_assembly] at hload
  exact ⟨hl,hu,hload⟩

end Carleman
