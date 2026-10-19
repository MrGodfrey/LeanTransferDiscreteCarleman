module

public import Carleman.Spatial.CartesianKuhnMassAssembly
public import Carleman.Spatial.SimplexLoadNorm

/-! Mesh-independent unweighted reconstruction and load estimates in the
actual domain, using the exact diagonal physical nodal mass. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnReconstruction_cell_sq_bounds (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N) :
    let T := cartesianFiniteSimplex o δ hδ N i
    let E := (volume.real (simplicialCell T.points)/(d+1:ℝ))*
      (∑ k, (cartesianInteriorData o δ N f (T.points k))^2)
    (d+2:ℝ)⁻¹*E ≤ (∫ x in simplicialCell T.points, (cartesianKuhnReconstruction o δ hδ N f x)^2) ∧
    (∫ x in simplicialCell T.points, (cartesianKuhnReconstruction o δ hδ N f x)^2) ≤ E := by
  dsimp only
  let T := cartesianFiniteSimplex o δ hδ N i
  have he : (∫ x in simplicialCell T.points, (cartesianKuhnReconstruction o δ hδ N f x)^2)=
      (∫ x in simplicialCell T.points,
        (simplexNodalInterpolant T (fun k => cartesianInteriorData o δ N f (T.points k)) x)^2) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
    rw [cartesianKuhnReconstruction_on_cell o δ hδ N f i hx]
  rw [he]
  have h := integral_simplexNodalInterpolant_sq_bounds T (fun k => cartesianInteriorData o δ N f (T.points k))
  have hd1 : (d+1:ℝ) ≠ 0 := by positivity
  have hd2 : (d+2:ℝ) ≠ 0 := by positivity
  constructor
  · calc
      _ = volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*
          (∑ k, (cartesianInteriorData o δ N f (T.points k))^2) := by
        dsimp only [T]
        field_simp
      _ ≤ _ := h.1
  · calc
      _ ≤ volume.real (simplicialCell T.points)/((d+1:ℝ)*(d+2))*(d+2)*
          (∑ k, (cartesianInteriorData o δ N f (T.points k))^2) := h.2
      _ = _ := by
        dsimp only [T]
        field_simp

theorem cartesianKuhnReconstruction_sq_bounds (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    (d+2:ℝ)⁻¹*((∏ j, δ j)*(∑ a, (f a)^2)) ≤
      (∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j), (cartesianKuhnReconstruction o δ hδ N f x)^2) ∧
    (∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j), (cartesianKuhnReconstruction o δ hδ N f x)^2) ≤
      (∏ j, δ j)*(∑ a, (f a)^2) := by
  rw [(cartesianKuhnPartition o δ hδ N).integral_eq_sum_cells
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) _
    (cartesianKuhnReconstruction_sq_integrable o δ hδ N f).integrableOn]
  have hl := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (CartesianCellIndex N))) =>
    (cartesianKuhnReconstruction_cell_sq_bounds o δ hδ N f i).1)
  have hu := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (CartesianCellIndex N))) =>
    (cartesianKuhnReconstruction_cell_sq_bounds o δ hδ N f i).2)
  rw [← Finset.mul_sum,cartesianKuhn_vertex_mass_sq_assembly] at hl
  rw [cartesianKuhn_vertex_mass_sq_assembly] at hu
  exact ⟨hl,hu⟩

theorem cartesianKuhnLoadLift_cell_sq_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N) :
    (∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
      (cartesianKuhnLoadLift o δ hδ N f x)^2) ≤
      (d+2:ℝ)*(volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ))*
      (∑ k, (cartesianInteriorData o δ N f ((cartesianFiniteSimplex o δ hδ N i).points k))^2) := by
  have he := integral_congr_ae ((cartesianKuhnLoad_on_cell o δ hδ N (cartesianInteriorData o δ N f) i).fun_comp
    (fun r => r^2))
  simp only [Function.comp_apply] at he
  change (∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
    (cartesianKuhnLoad o δ hδ N (cartesianInteriorData o δ N f) x)^2) ≤ _
  rw [he]
  have h := integral_simplexLoadPolynomial_sq_le (cartesianFiniteSimplex o δ hδ N i)
    (cartesianKuhnLoadCoefficients o δ hδ N (cartesianInteriorData o δ N f) i)
  simpa only [cartesianKuhnLoadCoefficients_interiorData] using h

theorem cartesianKuhnLoadLift_sq_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) :
    (∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j), (cartesianKuhnLoadLift o δ hδ N f x)^2) ≤
      (d+2:ℝ)*((∏ j, δ j)*(∑ a, (f a)^2)) := by
  have hi : Integrable (fun x => (cartesianKuhnLoadLift o δ hδ N f x)^2)
      (volume.restrict (openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))) := by
    convert (cartesianKuhnLoadLift_memLp o δ hδ N f).integrable_mul
      (cartesianKuhnLoadLift_memLp o δ hδ N f) using 1
    funext x
    exact sq _
  rw [(cartesianKuhnPartition o δ hδ N).integral_eq_sum_cells
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) _ hi]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (CartesianCellIndex N))) =>
    cartesianKuhnLoadLift_cell_sq_bound o δ hδ N f i)
  simp only [mul_assoc] at h
  rw [← Finset.mul_sum,cartesianKuhn_vertex_mass_sq_assembly] at h
  exact h

end Carleman
