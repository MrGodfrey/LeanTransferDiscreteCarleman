module

public import Carleman.Geometry.KuhnCellVolume
public import Carleman.Geometry.KuhnNodeIncidence
public import Carleman.Spatial.CartesianKuhnFirstMoment
public import Carleman.Spatial.SimplexBarycentricDistribution

/-! Exact zeroth moment of the actual finite-domain interior-node hat.
The true incidence sum reduces to one complete Cartesian box volume. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem integral_cartesianKuhnHat_cell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ) (i : CartesianCellIndex N) :
    (∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points, cartesianKuhnHat o δ hδ N a x)=
      ∑ k : Fin (d+1), if (cartesianFiniteSimplex o δ hδ N i).points k=cartesianGridPoint o δ a
      then volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)/(d+1:ℝ) else 0 := by
  let T := cartesianFiniteSimplex o δ hδ N i
  calc
    _ = ∫ x in simplicialCell T.points, ∑ k : Fin (d+1),
        if T.points k=cartesianGridPoint o δ a then simplexBarycentric T k x else 0 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
      exact cartesianKuhnHat_on_cell o δ hδ N a i hx
    _ = ∑ k : Fin (d+1), ∫ x in simplicialCell T.points,
        if T.points k=cartesianGridPoint o δ a then simplexBarycentric T k x else 0 := by
      apply integral_finsetSum
      intro k _
      split_ifs
      · exact (simplexBarycentric T k).continuous_of_finiteDimensional.continuousOn.integrableOn_compact
          (simplicialCell_compact _)
      · exact integrable_zero _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      change (∫ x in simplicialCell T.points,
        if T.points k=cartesianGridPoint o δ a then simplexBarycentric T k x else 0)=
        if T.points k=cartesianGridPoint o δ a then volume.real (simplicialCell T.points)/(d+1:ℝ) else 0
      split_ifs
      · exact integral_simplexBarycentric T k
      · exact integral_zero _ _

theorem cartesianKuhnHat_mass_domain (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    (∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j), cartesianKuhnHat o δ hδ N a x)=
      ∏ j, δ j := by
  rw [(cartesianKuhnPartition o δ hδ N).integral_eq_sum_cells
    (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) _
    (cartesianKuhnHat_integrable o δ hδ N a ha).integrableOn]
  change (∑ i : CartesianCellIndex N, ∫ x in
    simplicialCell (cartesianFiniteSimplex o δ hδ N i).points, cartesianKuhnHat o δ hδ N a x)=_
  simp_rw [integral_cartesianKuhnHat_cell]
  have hv (i : CartesianCellIndex N) :
      volume.real (simplicialCell (cartesianFiniteSimplex o δ hδ N i).points)=
      volume.real (simplicialCell (cartesianKuhnSimplex o δ hδ 0 i.2).points) :=
    cartesianKuhnSimplex_volume_translation o δ hδ _ i.2
  simp_rw [hv]
  rw [cartesianKuhn_node_incidence_sum o δ hδ N a ha
    (fun π => volume.real (simplicialCell (cartesianKuhnSimplex o δ hδ 0 π).points)/(d+1:ℝ))]
  have he (π : Equiv.Perm (Fin d)) : (d+1:ℝ)*
      (volume.real (simplicialCell (cartesianKuhnSimplex o δ hδ 0 π).points)/(d+1:ℝ))=
      volume.real (simplicialCell (cartesianKuhnSimplex o δ hδ 0 π).points) := by
    have hd : (d+1:ℝ) ≠ 0 := by positivity
    field_simp
  simp_rw [he]
  exact cartesianKuhnSimplex_sum_permutation_volume o δ hδ

theorem cartesianKuhnHat_mass (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    (∫ x, cartesianKuhnHat o δ hδ N a x)=∏ j, δ j := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => cartesianKuhnHat_zero_compl o δ hδ N a ha hx)]
  exact cartesianKuhnHat_mass_domain o δ hδ N a ha

end Carleman
