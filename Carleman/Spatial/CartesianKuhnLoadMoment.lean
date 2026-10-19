module

public import Carleman.Spatial.CartesianKuhnLoad

/-! The actual finite-grid load is a right inverse of the normalized
hat moments, on every interior node and for arbitrary nodal data. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem integral_cartesianKuhnLoad_mul_hat_cell (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (i : CartesianCellIndex N) :
    (∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
      cartesianKuhnLoad o δ hδ N f x*cartesianKuhnHat o δ hδ N a x)=
      f (cartesianGridPoint o δ a)*(∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
        cartesianKuhnHat o δ hδ N a x) := by
  classical
  let T := cartesianFiniteSimplex o δ hδ N i
  let c := cartesianKuhnLoadCoefficients o δ hδ N f i
  have he : (fun x => cartesianKuhnLoad o δ hδ N f x*cartesianKuhnHat o δ hδ N a x)
      =ᵐ[volume.restrict (simplicialCell T.points)]
      (fun x => simplexLoadPolynomial T c x*cartesianKuhnHat o δ hδ N a x) := by
    filter_upwards [cartesianKuhnLoad_on_cell o δ hδ N f i] with x hx
    rw [hx]
  rw [integral_congr_ae he]
  by_cases hv : cartesianGridPoint o δ a ∈ Set.range T.points
  · obtain ⟨k,hk⟩ := hv
    have hh : cartesianKuhnHat o δ hδ N a =ᵐ[volume.restrict (simplicialCell T.points)]
        simplexBarycentric T k := by
      filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
      exact cartesianKuhnHat_on_incidentCell o δ hδ N a i k hk.symm hx
    rw [integral_congr_ae (hh.mono (fun x hx => congrArg (fun v => simplexLoadPolynomial T c x*v) hx)),
      integral_simplexLoadPolynomial_barycentric,integral_congr_ae hh,integral_simplexBarycentric]
    have hc : c k=f (cartesianGridPoint o δ a) := by
      change (if T.points k ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) then f (T.points k) else 0)=_
      rw [hk,ite_eq_left ha]
    rw [hc]
  · have hh : cartesianKuhnHat o δ hδ N a =ᵐ[volume.restrict (simplicialCell T.points)] (fun _ => 0) := by
      filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
      exact cartesianKuhnHat_zero_on_nonincidentCell o δ hδ N a i hv hx
    rw [integral_congr_ae (hh.mono (fun x hx => congrArg (fun v => simplexLoadPolynomial T c x*v) hx)),
      integral_congr_ae hh]
    simp only [mul_zero,integral_zero]

theorem cartesianKuhnLoad_hat_integral_domain (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    (∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j),
      cartesianKuhnLoad o δ hδ N f x*cartesianKuhnHat o δ hδ N a x)=
      f (cartesianGridPoint o δ a)*(∏ j, δ j) := by
  let M := cartesianKuhnPartition o δ hδ N
  rw [M.integral_eq_sum_cells (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _) _
    (cartesianKuhnLoad_mul_hat_integrable o δ hδ N f a ha).integrableOn]
  change (∑ i : CartesianCellIndex N, ∫ x in simplicialCell (cartesianFiniteSimplex o δ hδ N i).points,
    cartesianKuhnLoad o δ hδ N f x*cartesianKuhnHat o δ hδ N a x)=_
  simp_rw [integral_cartesianKuhnLoad_mul_hat_cell o δ hδ N f a ha]
  rw [← Finset.mul_sum]
  have hm := M.integral_eq_sum_cells (openCoordinateBox_isOpen _ _) (openCoordinateBox_convex _ _)
    (cartesianKuhnHat o δ hδ N a) (cartesianKuhnHat_integrable o δ hδ N a ha).integrableOn
  rw [cartesianKuhnHat_mass_domain o δ hδ N a ha] at hm
  exact congrArg (fun r => f (cartesianGridPoint o δ a)*r) hm.symm

theorem cartesianKuhnLoad_moment_right_inverse (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : SpatialCoordinates d → ℝ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    (∏ j, δ j)⁻¹*(∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j),
      cartesianKuhnLoad o δ hδ N f x*cartesianKuhnHat o δ hδ N a x)=f (cartesianGridPoint o δ a) := by
  rw [cartesianKuhnLoad_hat_integral_domain o δ hδ N f a ha,mul_comm (f _)]
  exact inv_mul_cancel_left₀ (Finset.prod_pos (fun j _ => hδ j)).ne' _

end Carleman
