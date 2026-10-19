module

public import Carleman.Spatial.CartesianKuhnMass
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The actual normalized nodal moment reproduces every affine function
at every interior grid node, including the first layer next to the boundary. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnHat_affine_integrable (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    Integrable (fun x => p x * cartesianKuhnHat o δ hδ N a x) volume :=
  (p.continuous_of_finiteDimensional.mul (cartesianKuhnHat_continuous o δ hδ N a ha)).integrable_of_hasCompactSupport
    (cartesianKuhnHat_compact o δ hδ N a).mul_left

theorem cartesianKuhnHat_affine_integral (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    (∫ x, p x * cartesianKuhnHat o δ hδ N a x)=(∏ j, δ j)*p (cartesianGridPoint o δ a) := by
  let L := p.linear.toContinuousLinearMap
  let v := cartesianGridPoint o δ a
  let φ := cartesianKuhnHat o δ hδ N a
  have hlin (x : SpatialCoordinates d) : L (x-v)=p x-p v := p.linear_apply_vsub x v
  have he : (fun x => p x * φ x)=
      (fun x => φ x*p v+L (φ x • (x-v))) := by
    funext x
    rw [map_smul]
    change p x*φ x=φ x*p v+φ x*L (x-v)
    rw [hlin]
    ring
  have hi := cartesianKuhnHat_firstMoment_integrable o δ hδ N a ha
  rw [he,integral_add ((cartesianKuhnHat_integrable o δ hδ N a ha).mul_const _) (L.integrable_comp hi),
    integral_mul_const,L.integral_comp_comm hi]
  change (∫ x, cartesianKuhnHat o δ hδ N a x)*p v+
    L (∫ x, cartesianKuhnHat o δ hδ N a x • (x-cartesianGridPoint o δ a))=_
  rw [cartesianKuhnHat_mass o δ hδ N a ha,cartesianKuhnHat_firstMoment_zero o δ hδ N a ha,
    map_zero,add_zero]

theorem cartesianKuhnHat_affine_integral_domain (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    (∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j),
      p x * cartesianKuhnHat o δ hδ N a x)=(∏ j, δ j)*p (cartesianGridPoint o δ a) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [cartesianKuhnHat_zero_compl o δ hδ N a ha hx,mul_zero])]
  exact cartesianKuhnHat_affine_integral o δ hδ N a ha p

theorem cartesianKuhnHat_affine_moment (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j))
    (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) :
    (∏ j, δ j)⁻¹ * (∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j),
      p x * cartesianKuhnHat o δ hδ N a x)=p (cartesianGridPoint o δ a) := by
  rw [cartesianKuhnHat_affine_integral_domain o δ hδ N a ha p]
  have hd : (∏ j, δ j) ≠ 0 := (Finset.prod_pos (fun j _ => hδ j)).ne'
  exact inv_mul_cancel_left₀ hd _

end Carleman
