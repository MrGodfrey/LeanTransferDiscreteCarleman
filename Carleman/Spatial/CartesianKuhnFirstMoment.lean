module

public import Carleman.Spatial.CartesianKuhnHatSymmetry
public import Mathlib.MeasureTheory.Group.Integral

/-! The actual interior-node hat has zero vector first moment. Compact
support and continuity supply genuine integrability before cancellation. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnHat_integrable (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    Integrable (cartesianKuhnHat o δ hδ N a) volume :=
  (cartesianKuhnHat_continuous o δ hδ N a ha).integrable_of_hasCompactSupport
    (cartesianKuhnHat_compact o δ hδ N a)

theorem cartesianKuhnHat_firstMoment_integrable (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    Integrable (fun x => cartesianKuhnHat o δ hδ N a x • (x-cartesianGridPoint o δ a)) volume :=
  ((cartesianKuhnHat_continuous o δ hδ N a ha).smul
    (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (cartesianKuhnHat_compact o δ hδ N a).smul_right

theorem cartesianKuhnHat_firstMoment_zero (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    (∫ x, cartesianKuhnHat o δ hδ N a x • (x-cartesianGridPoint o δ a))=0 := by
  let p := cartesianGridPoint o δ a
  let F := fun x => cartesianKuhnHat o δ hδ N a x • (x-p)
  have hr (x : SpatialCoordinates d) : p+p-x=AffineEquiv.pointReflection ℝ p x := by
    rw [AffineEquiv.pointReflection_apply]
    change p+p-x=(p-x)+p
    abel
  have he : (fun x => F (p+p-x))=(fun x => -F x) := by
    funext x
    change cartesianKuhnHat o δ hδ N a (p+p-x) • (p+p-x-p)=
      -(cartesianKuhnHat o δ hδ N a x • (x-p))
    have hv : p+p-x-p=-(x-p) := by abel
    rw [hv,hr,cartesianKuhnHat_reflection o δ hδ N a ha,smul_neg]
  have h := integral_sub_left_eq_self F volume (p+p)
  rw [he,integral_neg] at h
  apply PiLp.ext
  intro j
  have hj := congrArg (fun y : SpatialCoordinates d => y j) h
  change -(∫ x, F x) j=(∫ x, F x) j at hj
  change (∫ x, F x) j=0
  linarith

theorem cartesianKuhnHat_firstMoment_domain (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (a : Fin d → ℤ)
    (ha : cartesianGridPoint o δ a ∈ openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j)) :
    (∫ x in openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j),
      cartesianKuhnHat o δ hδ N a x • (x-cartesianGridPoint o δ a))=0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [cartesianKuhnHat_zero_compl o δ hδ N a ha hx,zero_smul])]
  exact cartesianKuhnHat_firstMoment_zero o δ hδ N a ha

end Carleman
