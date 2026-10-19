module

public import Carleman.Spatial.CartesianPhysicalSpaces
public import Carleman.Spatial.AllowedCartesianObservation

/-! The original observation inequality in the actual physical Hilbert
spaces, using the Hilbert adjoint of zero extension and its weighted norm. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}
attribute [local instance] Classical.propDecidable

theorem allowed_weight_cartesian_hilbert_observation
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (ω₀ ω : Set (SpatialCoordinates d)) (hω₀ : MeasurableSet ω₀)
    (hcompact₀ : IsCompact (closure ω₀)) (hω : IsOpen ω) (hinc : closure ω₀ ⊆ ω) :
    ∃ h₀ > (0:ℝ), ∃ C > (0:ℝ),
    ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hTS : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆ S)
      (h : ℝ), 0 < h → h ≤ h₀ → (∀ j, δ j ≤ h) →
    ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → h*w.q t ≤ 1 →
    ∀ f : CartesianPhysicalState δ hδ N,
      let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
      σ.observation ω₀ hω₀ (cartesianKuhnReconstructionLp o δ hδ N f) ≤
        C*‖cartesianPhysicalControlWeight o δ hδ N ω σ.value
          ((cartesianPhysicalControlExtension o δ hδ N ω).adjoint f)‖ := by
  obtain ⟨h₀,hh₀,C,hC,hbound⟩ := allowed_weight_cartesian_observation
    hS hc hcompact ρ hρ ω₀ ω hω₀ hcompact₀ hω hinc
  refine ⟨h₀,hh₀,C,hC,?_⟩
  intro o δ hδ N hTS h hh hmesh hstep w τ t η hη hsmall f
  let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
  have hb := hbound o δ hδ N hTS h hh hmesh hstep w τ t η hη hsmall f
  dsimp only at hb
  rw [cartesianPhysicalControl_adjoint]
  have he := cartesianPhysicalControlWeight_norm_sq o δ hδ N ω σ.value
    (cartesianPhysicalControlRestriction o δ hδ N ω f)
  change ‖cartesianPhysicalControlWeight o δ hδ N ω σ.value
    (cartesianPhysicalControlRestriction o δ hδ N ω f)‖^2=
    cartesianControlWeightedSq o δ N ω σ.value (cartesianControlRestriction o δ N ω f) at he
  rw [← he,Real.sqrt_sq (norm_nonneg _)] at hb
  exact hb

end Carleman
