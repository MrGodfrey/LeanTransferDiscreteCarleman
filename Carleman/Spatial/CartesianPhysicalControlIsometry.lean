module

public import Carleman.Spatial.CartesianPhysicalNorms

/-! Exact preservation of the physical control norm under the actual nodal zero extension. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem cartesianPhysicalControl_adjoint_extension (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (v : CartesianPhysicalControl o δ hδ N ω) :
    (cartesianPhysicalControlExtension o δ hδ N ω).adjoint
      (cartesianPhysicalControlExtension o δ hδ N ω v) = v := by
  rw [cartesianPhysicalControl_adjoint]
  apply PhysicalFiniteSpace.valuesEquiv.injective
  exact cartesianControlRestriction_extension o δ N ω v

theorem cartesianPhysicalControlExtension_norm (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (v : CartesianPhysicalControl o δ hδ N ω) :
    ‖cartesianPhysicalControlExtension o δ hδ N ω v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,
    ← ContinuousLinearMap.adjoint_inner_right,cartesianPhysicalControl_adjoint_extension]

theorem cartesianPhysicalControlExtension_weight (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (σ : SpatialCoordinates d → ℝ)
    (v : CartesianPhysicalControl o δ hδ N ω) :
    cartesianPhysicalStateWeight o δ hδ N σ (cartesianPhysicalControlExtension o δ hδ N ω v) =
      cartesianPhysicalControlExtension o δ hδ N ω (cartesianPhysicalControlWeight o δ hδ N ω σ v) := by
  apply PhysicalFiniteSpace.valuesEquiv.injective
  funext a
  change σ (cartesianInteriorPoint o δ N a) *
      (if ha : cartesianInteriorPoint o δ N a ∈ ω then v ⟨a,ha⟩ else 0) =
    (if ha : cartesianInteriorPoint o δ N a ∈ ω then
      σ (cartesianInteriorPoint o δ N a)*v ⟨a,ha⟩ else 0)
  split_ifs <;> simp

theorem cartesianPhysicalControlExtension_seminorm (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (σ : SpatialCoordinates d → ℝ)
    (v : CartesianPhysicalControl o δ hδ N ω) :
    cartesianStateSeminorm o δ hδ N σ (cartesianPhysicalControlExtension o δ hδ N ω v) =
      cartesianControlSeminorm o δ hδ N ω σ v := by
  rw [cartesianStateSeminorm_apply,cartesianControlSeminorm_apply,
    cartesianPhysicalControlExtension_weight,cartesianPhysicalControlExtension_norm]

end Carleman
