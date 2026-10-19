module

public import Carleman.Spatial.CartesianPhysicalTest
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-! The prescribed physical weighted norms, as actual seminorms used by the
transfer interface. Positivity and weight homogeneity are proved explicitly. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

def cartesianStateSeminorm (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (σ : SpatialCoordinates d → ℝ) : Seminorm ℝ (CartesianPhysicalState δ hδ N) :=
  (normSeminorm ℝ (CartesianPhysicalState δ hδ N)).comp
    (cartesianPhysicalStateWeight o δ hδ N σ).toLinearMap

def cartesianControlSeminorm (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (ω : Set (SpatialCoordinates d)) (σ : SpatialCoordinates d → ℝ) :
    Seminorm ℝ (CartesianPhysicalControl o δ hδ N ω) :=
  (normSeminorm ℝ (CartesianPhysicalControl o δ hδ N ω)).comp
    (cartesianPhysicalControlWeight o δ hδ N ω σ).toLinearMap

theorem cartesianStateSeminorm_apply (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (σ : SpatialCoordinates d → ℝ) (f : CartesianPhysicalState δ hδ N) :
    cartesianStateSeminorm o δ hδ N σ f=‖cartesianPhysicalStateWeight o δ hδ N σ f‖ := rfl

theorem cartesianControlSeminorm_apply (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (σ : SpatialCoordinates d → ℝ)
    (f : CartesianPhysicalControl o δ hδ N ω) :
    cartesianControlSeminorm o δ hδ N ω σ f=‖cartesianPhysicalControlWeight o δ hδ N ω σ f‖ := rfl

theorem cartesianStateSeminorm_definite (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (σ : SpatialCoordinates d → ℝ)
    (hσ : ∀ a : CartesianInteriorIndex N, σ (cartesianInteriorPoint o δ N a) ≠ 0)
    (f : CartesianPhysicalState δ hδ N) : cartesianStateSeminorm o δ hδ N σ f=0 ↔ f=0 := by
  rw [cartesianStateSeminorm_apply,norm_eq_zero]
  constructor
  · intro he
    apply PhysicalFiniteSpace.valuesEquiv.injective
    funext a
    have ha := congrArg (fun z : CartesianPhysicalState δ hδ N => z a) he
    change σ (cartesianInteriorPoint o δ N a)*f a=0 at ha
    exact (mul_eq_zero.mp ha).resolve_left (hσ a)
  · rintro rfl
    exact map_zero _

theorem cartesianControlSeminorm_definite (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (σ : SpatialCoordinates d → ℝ)
    (hσ : ∀ a : CartesianObservationIndex o δ N ω, σ (cartesianInteriorPoint o δ N a.val) ≠ 0)
    (f : CartesianPhysicalControl o δ hδ N ω) :
    cartesianControlSeminorm o δ hδ N ω σ f=0 ↔ f=0 := by
  rw [cartesianControlSeminorm_apply,norm_eq_zero]
  constructor
  · intro he
    apply PhysicalFiniteSpace.valuesEquiv.injective
    funext a
    have ha := congrArg (fun z : CartesianPhysicalControl o δ hδ N ω => z a) he
    change σ (cartesianInteriorPoint o δ N a.val)*f a=0 at ha
    exact (mul_eq_zero.mp ha).resolve_left (hσ a)
  · rintro rfl
    exact map_zero _

theorem cartesianStateSeminorm_weight_scale (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (σ : SpatialCoordinates d → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (f : CartesianPhysicalState δ hδ N) :
    cartesianStateSeminorm o δ hδ N (fun x => r*σ x) f=r*cartesianStateSeminorm o δ hδ N σ f := by
  have he : cartesianPhysicalStateWeight o δ hδ N (fun x => r*σ x) f=
      r • cartesianPhysicalStateWeight o δ hδ N σ f := by
    apply PhysicalFiniteSpace.valuesEquiv.injective
    funext a
    change (r*σ (cartesianInteriorPoint o δ N a))*f a=r*(σ (cartesianInteriorPoint o δ N a)*f a)
    ring
  rw [cartesianStateSeminorm_apply,he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  rfl

theorem cartesianControlSeminorm_weight_scale (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ω : Set (SpatialCoordinates d)) (σ : SpatialCoordinates d → ℝ)
    (r : ℝ) (hr : 0 ≤ r) (f : CartesianPhysicalControl o δ hδ N ω) :
    cartesianControlSeminorm o δ hδ N ω (fun x => r*σ x) f=
      r*cartesianControlSeminorm o δ hδ N ω σ f := by
  have he : cartesianPhysicalControlWeight o δ hδ N ω (fun x => r*σ x) f=
      r • cartesianPhysicalControlWeight o δ hδ N ω σ f := by
    apply PhysicalFiniteSpace.valuesEquiv.injective
    funext a
    change (r*σ (cartesianInteriorPoint o δ N a.val))*f a=r*(σ (cartesianInteriorPoint o δ N a.val)*f a)
    ring
  rw [cartesianControlSeminorm_apply,he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  rfl

theorem cartesianPhysicalTest_positive (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) (w : TimeWeight) (τ η t : ℝ)
    (f : CartesianPhysicalState δ hδ N) (hf : f ≠ 0) :
    0 < inner ℝ f (cartesianPhysicalTest o δ hδ N ρ w τ η t f) := by
  rw [cartesianPhysicalTest_pairing]
  have hpos (a : CartesianInteriorIndex N) :
      TimeWeightRegularity.allowedWeight (w := w) τ (η*ρ (cartesianInteriorPoint o δ N a)) t ≠ 0 :=
    (TimeWeightRegularity.allowedWeight_pos _ _ _).ne'
  apply lt_of_le_of_ne (cartesianWeightedNodeEnergy_nonneg o δ hδ N _ _) (Ne.symm _)
  intro he
  apply hf
  apply PhysicalFiniteSpace.valuesEquiv.injective
  exact (cartesianWeightedNodeEnergy_eq_zero_iff o δ hδ N _ hpos (fun a => f a)).mp he

end Carleman
