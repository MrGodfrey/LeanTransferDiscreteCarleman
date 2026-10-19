module

public import Carleman.Spatial.PhysicalFiniteDiagonal
public import Carleman.Spatial.CartesianReconstructionInterface
public import Carleman.Spatial.AllowedCartesianTestTime
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The original squared-weight test on the actual physical Hilbert space,
including its genuine operator-norm derivative. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def cartesianPhysicalTest (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (ρ : SpatialCoordinates d → ℝ) (w : TimeWeight) (τ η t : ℝ) :
    CartesianPhysicalState δ hδ N →L[ℝ] CartesianPhysicalState δ hδ N :=
  PhysicalFiniteSpace.multiplierFamily (fun a =>
    (TimeWeightRegularity.allowedWeight (w := w) τ (η*ρ (cartesianInteriorPoint o δ N a)) t)^2)

def cartesianPhysicalTestDerivative (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) {w : TimeWeight} {g : TimeGrid}
    {β : ℝ} (H : TimeWeightRegularity w g β) (τ η t : ℝ) :
    CartesianPhysicalState δ hδ N →L[ℝ] CartesianPhysicalState δ hδ N :=
  PhysicalFiniteSpace.multiplierFamily (fun a =>
    2*(TimeWeightRegularity.allowedWeight (w := w) τ (η*ρ (cartesianInteriorPoint o δ N a)) t)^2*
      (τ*(H.derivative t/w.q t)+(η*ρ (cartesianInteriorPoint o δ N a))*H.derivative t))

theorem cartesianPhysicalTest_values (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) (w : TimeWeight) (τ η t : ℝ)
    (f : CartesianPhysicalState δ hδ N) :
    ⇑(cartesianPhysicalTest o δ hδ N ρ w τ η t f)=
      cartesianAllowedTestOperator o δ N ρ w τ η t (fun a => f a) := rfl

theorem cartesianPhysicalTestDerivative_values (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) {w : TimeWeight} {g : TimeGrid}
    {β : ℝ} (H : TimeWeightRegularity w g β) (τ η t : ℝ)
    (f : CartesianPhysicalState δ hδ N) :
    ⇑(cartesianPhysicalTestDerivative o δ hδ N ρ H τ η t f)=
      cartesianAllowedTestDerivative o δ N ρ H τ η t (fun a => f a) := rfl

theorem cartesianPhysicalTest_hasDerivWithinAt (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) {w : TimeWeight} {g : TimeGrid}
    {β : ℝ} (H : TimeWeightRegularity w g β) (τ η : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    HasDerivWithinAt (cartesianPhysicalTest o δ hδ N ρ w τ η)
      (cartesianPhysicalTestDerivative o δ hδ N ρ H τ η t) (Icc 0 g.period) t := by
  apply PhysicalFiniteSpace.multiplierFamily_hasDerivWithinAt
  intro a
  convert (H.hasDerivWithinAt_allowedWeight τ (η*ρ (cartesianInteriorPoint o δ N a)) ht).pow 2 using 1
  ring

theorem cartesianPhysicalTest_pairing_hasDerivWithinAt (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) {w : TimeWeight} {g : TimeGrid}
    {β : ℝ} (H : TimeWeightRegularity w g β) (τ η : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period)
    (f : CartesianPhysicalState δ hδ N) :
    HasDerivWithinAt (fun s => inner ℝ f (cartesianPhysicalTest o δ hδ N ρ w τ η s f))
      (inner ℝ f (cartesianPhysicalTestDerivative o δ hδ N ρ H τ η t f)) (Icc 0 g.period) t := by
  have hp := (cartesianPhysicalTest_hasDerivWithinAt o δ hδ N ρ H τ η ht).clm_apply
    (hasDerivWithinAt_const t (Icc 0 g.period) f)
  have hi := (hasDerivWithinAt_const t (Icc 0 g.period) f).inner ℝ hp
  simpa only [map_zero,zero_add,inner_zero_left,add_zero] using hi

theorem cartesianPhysicalTest_endpoint (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) {w : TimeWeight} {g : TimeGrid}
    {β : ℝ} (H : TimeWeightRegularity w g β) (τ η : ℝ) :
    cartesianPhysicalTest o δ hδ N ρ w τ η 0=
      cartesianPhysicalTest o δ hδ N ρ w τ η g.period := by
  unfold cartesianPhysicalTest TimeWeightRegularity.allowedWeight
  rw [H.endpoint]

theorem cartesianPhysicalTest_symmetric (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) (w : TimeWeight) (τ η t : ℝ)
    (f z : CartesianPhysicalState δ hδ N) :
    inner ℝ f (cartesianPhysicalTest o δ hδ N ρ w τ η t z)=
      inner ℝ z (cartesianPhysicalTest o δ hδ N ρ w τ η t f) := by
  rw [PhysicalFiniteSpace.inner_eq,PhysicalFiniteSpace.inner_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change f a*(_*z a)=z a*(_*f a)
  ring

theorem cartesianPhysicalTest_pairing (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) (w : TimeWeight) (τ η t : ℝ)
    (f : CartesianPhysicalState δ hδ N) :
    inner ℝ f (cartesianPhysicalTest o δ hδ N ρ w τ η t f)=
      cartesianWeightedNodeEnergy o δ N
        (fun x => TimeWeightRegularity.allowedWeight (w := w) τ (η*ρ x) t) (fun a => f a) := by
  rw [cartesianPhysicalState_inner]
  change cartesianPhysicalInner δ N (fun a => f a)
    (cartesianSquaredWeightTest o δ N
      (fun x => TimeWeightRegularity.allowedWeight (w := w) τ (η*ρ x) t) (fun a => f a))=_
  exact cartesianSquaredWeightTest_pairing o δ N _ (fun a => f a)

theorem cartesianPhysicalTest_nonneg (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) (w : TimeWeight) (τ η t : ℝ)
    (f : CartesianPhysicalState δ hδ N) :
    0 ≤ inner ℝ f (cartesianPhysicalTest o δ hδ N ρ w τ η t f) := by
  rw [cartesianPhysicalTest_pairing]
  exact cartesianWeightedNodeEnergy_nonneg o δ hδ N _ _

end Carleman
