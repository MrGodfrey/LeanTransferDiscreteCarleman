module

public import Carleman.Spatial.FiniteDiagonalOperator
public import Carleman.Weights.TemporalDerivatives

/-! The original allowed diagonal test as an actual operator-valued path,
its operator-norm time derivative, endpoint matching, and physical pairing bound. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def cartesianAllowedTestOperator (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ρ : SpatialCoordinates d → ℝ) (w : TimeWeight) (τ η t : ℝ) :
    (CartesianInteriorIndex N → ℝ) →L[ℝ] (CartesianInteriorIndex N → ℝ) :=
  finiteDiagonalOperatorFamily (fun a =>
    (TimeWeightRegularity.allowedWeight (w := w) τ (η*ρ (cartesianInteriorPoint o δ N a)) t)^2)

def cartesianAllowedTestDerivative (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ρ : SpatialCoordinates d → ℝ) {w : TimeWeight} {g : TimeGrid} {β : ℝ}
    (H : TimeWeightRegularity w g β) (τ η t : ℝ) :
    (CartesianInteriorIndex N → ℝ) →L[ℝ] (CartesianInteriorIndex N → ℝ) :=
  finiteDiagonalOperatorFamily (fun a =>
    2*(TimeWeightRegularity.allowedWeight (w := w) τ (η*ρ (cartesianInteriorPoint o δ N a)) t)^2*
      (τ*(H.derivative t/w.q t)+(η*ρ (cartesianInteriorPoint o δ N a))*H.derivative t))

theorem cartesianAllowedTestOperator_apply (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ρ : SpatialCoordinates d → ℝ) (w : TimeWeight) (τ η t : ℝ) (f : CartesianInteriorIndex N → ℝ) :
    cartesianAllowedTestOperator o δ N ρ w τ η t f=
      cartesianSquaredWeightTest o δ N
        (fun x => TimeWeightRegularity.allowedWeight (w := w) τ (η*ρ x) t) f := rfl

theorem cartesianAllowedTestOperator_hasDerivWithinAt (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ρ : SpatialCoordinates d → ℝ) {w : TimeWeight} {g : TimeGrid} {β : ℝ}
    (H : TimeWeightRegularity w g β) (τ η : ℝ) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    HasDerivWithinAt (cartesianAllowedTestOperator o δ N ρ w τ η)
      (cartesianAllowedTestDerivative o δ N ρ H τ η t) (Icc 0 g.period) t := by
  apply finiteDiagonalOperatorFamily_hasDerivWithinAt
  intro a
  convert (H.hasDerivWithinAt_allowedWeight τ (η*ρ (cartesianInteriorPoint o δ N a)) ht).pow 2 using 1
  ring

theorem cartesianAllowedTestOperator_endpoint (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ρ : SpatialCoordinates d → ℝ) {w : TimeWeight} {g : TimeGrid} {β : ℝ}
    (H : TimeWeightRegularity w g β) (τ η : ℝ) :
    cartesianAllowedTestOperator o δ N ρ w τ η 0=
      cartesianAllowedTestOperator o δ N ρ w τ η g.period := by
  unfold cartesianAllowedTestOperator TimeWeightRegularity.allowedWeight
  rw [H.endpoint]

theorem cartesianAllowedTestDerivative_pairing_bound (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (ρ : SpatialCoordinates d → ℝ) (R : ℝ)
    (hR : ∀ a : CartesianInteriorIndex N, |ρ (cartesianInteriorPoint o δ N a)| ≤ R)
    {w : TimeWeight} {g : TimeGrid} {β : ℝ} (H : TimeWeightRegularity w g β)
    (τ η : ℝ) (hη : |η|=1) {t : ℝ} (ht : t ∈ Icc 0 g.period)
    (f : CartesianInteriorIndex N → ℝ) :
    |cartesianPhysicalInner δ N f (cartesianAllowedTestDerivative o δ N ρ H τ η t f)| ≤
      (2*β*(|τ|+R)*(w.q t)^2)*cartesianWeightedNodeEnergy o δ N
        (fun x => TimeWeightRegularity.allowedWeight (w := w) τ (η*ρ x) t) f := by
  apply cartesianPhysicalInner_diagonal_bound o δ hδ N
  intro a
  let σ := TimeWeightRegularity.allowedWeight (w := w) τ (η*ρ (cartesianInteriorPoint o δ N a)) t
  let L := τ*(H.derivative t/w.q t)+(η*ρ (cartesianInteriorPoint o δ N a))*H.derivative t
  have hb : |L| ≤ β*(|τ|+R)*(w.q t)^2 := by
    have he := H.logWeight_derivative_bound τ (η*ρ (cartesianInteriorPoint o δ N a)) ht
    rw [abs_mul,hη,one_mul] at he
    exact he.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hR a)) H.beta_pos.le) (sq_nonneg _))
  change |2*σ^2*L| ≤ (2*β*(|τ|+R)*(w.q t)^2)*σ^2
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*σ^2)]
  calc
    _ ≤ 2*σ^2*(β*(|τ|+R)*(w.q t)^2) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end Carleman
