module

public import Carleman.Spatial.CartesianTestTimeDerivative
public import Carleman.Spatial.AllowedCartesianDiagonalTest

/-! The original test-time estimate, with one constant fixed before all
grids, periods, allowed time weights, bounded powers, signs, times and states. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem cartesianAllowedTestOperator_periodic (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (ρ : SpatialCoordinates d → ℝ) (w : TimeWeight) (T τ η : ℝ)
    (hper : Function.Periodic w.q T) :
    Function.Periodic (cartesianAllowedTestOperator o δ N ρ w τ η) T := by
  intro t
  unfold cartesianAllowedTestOperator TimeWeightRegularity.allowedWeight
  rw [hper t]

theorem allowed_weight_cartesian_test_time
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (β τStar : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ C > 0, ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hTS : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆ S)
      (h : ℝ), 0 < h → (∀ j, δ j ≤ h) →
      ∀ (w : TimeWeight) (g : TimeGrid) (H : TimeWeightRegularity w g β)
        (τ η t : ℝ), |τ| ≤ τStar → |η|=1 → t ∈ Icc 0 g.period → h*w.q t ≤ 1 →
      ∀ f : CartesianInteriorIndex N → ℝ,
      let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
      |cartesianPhysicalInner δ N f (cartesianAllowedTestDerivative o δ N ρ.value H τ η t f)| ≤
        C*(w.q t)^2*(σ.seminorm (cartesianKuhnReconstructionLp o δ hδ N f))^2 := by
  obtain ⟨R₀,hR₀⟩ := hcompact.exists_bound_of_continuousOn hρ.continuousOn
  let R := max 0 R₀+1
  have hRpos : 0 < R := by dsimp only [R]; positivity
  obtain ⟨C₀,hC₀,hbound⟩ := allowed_weight_cartesianKuhn_stability hS hc hcompact ρ hρ
  let A := 2*β*(τStar+R)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A*C₀,mul_pos hA hC₀,?_⟩
  intro o δ hδ N hTS h hh hstep w g H τ η t hτ hη ht hsmall f
  let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
  have hnode (a : CartesianInteriorIndex N) : |ρ.value (cartesianInteriorPoint o δ N a)| ≤ R := by
    have hr := hR₀ _ (subset_closure (hTS (cartesianInteriorPoint_mem o δ hδ N a)))
    rw [Real.norm_eq_abs] at hr
    exact hr.trans (by dsimp only [R]; linarith [le_max_right (0:ℝ) R₀])
  have htime := cartesianAllowedTestDerivative_pairing_bound o δ hδ N ρ.value R hnode H τ η hη ht f
  have hmass := (hbound o δ hδ N hTS h hh hstep w τ t η hη hsmall f).1
  change cartesianWeightedNodeEnergy o δ N σ.value f ≤ C₀*(σ.seminorm (cartesianKuhnReconstructionLp o δ hδ N f))^2 at hmass
  change |cartesianPhysicalInner δ N f (cartesianAllowedTestDerivative o δ N ρ.value H τ η t f)| ≤
    (2*β*(|τ|+R)*(w.q t)^2)*cartesianWeightedNodeEnergy o δ N σ.value f at htime
  change _ ≤ (A*C₀)*(w.q t)^2*(σ.seminorm (cartesianKuhnReconstructionLp o δ hδ N f))^2
  calc
    _ ≤ (2*β*(|τ|+R)*(w.q t)^2)*cartesianWeightedNodeEnergy o δ N σ.value f := htime
    _ ≤ (A*(w.q t)^2)*cartesianWeightedNodeEnergy o δ N σ.value f := by
      apply mul_le_mul_of_nonneg_right _ (cartesianWeightedNodeEnergy_nonneg o δ hδ N σ.value f)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hτ le_rfl) (by positivity)) (sq_nonneg _)
    _ ≤ (A*(w.q t)^2)*(C₀*(σ.seminorm (cartesianKuhnReconstructionLp o δ hδ N f))^2) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hA.le (sq_nonneg _))
    _ = _ := by ring

end Carleman
