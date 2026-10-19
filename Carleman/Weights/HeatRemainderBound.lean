module

public import Carleman.Weights.InteriorHeatB

/-! A quantitative remainder estimate preserving the manuscript's q and beta orders. -/
@[expose] public noncomputable section
namespace Carleman

theorem heat_remainder_bound {K Q Q₁ Q₂ β A₂ A₁ A₀ ρ : ℝ}
    (hK : 0 ≤ K) (hQ : 1 ≤ Q) (hβ : 0 ≤ β)
    (hQ₁ : |Q₁| ≤ β*Q^2) (hQ₂ : |Q₂| ≤ β^2*Q^3)
    (hA₂ : |A₂| ≤ K) (hA₁ : |A₁| ≤ K) (hA₀ : |A₀| ≤ K) (hρ : |ρ| ≤ K) :
    |Q^2*A₂+Q₁*(Q*A₁+A₀)+Q₂*ρ| ≤ 2*K*(Q^2+(β+β^2)*Q^3) := by
  have hQ0 : 0 ≤ Q := by linarith
  have h1 : |Q^2*A₂| ≤ K*Q^2 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg Q)]
    nlinarith [mul_le_mul_of_nonneg_left hA₂ (sq_nonneg Q)]
  have hc : |Q*A₁+A₀| ≤ 2*K*Q := by
    have hh := abs_add_le (Q*A₁) A₀
    rw [abs_mul,abs_of_nonneg hQ0] at hh
    nlinarith [mul_le_mul_of_nonneg_left hA₁ hQ0,
      mul_nonneg hK (sub_nonneg.mpr hQ)]
  have h2 : |Q₁*(Q*A₁+A₀)| ≤ 2*K*β*Q^3 := by
    rw [abs_mul]
    have hh := mul_le_mul hQ₁ hc (abs_nonneg _) (show 0 ≤ β*Q^2 by positivity)
    nlinarith [hh]
  have h3 : |Q₂*ρ| ≤ K*β^2*Q^3 := by
    rw [abs_mul]
    have hh := mul_le_mul hQ₂ hρ (abs_nonneg _) (show 0 ≤ β^2*Q^3 by positivity)
    nlinarith [hh]
  have ha := abs_add_le (Q^2*A₂+Q₁*(Q*A₁+A₀)) (Q₂*ρ)
  have hb := abs_add_le (Q^2*A₂) (Q₁*(Q*A₁+A₀))
  have hn : 0 ≤ K*Q^2+K*β^2*Q^3 := by positivity
  nlinarith

end Carleman
