module

public import Carleman.Spatial.SmoothDirectionalEnergy

/-! Young's inequality for the actual finite family of directional derivatives. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem directionalEnergy_nonneg (e : ι → E) (f : E → ℝ) (x : E) :
    0 ≤ directionalEnergy e f x := Finset.sum_nonneg fun i _ => sq_nonneg (smoothD (e i) f x)

theorem directionalPair_young (e : ι → E) (p z : E → ℝ) (x : E)
    {a C : ℝ} (ha : 0 < a) (hp : directionalEnergy e p x ≤ C*a) :
    2*directionalPair e p z x*z x ≤ a*directionalEnergy e z x+C*(z x)^2 := by
  have hs : 0 ≤ ∑ i, (a*smoothD (e i) z x-smoothD (e i) p x*z x)^2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (a*smoothD (e i) z x-smoothD (e i) p x*z x)
  have he : (∑ i, (a*smoothD (e i) z x-smoothD (e i) p x*z x)^2)=
      a^2*directionalEnergy e z x-2*a*directionalPair e p z x*z x+
        directionalEnergy e p x*(z x)^2 := by
    simp only [directionalEnergy,directionalPair,Finset.mul_sum,Finset.sum_mul,
      ← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he] at hs
  have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg (z x))
  have hn : 0 ≤ a*(a*directionalEnergy e z x+C*(z x)^2-
      2*directionalPair e p z x*z x) := by nlinarith
  have := nonneg_of_mul_nonneg_right hn ha
  linarith

end Carleman
