module

public import Carleman.Spatial.WeightedSobolevNorm

/-! The actual order-one weighted Sobolev norm and nonnegative square bounds. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem WeakSobolevJet.heat_weightedNorm_sq
    {d : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
    {S : Set (SpatialCoordinates d)} (q : ℝ) (σ : BoundedMultiplier ν)
    (u : WeakSobolevJet d 1 ν S) :
    (weightedNorm q σ u)^2 = q^2*(σ.seminorm (value u))^2+(σ.seminorm (field 1 u))^2 := by
  rw [weightedNorm_sq,weightedSq,Fin.sum_univ_two]
  norm_num only [Fin.val_zero,Fin.val_one,Nat.sub_zero,Nat.sub_self,pow_one,pow_zero,one_mul]
  rw [weighted_zero_eq]
  ring

theorem nonneg_le_sqrt_mul_of_sq_le {x C b : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hb : 0 ≤ b) (h : x^2 ≤ C*b^2) : x ≤ Real.sqrt C*b := by
  apply (sq_le_sq₀ hx (mul_nonneg (Real.sqrt_nonneg _) hb)).mp
  simpa only [mul_pow,Real.sq_sqrt hC] using h

end Carleman
