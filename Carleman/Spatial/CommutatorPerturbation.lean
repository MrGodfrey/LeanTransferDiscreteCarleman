module

public import Carleman.Spatial.ParameterConjugation
public import Carleman.Spatial.ShiftedFormBounds

/-! The original A2 commutator on the actual operator domain has the required
1/L loss against the scaled full spatial graph norm. No interpolation or
parabolic estimate is presumed by this independent perturbation estimate. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
namespace WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

/-- Every lower derivative order earns at least one factor L. -/
theorem lower_parameterNorm_le {q L : ℝ} (hq : 0 ≤ q) (hL : 1 ≤ L)
    (w : BoundedMultiplier ν) (u : WeakSobolevJet d n ν S) :
    L*(∑ k : Fin n, q^(n-k.val)*w.seminorm (field k.castSucc u)) ≤ parameterNorm (L*q) w u := by
  have hk (k : Fin n) : L*(q^(n-k.val)*w.seminorm (field k.castSucc u)) ≤
      (L*q)^(n-k.val)*w.seminorm (field k.castSucc u) := by
    rw [mul_pow]
    have hp : L ≤ L^(n-k.val) := by
      simpa using pow_le_pow_right₀ hL (show 1 ≤ n-k.val by omega)
    nlinarith [mul_le_mul_of_nonneg_right hp
      (mul_nonneg (pow_nonneg hq (n-k.val)) (apply_nonneg w.seminorm (field k.castSucc u)))]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ k : Fin n, (L*q)^(n-k.val)*w.seminorm (field k.castSucc u) :=
      Finset.sum_le_sum fun k _ => hk k
    _ ≤ parameterNorm (L*q) w u := by
      unfold parameterNorm
      rw [Fin.sum_univ_castSucc]
      exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (mul_nonneg (zero_le_one.trans hL) hq) _)
        (apply_nonneg _ _))
end WeakSobolevJet

variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)

/-- The actual A2 expression [A,w] ξv, with both domain maps justified by A2. -/
def conjugatedCommutator (A : D →ₗ[ℝ] Lp ℝ 2 ν) (w ξ : BoundedMultiplier ν)
    (hw : ∀ v : D, w.map (v : Lp ℝ 2 ν) ∈ D)
    (hξ : ∀ v : D, ξ.map (v : Lp ℝ 2 ν) ∈ D) (v : D) : Lp ℝ 2 ν :=
  A (conformingWeight w hw (conformingWeight ξ hξ v)) - w.map (A (conformingWeight ξ hξ v))

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
/-- Cancellation is equality in the original domain, not added operator regularity. -/
theorem conjugatedCommutator_eq (A : D →ₗ[ℝ] Lp ℝ 2 ν) (w ξ : BoundedMultiplier ν)
    (hw : ∀ v : D, w.map (v : Lp ℝ 2 ν) ∈ D)
    (hξ : ∀ v : D, ξ.map (v : Lp ℝ 2 ν) ∈ D)
    (hinv : ∀ᵐ x ∂ν, w.value x*ξ.value x=1) (v : D) :
    conjugatedCommutator A w ξ hw hξ v = A v - w.map (A (conformingWeight ξ hξ v)) := by
  have he : conformingWeight w hw (conformingWeight ξ hξ v) = v := by
    apply Subtype.ext
    exact w.map_inverse ξ hinv (v : Lp ℝ 2 ν)
  unfold conjugatedCommutator
  rw [he]

/-- Exactly the 1/L perturbation of Lemma3.1, using original A2 and actual D^jv. -/
theorem conjugatedCommutator_parameter_le (A : D →ₗ[ℝ] Lp ℝ 2 ν)
    (w ξ : BoundedMultiplier ν)
    (hw : ∀ v : D, w.map (v : Lp ℝ 2 ν) ∈ D)
    (hξ : ∀ v : D, ξ.map (v : Lp ℝ 2 ν) ∈ D)
    {q L C : ℝ} (hq : 0 ≤ q) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hA2 : ∀ v : D, ‖conjugatedCommutator A w ξ hw hξ v‖ ≤
      C*∑ k : Fin n, q^(n-k.val)*‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖)
    (v : D) : ‖conjugatedCommutator A w ξ hw hξ v‖ ≤
      (C/L)*WeakSobolevJet.parameterNorm (L*q) BoundedMultiplier.one (domainSobolevJet hS hν hD v) := by
  have hh := WeakSobolevJet.lower_parameterNorm_le hq hL BoundedMultiplier.one (domainSobolevJet hS hν hD v)
  simp only [BoundedMultiplier.one_seminorm] at hh
  have hLpos := zero_lt_one.trans_le hL
  have he := mul_le_mul_of_nonneg_left hh hC
  have ha := mul_le_mul_of_nonneg_left (hA2 v) hLpos.le
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hLpos).mpr
  nlinarith [he, ha]
end Carleman
