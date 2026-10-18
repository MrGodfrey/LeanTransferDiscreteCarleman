module

public import Carleman.Periodic.SeminormSum
public import Carleman.Section4.SpatialEnergy
public import Carleman.Weights.SecondOrderEulerSobolev
public import Carleman.Spatial.SobolevTruncation

/-! N3's spatial approximation lifts to the actual nodal R norm from
Section 3, with no replacement by an assumed sequence error estimate. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.WeakSobolevJet
variable {d m n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

/-- A fixed order-only bound suffices to compare N_m with R_n. -/
theorem weightedNorm_truncate_le_parameterNorm (hmn : m ≤ n) {q : ℝ} (hq : 1 ≤ q)
    (σ : BoundedMultiplier ν) (u : WeakSobolevJet d n ν S) :
    weightedNorm q σ (truncate hmn u) ≤ (m+1:ℝ)*parameterNorm q σ u := by
  apply (weightedNorm_le_parameterNorm (zero_le_one.trans hq) σ _).trans
  calc
    _ ≤ ∑ _k : Fin (m+1), parameterNorm q σ u := by
      apply Finset.sum_le_sum
      intro k _
      let j : Fin (n+1) := ⟨k.val,by omega⟩
      have hp : q^(m-k.val) ≤ q^(n-j.val) := pow_le_pow_right₀ hq (by dsimp [j]; omega)
      have hs : q^(n-j.val)*σ.seminorm (field j u) ≤ parameterNorm q σ u := by
        unfold parameterNorm
        exact Finset.single_le_sum (f := fun l : Fin (n+1) => q^(n-l.val)*σ.seminorm (field l u))
          (fun l _ => mul_nonneg (pow_nonneg (zero_le_one.trans hq) _) (apply_nonneg σ.seminorm (field l u)))
          (Finset.mem_univ j)
      exact (mul_le_mul_of_nonneg_right hp (apply_nonneg σ.seminorm (field j u))).trans hs
    _ = _ := by simp

/-- Nodewise bounds by the real spatial R yield the real sum of field L²
norms used in Lemma 3.3. The target may be an energy or an L² error. -/
theorem nodal_approximation_bound (g : TimeGrid) (q : g.Sequence ℝ) (hq : ∀ i, 0 ≤ q i)
    (σ : g.Index → BoundedMultiplier ν) (u : g.Sequence (WeakSobolevJet d n ν S))
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : g.Index → Seminorm ℝ E) (v : g.Sequence E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, p i (v i) ≤ C*parameterNorm (q i) (σ i) (u i)) :
    g.weightedNorm p v ≤ C*nodeParameterNorm g q σ u := by
  apply g.weightedNorm_le_field_sum p v
    (fun (k : Fin (n+1)) i => q i^(n-k.val) • (σ i).map (field k (u i))) hC
  intro i
  simpa only [parameterNorm,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hq i) _),
    BoundedMultiplier.seminorm_apply] using hb i

end Carleman.WeakSobolevJet
namespace Carleman.Section4
variable {d m n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hD : D ≤ sobolevSubspace d n ν S) (hDV : D ≤ V)

/-- The original-domain inclusion identifies the jets before estimating N.
This applies to n=2m and introduces only a constant depending on m. -/
theorem conforming_energy_le_parameterNorm (hmn : m ≤ n) {q : ℝ} (hq : 1 ≤ q)
    (σ : BoundedMultiplier ν) (u : D) :
    conformingWeightedNorm hS hν hV q σ (Submodule.inclusion hDV u) ≤
      (m+1:ℝ)*conformingParameterNorm hS hν hD q σ u := by
  have he : domainSobolevJet hS hν hV (Submodule.inclusion hDV u) =
      WeakSobolevJet.truncate hmn (domainSobolevJet hS hν hD u) := by
    apply WeakSobolevJet.value_injective hS hν
    simp only [domainSobolevJet_value,WeakSobolevJet.truncate_value,Submodule.coe_inclusion]
  change WeakSobolevJet.weightedNorm q σ _ ≤ _
  rw [he]
  exact WeakSobolevJet.weightedNorm_truncate_le_parameterNorm hmn hq σ _

end Carleman.Section4
