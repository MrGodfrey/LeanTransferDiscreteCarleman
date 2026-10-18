module

public import Carleman.Control.ConformingInterpolation

/-! Actual first weak derivatives and the mesh-weight inverse/interpolation
budgets used in the heat (m=1) realization. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d 1 ν S)

def conformingHeatGradient (σ : BoundedMultiplier ν) (v : V) : ℝ :=
  σ.seminorm (WeakSobolevJet.field 1 (domainSobolevJet hS hν hV v))

theorem conformingHeatGradient_nonneg (σ : BoundedMultiplier ν) (v : V) :
    0 ≤ conformingHeatGradient hS hν hV σ v := apply_nonneg _ _

theorem conformingHeatNorm_le {q : ℝ} (hq : 0 ≤ q) (σ : BoundedMultiplier ν) (v : V) :
    conformingWeightedNorm hS hν hV q σ v ≤
      q*σ.seminorm (v : Lp ℝ 2 ν)+conformingHeatGradient hS hν hV σ v := by
  have hh := WeakSobolevJet.weightedNorm_le_parameterNorm hq σ (domainSobolevJet hS hν hV v)
  change WeakSobolevJet.weightedNorm q σ (domainSobolevJet hS hν hV v) ≤
    ∑ k : Fin 2, q^(1-k.val)*σ.seminorm (WeakSobolevJet.field k (domainSobolevJet hS hν hV v)) at hh
  rw [Fin.sum_univ_two] at hh
  norm_num only [Fin.val_zero,Fin.val_one,Nat.sub_zero,Nat.sub_self,pow_one,pow_zero,one_mul] at hh
  have hz := WeakSobolevJet.weighted_zero_eq σ (domainSobolevJet hS hν hV v)
  rw [domainSobolevJet_value] at hz
  rw [hz] at hh
  exact hh

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
/-- The condition q|σ|≤|ζ| is precisely qℓ≤1 when ζ=ℓ⁻¹σ. -/
theorem scaled_seminorm_le_auxiliary {q : ℝ} (hq : 0 < q)
    (σ ζ : BoundedMultiplier ν) (hζ : ∀ᵐ x ∂ν, q*|σ.value x| ≤ |ζ.value x|)
    (u : Lp ℝ 2 ν) : q*σ.seminorm u ≤ ζ.seminorm u := by
  have hh := σ.seminorm_le_of_weight_le ζ q⁻¹
    (hζ.mono fun x hx => (le_inv_mul_iff₀ hq).mpr hx) u
  have hm := mul_le_mul_of_nonneg_left hh hq.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hq.ne',one_mul] using hm

theorem conformingHeatNorm_le_auxiliary {q : ℝ} (hq : 0 < q)
    (σ ζ : BoundedMultiplier ν) (hζ : ∀ᵐ x ∂ν, q*|σ.value x| ≤ |ζ.value x|) (v : V) :
    conformingWeightedNorm hS hν hV q σ v ≤
      conformingHeatGradient hS hν hV σ v+ζ.seminorm (v : Lp ℝ 2 ν) := by
  apply (conformingHeatNorm_le hS hν hV hq.le σ v).trans
  have hh := scaled_seminorm_le_auxiliary hq σ ζ hζ (v : Lp ℝ 2 ν)
  linarith only [hh]

theorem conformingHeatInverse_of_gradient {q : ℝ} (hq : 0 < q)
    (σ ζ : BoundedMultiplier ν) (hζ : ∀ᵐ x ∂ν, q*|σ.value x| ≤ |ζ.value x|)
    (CI : ℝ) (v : V)
    (hinv : conformingHeatGradient hS hν hV σ v ≤ CI*ζ.seminorm (v : Lp ℝ 2 ν)) :
    conformingWeightedNorm hS hν hV q σ v ≤ (1+CI)*ζ.seminorm (v : Lp ℝ 2 ν) := by
  apply (conformingHeatNorm_le_auxiliary hS hν hV hq σ ζ hζ v).trans
  linarith only [hinv]

end Carleman.Physical
