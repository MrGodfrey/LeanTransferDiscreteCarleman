module

public import Carleman.Weights.SecondOrderFrozenGraph

/-! Original A2/A3 at one actual allowed weight. This package contains no
graph or error conclusion. Positive and inverse weights are supplied separately
when an adjoint argument needs both, as required by the manuscript. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d 1 ν S)
  (hD : D ≤ sobolevSubspace d 2 ν S) (a : V → V → ℝ) (A : D →ₗ[ℝ] Lp ℝ 2 ν)

structure SecondOrderWeightData (ρ : SpatialProfile ν) (w : TimeWeight) (τ c C Ccomm : ℝ) : Prop where
  form_preserving : ∀ t (v : V), (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V
  domain_preserving : ∀ t (u : D), (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ D
  inverse_preserving : ∀ t (u : D), (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ D
  coercive : ∀ t (v : V), c*(conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v)^2 -
    C*(w.q t*(ρ.multiplier w τ t).seminorm (v : Lp ℝ 2 ν))^2 ≤
      a v (conformingWeight (ρ.multiplier w τ t) (form_preserving t)
        (conformingWeight (ρ.multiplier w τ t) (form_preserving t) v))
  commutator : ∀ t (v : D),
    ‖allowedCommutatorPath A ρ w τ domain_preserving inverse_preserving (fun _ => v) t‖ ≤
      Ccomm*∑ k : Fin 2, w.q t^(2-k.val)*
        ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖
end Carleman

namespace Carleman.SpatialProfile
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

@[simp] theorem neg_neg_profile (ρ : SpatialProfile ν) : ρ.neg.neg = ρ := by
  cases ρ
  simp only [neg,neg_neg]

theorem inverse_timeMap_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ρ : SpatialProfile ν) (g : TimeGrid) (w : TimeWeight) (τ : ℝ)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) (u : Lp (Lp E 2 ν) 2 g.timeMeasure) :
    ρ.neg.timeMap g w (-τ) hq (ρ.timeMap g w τ hq u) = u := by
  simpa only [neg_neg_profile,neg_neg] using ρ.neg.timeMap_inverse g w (-τ) hq u
end Carleman.SpatialProfile
