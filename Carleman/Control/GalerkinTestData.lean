module

public import Carleman.Control.GalerkinTestTimeBound

/-! The actual original test operator supplies every N4 property except the
spatial superapproximation estimate, which remains explicit. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (X : Submodule ℝ (Lp ℝ 2 ν)) [CompleteSpace X] (hX : X ≤ V)
  (g : TimeGrid) (ρ : SpatialProfile ν) (w : TimeWeight)

/-- N4's original spatial superapproximation, for the specified Pi_X(sigma²z),
not an arbitrary test map. No temporal property is an input. -/
def GalerkinSuperapprox (τ Csuper mesh : ℝ) : Prop :=
  ∀ t ∈ Icc 0 g.period,
    ∀ hw : ∀ v : V, (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V, ∀ z : X,
    conformingWeightedNorm hS hν hV (w.q t) (ρ.neg.multiplier w (-τ) t)
      (X.inclusion hX (galerkinWeightedTest X ρ w τ t z)-
        conformingWeight (ρ.multiplier w τ t) hw
          (conformingWeight (ρ.multiplier w τ t) hw (X.inclusion hX z))) ≤
      (Csuper*mesh*w.max)*conformingWeightedNorm hS hν hV (w.q t)
        (ρ.multiplier w τ t) (X.inclusion hX z)

def galerkinWeightedTestData {β : ℝ} (h : TimeWeightRegularity w g β)
    (τStar τ Csuper mesh : ℝ) (hτ : |τ| ≤ τStar)
    (hs : GalerkinSuperapprox hS hν hV X hX g ρ w τ Csuper mesh) :
    Section4.WeightedTest hS hν hV (conformingReconstruction V X hX)
      g ρ w τ (2*β*(τStar+ρ.bound)) Csuper mesh where
  op t := (galerkinWeightedTest X ρ w τ t).toLinearMap
  derivative t := (galerkinWeightedTestDerivative X ρ w h τ t).toLinearMap
  endpoint := congrArg ContinuousLinearMap.toLinearMap (galerkinWeightedTest_endpoint X ρ w h τ)
  hasDeriv z _ ht := galerkinWeightedTest_hasDeriv X ρ w h τ z ht
  symmetric t _ := galerkinWeightedTest_symmetric X ρ w τ t
  nonneg t _ := galerkinWeightedTest_nonneg X ρ w τ t
  time_bound z _ ht := galerkinWeightedTest_time_bound_uniform X ρ w h τStar τ hτ ht z
  superapprox := hs

end Carleman.Physical
