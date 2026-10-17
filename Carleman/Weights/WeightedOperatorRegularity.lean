module

public import Carleman.Weights.SpacetimeCommutator
public import Carleman.Weights.WeakTemporalProduct

/-! A2 and the actual weighted Sobolev regularity give the operator L² field
of the weighted path. This is not assumed as part of a product-rule premise. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm (Lp ℝ 2 ν) V) (A : D →ₗ[ℝ] Lp ℝ 2 ν) (hA : b.IsAssociated A)
  (ρ : SpatialProfile ν) (w : TimeWeight) (τ : ℝ)
  (hw : ∀ t (u : D), (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ D)
  (hξ : ∀ t (u : D), (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ D)

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
theorem conformingWeight_inverse (u : D) (t : ℝ) :
    conformingWeight (ρ.neg.multiplier w (-τ) t) (hξ t)
      (conformingWeight (ρ.multiplier w τ t) (hw t) u) = u := by
  apply Subtype.ext
  exact BoundedMultiplier.map_inverse _ _
    (Filter.Eventually.of_forall fun x => by rw [mul_comm]; exact ρ.multiplier_inverse w τ t x) _

include hA in
theorem weightedOperator_L2 (g : TimeGrid) (hq : AEStronglyMeasurable w.q g.timeMeasure)
    {C : ℝ} (hC : 0 ≤ C)
    (hA2 : ∀ t (v : D), ‖allowedCommutatorPath A ρ w τ hw hξ (fun _ => v) t‖ ≤
      C*∑ k : Fin n, w.q t^(n-k.val)*
        ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖)
    (u : ℝ → D) (huA : MemLp (fun t => A (u t)) 2 g.timeMeasure)
    (hv : MemLp (fun t => domainSobolevJet hS hν hD
      (conformingWeight (ρ.multiplier w τ t) (hw t) (u t))) 2 g.timeMeasure) :
    MemLp (fun t => A (conformingWeight (ρ.multiplier w τ t) (hw t) (u t))) 2 g.timeMeasure := by
  let v := fun t => conformingWeight (ρ.multiplier w τ t) (hw t) (u t)
  have hc := (allowedCommutator_spacetime_le hS hν hD b A hA ρ w τ hw hξ g hq
    hC (le_refl 1) hA2 v hv).1
  have hs := ρ.memLp_map w τ hq huA
  apply (hc.add hs).ae_eq
  apply Filter.Eventually.of_forall
  intro t
  change allowedCommutatorPath A ρ w τ hw hξ v t + (ρ.multiplier w τ t).map (A (u t)) = _
  rw [allowedCommutatorPath_eq]
  change A (v t) - (ρ.multiplier w τ t).map
    (A (conformingWeight (ρ.neg.multiplier w (-τ) t) (hξ t)
      (conformingWeight (ρ.multiplier w τ t) (hw t) (u t)))) + _ = _
  rw [conformingWeight_inverse, sub_add_cancel]
end Carleman
