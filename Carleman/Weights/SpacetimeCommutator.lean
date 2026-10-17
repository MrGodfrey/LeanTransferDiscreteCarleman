module

public import Carleman.Weights.SpacetimeConjugation
public import Carleman.Weights.AllowedFormBounds
public import Carleman.Spatial.CommutatorPerturbation

/-! Original A2 yields the actual Bochner L² commutator estimate C/L.
Measurability of A on domain paths follows from A1's closed associated graph. -/
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

def allowedCommutatorPath (v : ℝ → D) (t : ℝ) : Lp ℝ 2 ν :=
  conjugatedCommutator A (ρ.multiplier w τ t) (ρ.neg.multiplier w (-τ) t) (hw t) (hξ t) (v t)

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] in
theorem allowedCommutatorPath_eq (v : ℝ → D) (t : ℝ) :
    allowedCommutatorPath A ρ w τ hw hξ v t = A (v t) -
      (ρ.multiplier w τ t).map (A (conformingWeight (ρ.neg.multiplier w (-τ) t) (hξ t) (v t))) :=
  conjugatedCommutator_eq A _ _ (hw t) (hξ t)
    (Filter.Eventually.of_forall (ρ.multiplier_inverse w τ t)) (v t)

include hA in
omit [IsLocallyFiniteMeasure ν] in
theorem allowedCommutatorPath_aestronglyMeasurable (g : TimeGrid)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) (v : ℝ → D)
    (hv : AEStronglyMeasurable (fun t => (v t : Lp ℝ 2 ν)) g.timeMeasure) :
    AEStronglyMeasurable (allowedCommutatorPath A ρ w τ hw hξ v) g.timeMeasure := by
  have hvA := CoerciveForm.IsAssociated.operator_aestronglyMeasurable b hA hv
  have hiH : AEStronglyMeasurable (fun t =>
      (conformingWeight (ρ.neg.multiplier w (-τ) t) (hξ t) (v t) : Lp ℝ 2 ν)) g.timeMeasure :=
    ρ.neg.aestronglyMeasurable_map w (-τ) hq hv
  have hiA := CoerciveForm.IsAssociated.operator_aestronglyMeasurable b hA hiH
  change AEStronglyMeasurable (fun t => allowedCommutatorPath A ρ w τ hw hξ v t) g.timeMeasure
  simp_rw [allowedCommutatorPath_eq]
  exact hvA.sub (ρ.aestronglyMeasurable_map w τ hq hiA)

include hA in
/-- This is (9.26-eq3) in the genuine time-space norm, using original A2
and the actual domain path. Its C/L constant is independent of T and qmax. -/
theorem allowedCommutator_spacetime_le (g : TimeGrid)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) {C L : ℝ} (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hA2 : ∀ t (v : D), ‖allowedCommutatorPath A ρ w τ hw hξ (fun _ => v) t‖ ≤
      C*∑ k : Fin n, w.q t^(n-k.val)*
        ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖)
    (v : ℝ → D) (hv : MemLp (fun t => domainSobolevJet hS hν hD (v t)) 2 g.timeMeasure) :
    MemLp (allowedCommutatorPath A ρ w τ hw hξ v) 2 g.timeMeasure ∧
    bochnerL2Norm g.timeMeasure (allowedCommutatorPath A ρ w τ hw hξ v) ≤
      (C/L)*WeakSobolevJet.spacetimeParameterNorm g (fun t => L*w.q t)
        (fun _ => BoundedMultiplier.one) (fun t => domainSobolevJet hS hν hD (v t)) := by
  let J := fun t => domainSobolevJet hS hν hD (v t)
  let F := WeakSobolevJet.parameterTimeField (fun t => L*w.q t) (fun _ => BoundedMultiplier.one) J
  have hF := WeakSobolevJet.memLp_unweightedParameterTimeField g w L hq hv
  have hvH : AEStronglyMeasurable (fun t => (v t : Lp ℝ 2 ν)) g.timeMeasure := by
    simpa only [WeakSobolevJet.valueCLM_apply, domainSobolevJet_value] using
      WeakSobolevJet.valueCLM.continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable
  have hm := allowedCommutatorPath_aestronglyMeasurable b A hA ρ w τ hw hξ g hq v hvH
  have hc : 0 ≤ C/L := div_nonneg hC (zero_le_one.trans hL)
  have hb : ∀ᵐ t ∂g.timeMeasure, ‖allowedCommutatorPath A ρ w τ hw hξ v t‖ ≤
      (C/L)*∑ k, ‖F k t‖ := by
    apply Filter.Eventually.of_forall
    intro t
    have hh := conjugatedCommutator_parameter_le hS hν hD A _ _ (hw t) (hξ t)
      (w.nonneg t) hL hC (hA2 t) (v t)
    rw [WeakSobolevJet.parameterNorm_eq_sum_timeField (fun t => L*w.q t)
      (fun _ => BoundedMultiplier.one) J (mul_nonneg (zero_le_one.trans hL) (w.nonneg t))] at hh
    exact hh
  have hi := memLp_of_le_sum_norm hm F hF hc hb
  exact ⟨hi, bochnerL2Norm_le_sum hi F hF hc hb⟩
end Carleman
