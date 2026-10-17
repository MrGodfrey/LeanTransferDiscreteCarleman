module

public import Carleman.Weights.WeightedOperatorRegularity
public import Carleman.Weights.ClosureSpacetime

/-! Multiplication by an actual allowed weight preserves the original
periodic weak graph space, including the a.e. operator-domain representative. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman.PeriodicWeakTrajectory
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hνS : ∀ᵐ x ∂ν, x ∈ S)
  {D : Submodule ℝ (Lp ℝ 2 ν)} (hD : D ≤ sobolevSubspace d n ν S)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm (Lp ℝ 2 ν) V) (A : D →ₗ[ℝ] Lp ℝ 2 ν) (hA : b.IsAssociated A)
  (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)
  {g : TimeGrid} {w : TimeWeight} {β : ℝ} (h : TimeWeightRegularity w g β) (τ : ℝ)
  (hw : ∀ t (u : D), (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ D)
  (hξ : ∀ t (u : D), (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ D)

include hbounded hA hρ
/-- All regularity of the weighted path is derived from the original A1/A2,
actual smooth coefficient, and the given weak graph trajectory. No weighted
operator L² or weighted weak-product premise is left to a caller. -/
theorem exists_closure_weighted_trajectory {C Creg : ℝ} (hC : 0 ≤ C)
    (hell : ∀ v : D, ‖domainSobolevJet hS hνS hD v‖ ≤ Creg*‖A v‖)
    (hA2 : ∀ t (v : D), ‖allowedCommutatorPath A ρ w τ hw hξ (fun _ => v) t‖ ≤
      C*∑ k : Fin n, w.q t^(n-k.val)*
        ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hνS hD v)‖)
    (u : PeriodicWeakTrajectory g D A) :
    ∃ v : PeriodicWeakTrajectory g D A,
      v.value = (fun t => (ρ.multiplier w τ t).map (u.value t)) ∧
      v.derivative = ρ.weightedTimeDerivative h τ u.value u.derivative ∧
      v.domainValue =ᵐ[g.timeMeasure]
        (fun t => conformingWeight (ρ.multiplier w τ t) (hw t) (u.domainValue t)) := by
  let y := fun t => (ρ.multiplier w τ t).map (u.value t)
  have hyD : ∀ᵐ t ∂g.timeMeasure, y t ∈ D := by
    filter_upwards [u.domain_ae] with t ht
    exact hw t ⟨u.value t, ht⟩
  have hd : (fun t => domainRepresentative D y t) =ᵐ[g.timeMeasure]
      (fun t => conformingWeight (ρ.multiplier w τ t) (hw t) (u.domainValue t)) := by
    filter_upwards [domainRepresentative_ae D y g.timeMeasure hyD, u.domainValue_ae] with t ht hu
    apply Subtype.ext
    change (domainRepresentative D y t : Lp ℝ 2 ν) =
      (ρ.multiplier w τ t).map (u.domainValue t : Lp ℝ 2 ν)
    rw [ht, hu]
  obtain ⟨C₁, _, hconj⟩ := closure_spacetime_conjugation_uniform hS hbounded hνS hD ρ hρ
  have hj := (hconj g w τ false h.aestronglyMeasurable hw u.domainValue
    (u.domainSobolev_L2 hS hνS hD Creg hell)).1
  have hAy := weightedOperator_L2 hS hνS hD b A hA ρ w τ hw hξ g h.aestronglyMeasurable
    hC hA2 u.domainValue u.operator_L2 hj
  have hAyd : MemLp (fun t => A (domainRepresentative D y t)) 2 g.timeMeasure :=
    hAy.ae_eq (hd.mono fun t ht => congrArg A ht.symm)
  let v : PeriodicWeakTrajectory g D A := {
    value := y
    derivative := ρ.weightedTimeDerivative h τ u.value u.derivative
    continuous := ρ.continuousOn_map h τ u.continuous
    periodic_trace := ρ.map_periodic_trace h τ u.periodic_trace
    value_L2 := ρ.memLp_map w τ h.aestronglyMeasurable u.value_L2
    derivative_L2 := ρ.weightedTimeDerivative_L2 h τ u.value_L2 u.derivative_L2
    domain_ae := hyD
    operator_L2 := hAyd
    weak_derivative := ρ.hasWeakTimeDerivative_map h τ u.weak_derivative u.continuous u.derivative_L2 }
  exact ⟨v, rfl, rfl, hd⟩
end Carleman.PeriodicWeakTrajectory
