module

public import Carleman.Weights.WeightedGraphRemainder
public import Carleman.Weights.ClosureWeakTrajectory
public import Carleman.Continuous.PeriodicGraphEquivalence

/-! The weighted graph representative required by the remainder estimate is
constructed from the original one-way elliptic regularity and A2. Neither a
weighted graph estimate nor all-time operator-domain membership is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hνS : ∀ᵐ x ∂ν, x ∈ S)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm (Lp ℝ 2 ν) V) (hD : b.domain ≤ sobolevSubspace d n ν S)
  (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)

include hbounded hρ in
/-- Actual weak multiplication followed by the proved periodic graph equivalence. -/
theorem exists_weighted_graph {g : TimeGrid} {w : TimeWeight} {β : ℝ}
    (h : TimeWeightRegularity w g β) (τ : ℝ)
    (hw : ∀ t (u : b.domain), (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ b.domain)
    (hξ : ∀ t (u : b.domain), (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ b.domain)
    {C Creg : ℝ} (hC : 0 ≤ C)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hS hνS hD v‖ ≤ Creg*‖b.operator v‖)
    (hA2 : ∀ t (v : b.domain), ‖allowedCommutatorPath b.operator ρ w τ hw hξ (fun _ => v) t‖ ≤
      C*∑ k : Fin n, w.q t^(n-k.val)*
        ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hνS hD v)‖)
    (p : b.PeriodicGraph g) :
    ∃ q : b.PeriodicGraph g,
      let M := ρ.timeMap g w τ h.aestronglyMeasurable
      let B := (ρ.memLp_logDerivativeAction h τ (Lp.memLp (g.pathL2 q.val.1))).toLp
        (fun t => ρ.logDerivativeAction h τ t (g.pathL2 q.val.1 t))
      g.pathL2 q.val.1 = M (g.pathL2 p.val.1) ∧ q.val.2.1 = B + M p.val.2.1 := by
  obtain ⟨v,hv,hd,_⟩ := PeriodicWeakTrajectory.exists_closure_weighted_trajectory
    hS hbounded hνS hD b b.operator b.operator_isAssociated ρ hρ h τ hw hξ
    hC hell hA2 p.toTrajectory
  let q := v.toPeriodicGraph
  refine ⟨q,?_,?_⟩
  · apply Lp.ext
    filter_upwards [v.tracePathL2_ae, ρ.timeMap_ae g w τ h.aestronglyMeasurable (g.pathL2 p.val.1),
      g.pathL2_ae p.val.1] with t h1 h2 h3
    change g.pathL2 q.val.1 t = v.value t at h1
    rw [h1,h2,h3,hv]
    rfl
  · apply Lp.ext
    let B := (ρ.memLp_logDerivativeAction h τ (Lp.memLp (g.pathL2 q.val.1))).toLp
      (fun t => ρ.logDerivativeAction h τ t (g.pathL2 q.val.1 t))
    filter_upwards [v.derivative_L2.coeFn_toLp, v.tracePathL2_ae,
      (ρ.memLp_logDerivativeAction h τ (Lp.memLp (g.pathL2 q.val.1))).coeFn_toLp,
      ρ.timeMap_ae g w τ h.aestronglyMeasurable p.val.2.1,
      Lp.coeFn_add B (ρ.timeMap g w τ h.aestronglyMeasurable p.val.2.1)] with t h1 h2 h3 h4 h5
    change q.val.2.1 t = v.derivative t at h1
    change g.pathL2 q.val.1 t = v.value t at h2
    change B t = ρ.logDerivativeAction h τ t (g.pathL2 q.val.1 t) at h3
    simp only [Pi.add_apply] at h5
    change q.val.2.1 t = (B + ρ.timeMap g w τ h.aestronglyMeasurable p.val.2.1) t
    rw [h1,h5,h3,h4,h2,hd,hv]
    rfl

include hbounded hρ in
set_option maxHeartbeats 800000 in
/-- The weighted frozen graph bound with its real spatial commutator remainder.
The weighted weak graph and its domain regularity are constructed, not assumed. -/
theorem exists_weighted_frozen_graph_remainder_uniform (m : ℕ) (hm : 0 < m)
    (β τStar : ℝ) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s extension : Orientation) (w : TimeWeight)
        (h : TimeWeightRegularity w g β) (L τ : ℝ),
        L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        ∀ (hw : ∀ t (u : b.domain), (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ b.domain)
          (hξ : ∀ t (u : b.domain), (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ b.domain)
          (C Creg : ℝ), 0 ≤ C →
          (∀ v : b.domain, ‖domainSobolevJet hS hνS hD v‖ ≤ Creg*‖b.operator v‖) →
          (∀ t (v : b.domain), ‖allowedCommutatorPath b.operator ρ w τ hw hξ (fun _ => v) t‖ ≤
            C*∑ k : Fin n, w.q t^(n-k.val)*
              ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hνS hD v)‖) →
          ∀ p : b.PeriodicGraph g, ∃ q : b.PeriodicGraph g,
            let M := ρ.timeMap g w τ h.aestronglyMeasurable
            let μ := extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))
            g.pathL2 q.val.1 = M (g.pathL2 p.val.1) ∧
              ‖M p.val.2.1‖ + ‖M p.val.2.2‖ + ‖μ.map (M (g.pathL2 p.val.1))‖ ≤
                30*(‖M (b.evolution g s μ p)‖ + ‖q.val.2.2 - M p.val.2.2‖) := by
  obtain ⟨L₀,δ,hL,hδ,hgraph⟩ := b.weighted_frozen_graph_remainder_uniform ρ m hm β τStar hβ hτStar
  refine ⟨L₀,δ,hL,hδ,?_⟩
  intro g s extension w h L τ hLL hmesh hτ hw hξ C Creg hC hell hA2 p
  obtain ⟨q,hv,hd⟩ := b.exists_weighted_graph hS hbounded hνS hD ρ hρ
    h τ hw hξ hC hell hA2 p
  exact ⟨q,hv,hgraph g s extension w h L τ hLL hmesh hτ p q hv hd⟩

end Carleman.CoerciveForm
