module

public import Carleman.Weights.WeightedGraphCommutator
public import Carleman.Continuous.WeightedTemporalDuality

/-! The actual periodic adjoint for the squared reciprocal weight load. Its
weighted derivative is estimated uniformly, retaining only the genuine spatial
commutator. This is not the closed weighted graph or time-error theorem. -/
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
set_option maxHeartbeats 800000 in
/-- Here M is the inverse weight and W its reciprocal. The load is W(W e),
and M cancels one W exactly. Every adjoint and weighted graph is constructed. -/
theorem weighted_adjoint_remainder_uniform (m : ℕ) (hm : 0 < m)
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
          ∀ e : Lp (Lp ℝ 2 ν) 2 g.timeMeasure, ∃ Y Z : b.PeriodicGraph g,
            let M := ρ.timeMap (E := ℝ) g w τ h.aestronglyMeasurable
            let W := ρ.neg.timeMap (E := ℝ) g w (-τ) h.aestronglyMeasurable
            let μ := extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))
            b.evolution g s.opposite μ Y = W (W e) ∧
            g.pathL2 Z.val.1 = M (g.pathL2 Y.val.1) ∧
            ‖M Y.val.2.1‖ ≤ 30*(‖W e‖ + ‖Z.val.2.2 - M Y.val.2.2‖) ∧
            (Z.val.2.2 - M Y.val.2.2) =ᵐ[g.timeMeasure]
              allowedCommutatorPath b.operator ρ w τ hw hξ Z.toTrajectory.domainValue := by
  obtain ⟨L₀,δ,hL,hδ,hgraph⟩ := b.exists_weighted_frozen_graph_remainder_uniform
    hS hbounded hνS hD ρ hρ m hm β τStar hβ hτStar
  refine ⟨L₀,δ,hL,hδ,?_⟩
  intro g s extension w h L τ hLL hmesh hτ hw hξ C Creg hC hell hA2 e
  let M := ρ.timeMap (E := ℝ) g w τ h.aestronglyMeasurable
  let W := ρ.neg.timeMap (E := ℝ) g w (-τ) h.aestronglyMeasurable
  let μ := extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))
  have hn : ∀ᵐ t ∂g.timeMeasure, 0 ≤ μ.value t := Filter.Eventually.of_forall fun t => by
    change 0 ≤ extension.extension g (fun i => (L*w.nodes g i)^(2*m)) t
    cases extension <;> exact (even_two_mul m).pow_nonneg _
  obtain ⟨Y,hY,_⟩ := b.existsUnique_variable_periodic g s.opposite μ hn (W (W e))
  obtain ⟨Z,hZ,hbound⟩ := hgraph g s.opposite extension w h L τ hLL hmesh hτ hw hξ C Creg hC hell hA2 Y
  refine ⟨Y,Z,hY,hZ,?_,b.weighted_graph_commutator_ae ρ g w τ h.aestronglyMeasurable hw hξ Y Z hZ⟩
  have hcancel : M (b.evolution g s.opposite μ Y) = W e := by
    rw [hY]
    exact ρ.timeMap_inverse g w τ h.aestronglyMeasurable (W e)
  change ‖M Y.val.2.1‖ + ‖M Y.val.2.2‖ + ‖μ.map (M (g.pathL2 Y.val.1))‖ ≤
    30*(‖M (b.evolution g s.opposite μ Y)‖ + ‖Z.val.2.2 - M Y.val.2.2‖) at hbound
  rw [hcancel] at hbound
  change ‖M Y.val.2.1‖ ≤ _
  linarith [norm_nonneg (M Y.val.2.2), norm_nonneg (μ.map (M (g.pathL2 Y.val.1)))]

end Carleman.CoerciveForm
