module

public import Carleman.Weights.InterpolatedEulerGraph
public import Carleman.Weights.WeightedGraphCommutator
public import Carleman.Weights.ShiftedGraphRemainder

/-! General-order shift weighted operator graph with original-domain
parameter interpolation as a reusable analytic interface. The geometric entrypoint proves it.
The weighted graph and a.e. domain representatives are constructed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hν : ∀ᵐ x ∂ν, x ∈ S)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 ν) W)
  (hD : b.domain ≤ sobolevSubspace d (2*m) ν S)
  (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)

include hbounded hρ
set_option maxHeartbeats 800000 in
theorem interpolated_weighted_shift_graph_uniform (hm : 0 < m)
    (Cinterp Creg Ccomm β τStar : ℝ) (hCi : 1 ≤ Cinterp)
    (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hI : DomainParameterInterpolation hS hν hD Cinterp)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
        (L τ : ℝ) (hLpos : 0 < L), L₀ ≤ L → |τ| ≤ τStar →
        ∀ (hw : ∀ t, ∀ u : b.domain, (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ b.domain)
          (hξ : ∀ t, ∀ u : b.domain, (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ b.domain),
        (∀ t (v : b.domain), ‖allowedCommutatorPath b.operator ρ w τ hw hξ (fun _ => v) t‖ ≤
          Ccomm*∑ k : Fin (2*m), w.q t^(2*m-k.val)*
            ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖) →
        ∀ p : b.PeriodicGraph g,
        let M := ρ.timeMap g w τ h.aestronglyMeasurable
        let μ := h.shiftMultiplier m L hLpos
        ‖M p.val.2.1‖ + ‖M p.val.2.2‖ + ‖μ.map (M (g.pathL2 p.val.1))‖ ≤
          60*‖M (b.evolution g s μ p)‖ := by
  obtain ⟨H,_,hsmall⟩ := interpolated_commutator_small_shift hS hν hD b.operator
    Cinterp Creg Ccomm (1/60) hCi hCcomm (by norm_num) hI hell
  obtain ⟨L₁,hL₁,hshift⟩ := continuous_shift_margin_uniform m hm H
  obtain ⟨L₂,hL₂,hgraph⟩ := b.weighted_shift_graph_remainder_uniform ρ m hm β τStar hβ hτStar
  refine ⟨max L₁ L₂,hL₁.trans (le_max_left _ _),?_⟩
  intro g s w h L τ hLpos hL hτ hw hξ hA2 p M μ
  obtain ⟨q,hv,hd⟩ := b.exists_weighted_graph hS hbounded hν hD ρ hρ
    h τ hw hξ hCcomm hell hA2 p
  have hg := hgraph g s w h L τ hLpos ((le_max_right _ _).trans hL) hτ p q hv hd
  let R := q.val.2.2 - M p.val.2.2
  have hlow : ∀ᵐ t ∂g.timeMeasure, H*w.q t^(2*m) ≤ μ.value t :=
    Filter.Eventually.of_forall fun t => by
      change H*w.q t^(2*m) ≤ (L*w.q t)^(2*m)
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (hshift L ((le_max_left _ _).trans hL)) (pow_nonneg (w.nonneg t) _)
  have hR : ‖R‖ ≤ (1/60)*(‖M p.val.2.2‖+‖μ.map (M (g.pathL2 p.val.1))‖) := by
    apply lp_norm_le_two R (M p.val.2.2) (μ.map (M (g.pathL2 p.val.1))) (by norm_num)
    filter_upwards [hlow,b.weighted_graph_commutator_ae ρ g w τ h.aestronglyMeasurable hw hξ p q hv,
      b.weighted_graph_domain_ae ρ g w τ h.aestronglyMeasurable hw p q hv,
      p.toTrajectory_operator_ae,p.toTrajectory.domainValue_ae,g.pathL2_ae p.val.1,
      ρ.timeMap_ae g w τ h.aestronglyMeasurable p.val.2.2,
      ρ.timeMap_ae g w τ h.aestronglyMeasurable (g.pathL2 p.val.1),
      μ.map_ae (M (g.pathL2 p.val.1))] with t ht hr hd hpA hpD hpv hMA hMv hμ
    have he := hsmall (w.q t) (μ.value t) (w.lower t) ht _ _ (hw t) (hξ t)
      (Filter.Eventually.of_forall (ρ.multiplier_inverse w τ t)) (hA2 t) (p.toTrajectory.domainValue t)
    change g.pathL2 p.val.1 t = p.toTrajectory.value t at hpv
    change R t = allowedCommutatorPath b.operator ρ w τ hw hξ q.toTrajectory.domainValue t at hr
    change M p.val.2.2 t = _ at hMA
    change M (g.pathL2 p.val.1) t = _ at hMv
    rw [hr]
    unfold allowedCommutatorPath
    rw [hd,hMA,hμ,hMv,hpv,← hpD,← hpA]
    exact he
  change ‖M p.val.2.1‖+‖M p.val.2.2‖+‖μ.map (M (g.pathL2 p.val.1))‖ ≤
    30*(‖M (b.evolution g s μ p)‖+‖R‖) at hg
  linarith [norm_nonneg (M p.val.2.1)]
end Carleman.CoerciveForm
