module

public import Carleman.Weights.SecondOrderEulerGraph
public import Carleman.Weights.WeightedGraphCommutator

/-! A3 closes the actual m=1 frozen weighted operator graph. All a.e. domain
representatives and the weighted graph are constructed by the existing B1/A2
interfaces. No neighborhood smoothness or graph estimate is a premise. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hν : ∀ᵐ x ∂ν, x ∈ S)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 ν) W)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d 1 ν S) (hDV : b.domain ≤ V)
  (hD : b.domain ≤ sobolevSubspace d 2 ν S)
  (a : V → V → ℝ)
  (htest : ∀ u : b.domain, ∀ v : V,
    a (b.domain.inclusion hDV u) v = inner ℝ (b.operator u) (v : Lp ℝ 2 ν))
  (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)

include hbounded hρ htest
set_option maxHeartbeats 800000 in
theorem secondOrder_weighted_frozen_graph_uniform (c C Ccomm β τStar : ℝ)
    (hc : 0 < c) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s extension : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        ∀ (hwV : ∀ t, ∀ v : V, (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V)
          (hw : ∀ t, ∀ u : b.domain, (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ b.domain)
          (hξ : ∀ t, ∀ u : b.domain, (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ b.domain),
        (∀ t (v : V), c*(conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v)^2 -
          C*(w.q t*(ρ.multiplier w τ t).seminorm (v : Lp ℝ 2 ν))^2 ≤
          a v (conformingWeight (ρ.multiplier w τ t) (hwV t)
            (conformingWeight (ρ.multiplier w τ t) (hwV t) v))) →
        (∀ t (v : b.domain), ‖allowedCommutatorPath b.operator ρ w τ hw hξ (fun _ => v) t‖ ≤
          Ccomm*∑ k : Fin 2, w.q t^(2-k.val)*
            ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖) →
        ∀ Creg : ℝ, (∀ v : b.domain, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖b.operator v‖) →
        ∀ p : b.PeriodicGraph g,
        let M := ρ.timeMap g w τ h.aestronglyMeasurable
        let μ := extension.frozenMultiplier g (fun i => (L*w.nodes g i)^2)
        ‖M p.val.2.1‖ + ‖M p.val.2.2‖ + ‖μ.map (M (g.pathL2 p.val.1))‖ ≤
          60*‖M (b.evolution g s μ p)‖ := by
  obtain ⟨H,_,hsmall⟩ := secondOrder_commutator_small_shift hS hν hV hDV hD a b.operator
    htest hbounded ρ hρ c C Ccomm (1/60) hc hCcomm (by norm_num)
  obtain ⟨L₁,δ₁,hL₁,hδ₁,hshift⟩ := frozen_shift_margin_uniform 1 (by decide) β hβ H
  obtain ⟨L₂,δ₂,hL₂,hδ₂,hgraph⟩ := b.exists_weighted_frozen_graph_remainder_uniform
    hS hbounded hν hD ρ hρ 1 (by decide) β τStar hβ hτStar
  refine ⟨max L₁ L₂,min δ₁ δ₂,hL₁.trans (le_max_left _ _),lt_min hδ₁ hδ₂,?_⟩
  intro g s extension w h L τ hL hmesh hτ hwV hw hξ ha hA2 Creg hell p M μ
  obtain ⟨q,hv,hg⟩ := hgraph g s extension w h L τ ((le_max_right _ _).trans hL)
    (hmesh.trans (min_le_right _ _)) hτ hw hξ Ccomm Creg hCcomm hell hA2 p
  let R := q.val.2.2 - M p.val.2.2
  have hlow : ∀ᵐ t ∂g.timeMeasure, H*w.q t^2 ≤ μ.value t :=
    hshift g extension w h L ((le_max_left _ _).trans hL) (hmesh.trans (min_le_left _ _))
  have hR : ‖R‖ ≤ (1/60)*(‖M p.val.2.2‖+‖μ.map (M (g.pathL2 p.val.1))‖) := by
    apply lp_norm_le_two R (M p.val.2.2) (μ.map (M (g.pathL2 p.val.1))) (by norm_num)
    filter_upwards [hlow,b.weighted_graph_commutator_ae ρ g w τ h.aestronglyMeasurable hw hξ p q hv,
      b.weighted_graph_domain_ae ρ g w τ h.aestronglyMeasurable hw p q hv,
      p.toTrajectory_operator_ae,p.toTrajectory.domainValue_ae,g.pathL2_ae p.val.1,
      ρ.timeMap_ae g w τ h.aestronglyMeasurable p.val.2.2,
      ρ.timeMap_ae g w τ h.aestronglyMeasurable (g.pathL2 p.val.1),
      μ.map_ae (M (g.pathL2 p.val.1))] with t ht hr hd hpA hpD hpv hMA hMv hμ
    have he := hsmall w τ t (μ.value t) ht (hwV t) (hw t) (hξ t) (ha t) (hA2 t)
      (p.toTrajectory.domainValue t)
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
