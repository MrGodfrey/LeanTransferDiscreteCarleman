module

public import Carleman.Weights.InterpolatedFrozenGraph
public import Carleman.Spatial.InterpolatedParameterGraph

/-! Full continuous frozen R_{2m} lifting of the parameter graph.
The geometric hI instance is supplied by the Lipschitz entrypoint. This uses actual Bochner derivative-field norms and a.e.
operator-domain representatives; no weighted graph estimate is assumed. -/
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
set_option maxHeartbeats 1200000 in
theorem interpolated_weighted_frozen_sobolev_uniform (hm : 0 < m)
    (Ci Creg Ccomm β τStar : ℝ) (hCi : 1 ≤ Ci) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hI : DomainParameterInterpolation hS hν hD Ci)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ δ K : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ 0 < K ∧
      ∀ (g : TimeGrid) (s extension : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        ∀ (hw : ∀ t, ∀ u : b.domain, (ρ.multiplier w τ t).map (u : Lp ℝ 2 ν) ∈ b.domain)
          (hξ : ∀ t, ∀ u : b.domain, (ρ.neg.multiplier w (-τ) t).map (u : Lp ℝ 2 ν) ∈ b.domain),
        (∀ t (v : b.domain), ‖allowedCommutatorPath b.operator ρ w τ hw hξ (fun _ => v) t‖ ≤
          Ccomm*∑ k : Fin (2*m), w.q t^(2*m-k.val)*
            ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖) →
        ∀ p : b.PeriodicGraph g,
        let M := ρ.timeMap g w τ h.aestronglyMeasurable
        let μ := extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))
        let J := fun t => domainSobolevJet hS hν hD
          (p.toTrajectory.domainValue t)
        MemLp J 2 g.timeMeasure ∧
          ‖M p.val.2.1‖+WeakSobolevJet.spacetimeParameterNorm g w.q (ρ.multiplier w τ) J ≤
            K*‖M (b.evolution g s μ p)‖ := by
  obtain ⟨H,K,hH,hK,hR⟩ := interpolated_parameter_graph_uniform hS hν hD b.operator
    hbounded ρ hρ Ci Creg Ccomm hCi hCcomm hI hell
  obtain ⟨L₁,δ₁,hL₁,hδ₁,hshift⟩ := frozen_shift_margin_uniform m hm β hβ H
  obtain ⟨L₂,δ₂,hL₂,hδ₂,hgraph⟩ := b.interpolated_weighted_frozen_graph_uniform
    hS hbounded hν hD ρ hρ hm Ci Creg Ccomm β τStar hCi hCcomm hβ hτStar hI hell
  refine ⟨max L₁ L₂,min δ₁ δ₂,60+60*(2*m+1)*K,hL₁.trans (le_max_left _ _),
    lt_min hδ₁ hδ₂,by positivity,?_⟩
  intro g s extension w h L τ hL hmesh hτ hw hξ hA2 p M μ J
  have hJ : MemLp J 2 g.timeMeasure := p.toTrajectory.domainSobolev_L2 hS hν hD Creg hell
  have hlow : ∀ᵐ t ∂g.timeMeasure, H*w.q t^(2*m) ≤ μ.value t :=
    hshift g extension w h L ((le_max_left _ _).trans hL) (hmesh.trans (min_le_left _ _))
  have hfield (k : Fin (2*m+1)) :
      bochnerL2Norm g.timeMeasure (WeakSobolevJet.parameterTimeField w.q (ρ.multiplier w τ) J k) ≤
        K*(‖M p.val.2.2‖+‖μ.map (M (g.pathL2 p.val.1))‖) := by
    have hf : MemLp (WeakSobolevJet.parameterTimeField w.q (ρ.multiplier w τ) J k) 2 g.timeMeasure := by
      simpa only [one_mul] using WeakSobolevJet.memLp_parameterTimeField g w ρ τ 1 h.aestronglyMeasurable hJ k
    rw [bochnerL2Norm_eq _ hf]
    apply lp_norm_le_two _ (M p.val.2.2) (μ.map (M (g.pathL2 p.val.1))) hK.le
    filter_upwards [hf.coeFn_toLp,hlow,p.toTrajectory_operator_ae,p.toTrajectory.domainValue_ae,
      g.pathL2_ae p.val.1,ρ.timeMap_ae g w τ h.aestronglyMeasurable p.val.2.2,
      ρ.timeMap_ae g w τ h.aestronglyMeasurable (g.pathL2 p.val.1),
      μ.map_ae (M (g.pathL2 p.val.1))] with t hf ht hA hDval hval hMA hMv hμ
    rw [hf,WeakSobolevJet.parameterTimeField_norm _ _ _ _ (w.nonneg t)]
    have he := (WeakSobolevJet.parameterNorm_component (w.nonneg t) (ρ.multiplier w τ t) (J t) k).trans
      (hR w τ t (μ.value t) ht (hw t) (hξ t) (hA2 t) (p.toTrajectory.domainValue t))
    change M p.val.2.2 t = _ at hMA
    change M (g.pathL2 p.val.1) t = _ at hMv
    change g.pathL2 p.val.1 t = p.toTrajectory.value t at hval
    rw [hMA,hμ,hMv,hval,← hDval,← hA]
    exact he
  have hsum : WeakSobolevJet.spacetimeParameterNorm g w.q (ρ.multiplier w τ) J ≤
      (2*m+1)*K*(‖M p.val.2.2‖+‖μ.map (M (g.pathL2 p.val.1))‖) := by
    have he := Finset.sum_le_sum (s := Finset.univ) fun k _ => hfield k
    simpa only [WeakSobolevJet.spacetimeParameterNorm,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_assoc] using he
  have hg := hgraph g s extension w h L τ ((le_max_right _ _).trans hL)
    (hmesh.trans (min_le_right _ _)) hτ hw hξ hA2 p
  refine ⟨hJ,?_⟩
  have hd0 := norm_nonneg (M p.val.2.1)
  have hx0 := norm_nonneg (M p.val.2.2)
  have hy0 := norm_nonneg (μ.map (M (g.pathL2 p.val.1)))
  change ‖M p.val.2.1‖+‖M p.val.2.2‖+‖μ.map (M (g.pathL2 p.val.1))‖ ≤
    60*‖M (b.evolution g s μ p)‖ at hg
  have hmul := mul_le_mul_of_nonneg_left
    (show ‖M p.val.2.2‖+‖μ.map (M (g.pathL2 p.val.1))‖ ≤ 60*‖M (b.evolution g s μ p)‖ by linarith)
    (show 0 ≤ (2*m+1)*K by positivity)
  nlinarith
end Carleman.CoerciveForm
