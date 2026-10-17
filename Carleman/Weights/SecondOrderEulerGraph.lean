module

public import Carleman.Weights.WeightedEulerRemainder
public import Carleman.Spatial.SecondOrderCommutatorEnergy
public import Carleman.Continuous.NormDomination

/-! Closed actual weighted Euler operator graph for m=1. A3 absorbs the full
spatial commutator on D(A); arbitrary-domain Sobolev extension is unnecessary
for this estimate. This does not assert the higher-order manuscript theorem. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hν : ∀ᵐ x ∂ν, x ∈ S)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  (b : CoerciveForm (Lp ℝ 2 ν) W)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d 1 ν S) (hDV : b.domain ≤ V)
  (hD : b.domain ≤ sobolevSubspace d 2 ν S)
  (a : V → V → ℝ)
  (htest : ∀ u : b.domain, ∀ v : V,
    a (b.domain.inclusion hDV u) v = inner ℝ (b.operator u) (v : Lp ℝ 2 ν))
  (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)

include hbounded hρ htest
theorem secondOrder_weighted_euler_graph_uniform (c C Ccomm β τStar : ℝ)
    (hc : 0 < c) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        ∀ (hwV : ∀ i, ∀ v : V, (ρ.multiplier w τ (g.nodeTime i)).map (v : Lp ℝ 2 ν) ∈ V)
          (hw : ∀ i, ∀ u : b.domain,
            (ρ.multiplier w τ (g.nodeTime i)).map (u : Lp ℝ 2 ν) ∈ b.domain)
          (hξ : ∀ i, ∀ u : b.domain,
            (ρ.neg.multiplier w (-τ) (g.nodeTime i)).map (u : Lp ℝ 2 ν) ∈ b.domain),
        (∀ i (v : V), c*(conformingWeightedNorm hS hν hV (w.nodes g i)
          (ρ.multiplier w τ (g.nodeTime i)) v)^2 -
          C*(w.nodes g i*(ρ.multiplier w τ (g.nodeTime i)).seminorm (v : Lp ℝ 2 ν))^2 ≤
          a v (conformingWeight (ρ.multiplier w τ (g.nodeTime i)) (hwV i)
            (conformingWeight (ρ.multiplier w τ (g.nodeTime i)) (hwV i) v))) →
        (∀ i (v : b.domain), ‖conjugatedCommutator b.operator
          (ρ.multiplier w τ (g.nodeTime i)) (ρ.neg.multiplier w (-τ) (g.nodeTime i))
          (hw i) (hξ i) v‖ ≤ Ccomm*∑ k : Fin 2, (w.nodes g i)^(2-k.val)*
            ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖) →
        ∀ u : g.Sequence b.domain,
        let M := ρ.nodeMap g w τ
        let μ := fun i => (L*w.nodes g i)^2
        g.l2Norm (M (s.difference g (fun i => (u i : Lp ℝ 2 ν)))) +
          g.l2Norm (M (fun i => b.operator (u i))) +
          g.l2Norm (fun i => μ i • M (fun j => (u j : Lp ℝ 2 ν)) i) ≤
            12*g.l2Norm (M (b.eulerResidual g s μ u)) := by
  obtain ⟨H,hH,hsmall⟩ := secondOrder_commutator_small_shift hS hν hV hDV hD a b.operator
    htest hbounded ρ hρ c C Ccomm (1/12) hc hCcomm (by norm_num)
  obtain ⟨L₁,δ,hL₁,hδ,hgraph⟩ := b.weighted_euler_graph_remainder_uniform ρ 1 (by decide)
    β τStar hβ hτStar
  refine ⟨max H L₁,δ,hH.trans (le_max_left _ _),hδ,?_⟩
  intro g s w h L τ hL hmesh hτ hwV hw hξ ha hA2 u M μ
  have hL1 : 1 ≤ L := hH.trans ((le_max_left _ _).trans hL)
  have hHpow : H ≤ L^2 := by nlinarith [(le_max_left H L₁).trans hL]
  let v := ρ.weightedNodes g w τ b.domain hw u
  let R := (fun i => b.operator (v i)) - M (fun i => b.operator (u i))
  have hR : g.l2Norm R ≤ (1/12)*(g.l2Norm (M (fun i => b.operator (u i)))+
      g.l2Norm (fun i => μ i • M (fun j => (u j : Lp ℝ 2 ν)) i)) := by
    apply g.l2Norm_le_two R _ _ (by norm_num)
    intro i
    have hμ : H*w.q (g.nodeTime i)^2 ≤ μ i := by
      dsimp [μ,TimeWeight.nodes]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hHpow (sq_nonneg _)
    have he := hsmall w τ (g.nodeTime i) (μ i) hμ (hwV i) (hw i) (hξ i)
      (ha i) (hA2 i) (u i)
    rw [conjugatedCommutator_weighted_eq b.operator _ _ (hw i) (hξ i)
      (Filter.Eventually.of_forall (ρ.multiplier_inverse w τ (g.nodeTime i)))] at he
    exact he
  have hg := hgraph g s w h L τ ((le_max_right _ _).trans hL) hmesh hτ hw u
  change g.l2Norm (M (s.difference g (fun i => (u i : Lp ℝ 2 ν))))+
    g.l2Norm (M (fun i => b.operator (u i)))+
    g.l2Norm (fun i => μ i • M (fun j => (u j : Lp ℝ 2 ν)) i) ≤
      6*(g.l2Norm (M (b.eulerResidual g s μ u))+g.l2Norm R) at hg
  linarith [g.l2Norm_nonneg (M (s.difference g (fun i => (u i : Lp ℝ 2 ν))))]
end Carleman.CoerciveForm
