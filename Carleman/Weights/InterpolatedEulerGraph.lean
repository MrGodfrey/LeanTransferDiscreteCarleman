module

public import Carleman.Weights.WeightedEulerRemainder
public import Carleman.Spatial.InterpolatedCommutator
public import Carleman.Continuous.NormDomination

/-! General m actual weighted Euler graph, conditional only on the explicitly
named original-domain interpolation input beyond the original A1/A2 data. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  (b : CoerciveForm (Lp ℝ 2 ν) W) (hD : b.domain ≤ sobolevSubspace d (2*m) ν S)
  (ρ : SpatialProfile ν)

theorem interpolated_weighted_euler_graph_uniform (hm : 0 < m)
    (Cinterp Creg Ccomm β τStar : ℝ) (hCi : 1 ≤ Cinterp)
    (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hI : DomainParameterInterpolation hS hν hD Cinterp)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        ∀ (hw : ∀ i (u : b.domain),
          (ρ.multiplier w τ (g.nodeTime i)).map (u : Lp ℝ 2 ν) ∈ b.domain)
          (hξ : ∀ i (u : b.domain),
          (ρ.neg.multiplier w (-τ) (g.nodeTime i)).map (u : Lp ℝ 2 ν) ∈ b.domain),
        (∀ i (v : b.domain), ‖conjugatedCommutator b.operator
          (ρ.multiplier w τ (g.nodeTime i)) (ρ.neg.multiplier w (-τ) (g.nodeTime i))
          (hw i) (hξ i) v‖ ≤ Ccomm*∑ k : Fin (2*m), (w.nodes g i)^(2*m-k.val)*
            ‖WeakSobolevJet.field k.castSucc (domainSobolevJet hS hν hD v)‖) →
        ∀ u : g.Sequence b.domain,
        let M := ρ.nodeMap g w τ
        let μ := fun i => (L*w.nodes g i)^(2*m)
        g.l2Norm (M (s.difference g (fun i => (u i : Lp ℝ 2 ν)))) +
          g.l2Norm (M (fun i => b.operator (u i))) +
          g.l2Norm (fun i => μ i • M (fun j => (u j : Lp ℝ 2 ν)) i) ≤
            12*g.l2Norm (M (b.eulerResidual g s μ u)) := by
  obtain ⟨H,hH,hsmall⟩ := interpolated_commutator_small_shift hS hν hD b.operator
    Cinterp Creg Ccomm (1/12) hCi hCcomm (by norm_num) hI hell
  obtain ⟨L₁,δ,hL₁,hδ,hgraph⟩ := b.weighted_euler_graph_remainder_uniform ρ m hm β τStar hβ hτStar
  refine ⟨max H L₁,δ,hH.trans (le_max_left _ _),hδ,?_⟩
  intro g s w h L τ hL hmesh hτ hw hξ hA2 u M μ
  have hL1 : 1 ≤ L := hH.trans ((le_max_left _ _).trans hL)
  have hHpow : H ≤ L^(2*m) := ((le_max_left _ _).trans hL).trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ 2*m by omega))
  let v := ρ.weightedNodes g w τ b.domain hw u
  let R := (fun i => b.operator (v i)) - M (fun i => b.operator (u i))
  have hR : g.l2Norm R ≤ (1/12)*(g.l2Norm (M (fun i => b.operator (u i)))+
      g.l2Norm (fun i => μ i • M (fun j => (u j : Lp ℝ 2 ν)) i)) := by
    apply g.l2Norm_le_two R _ _ (by norm_num)
    intro i
    have hμ : H*w.q (g.nodeTime i)^(2*m) ≤ μ i := by
      dsimp [μ,TimeWeight.nodes]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hHpow (pow_nonneg (w.nonneg _) _)
    have hinv : ∀ᵐ x ∂ν, (ρ.multiplier w τ (g.nodeTime i)).value x *
        (ρ.neg.multiplier w (-τ) (g.nodeTime i)).value x = 1 :=
      Filter.Eventually.of_forall (ρ.multiplier_inverse w τ (g.nodeTime i))
    have he := hsmall (w.nodes g i) (μ i) (w.lower _) hμ _ _ (hw i) (hξ i)
      hinv (hA2 i) (u i)
    rw [conjugatedCommutator_weighted_eq b.operator _ _ (hw i) (hξ i) hinv] at he
    exact he
  have hg := hgraph g s w h L τ ((le_max_right _ _).trans hL) hmesh hτ hw u
  change g.l2Norm (M (s.difference g (fun i => (u i : Lp ℝ 2 ν))))+
    g.l2Norm (M (fun i => b.operator (u i)))+
    g.l2Norm (fun i => μ i • M (fun j => (u j : Lp ℝ 2 ν)) i) ≤
      6*(g.l2Norm (M (b.eulerResidual g s μ u))+g.l2Norm R) at hg
  linarith [g.l2Norm_nonneg (M (s.difference g (fun i => (u i : Lp ℝ 2 ν))))]
end Carleman.CoerciveForm
