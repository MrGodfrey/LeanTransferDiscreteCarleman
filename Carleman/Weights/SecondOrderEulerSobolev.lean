module

public import Carleman.Spatial.SecondOrderParameterGraph
public import Carleman.Spatial.SecondOrderWeightData
public import Carleman.Weights.SecondOrderEulerGraph

/-! The manuscript sum of derivative-field sequence norms, and the full m=1
weighted Euler estimate on every D(A)-valued periodic sequence. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

def nodeParameterNorm (g : TimeGrid) (r : g.Sequence ℝ)
    (σ : g.Index → BoundedMultiplier ν) (u : g.Sequence (WeakSobolevJet d n ν S)) : ℝ :=
  ∑ k : Fin (n+1), g.l2Norm (fun i => r i^(n-k.val) • (σ i).map (field k (u i)))
end Carleman.WeakSobolevJet

namespace Carleman.CoerciveForm
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hν : ∀ᵐ x ∂ν, x ∈ S)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  (b : CoerciveForm (Lp ℝ 2 ν) W)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d 1 ν S) (hDV : b.domain ≤ V)
  (hD : b.domain ≤ sobolevSubspace d 2 ν S) (a : V → V → ℝ)
  (htest : ∀ u : b.domain, ∀ v : V,
    a (b.domain.inclusion hDV u) v = inner ℝ (b.operator u) (v : Lp ℝ 2 ν))
  (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)

include hbounded hρ htest
theorem secondOrder_weighted_euler_sobolev_uniform (c C Ccomm Creg β τStar : ℝ)
    (hc : 0 < c) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ δ K : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ 0 < K ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        SecondOrderWeightData hS hν hV hD a b.operator ρ w τ c C Ccomm →
        ∀ u : g.Sequence b.domain,
        g.l2Norm (ρ.nodeMap g w τ (s.difference g (fun i => (u i : Lp ℝ 2 ν)))) +
          WeakSobolevJet.nodeParameterNorm g (w.nodes g)
            (fun i => ρ.multiplier w τ (g.nodeTime i)) (fun i => domainSobolevJet hS hν hD (u i)) ≤
          K*g.l2Norm (ρ.nodeMap g w τ (b.eulerResidual g s (fun i => (L*w.nodes g i)^2) u)) := by
  obtain ⟨H,K,hH,hK,hR⟩ := secondOrder_parameter_graph_uniform hS hν hV hDV hD a b.operator htest
    hbounded ρ hρ c C Ccomm Creg hc hCcomm hell
  obtain ⟨L₁,δ,hL₁,hδ,hgraph⟩ := b.secondOrder_weighted_euler_graph_uniform
    hS hbounded hν hV hDV hD a htest ρ hρ c C Ccomm β τStar hc hCcomm hβ hτStar
  refine ⟨max H L₁,δ,12+36*K,hH.trans (le_max_left _ _),hδ,by positivity,?_⟩
  intro g s w h L τ hL hmesh hτ pos u
  let M := ρ.nodeMap (E := ℝ) g w τ
  let μ := fun i => (L*w.nodes g i)^2
  let X := M (fun i => b.operator (u i))
  let Y := fun i => μ i • M (fun j => (u j : Lp ℝ 2 ν)) i
  let F := g.l2Norm (M (b.eulerResidual g s μ u))
  have hL1 : 1 ≤ L := hH.trans ((le_max_left _ _).trans hL)
  have hHL : H ≤ L^2 := by nlinarith [(le_max_left H L₁).trans hL]
  have hfield (k : Fin 3) : g.l2Norm (fun i => (w.nodes g i)^(2-k.val) •
      (ρ.multiplier w τ (g.nodeTime i)).map (WeakSobolevJet.field k (domainSobolevJet hS hν hD (u i)))) ≤
      K*(g.l2Norm X+g.l2Norm Y) := by
    apply g.l2Norm_le_two _ X Y hK.le
    intro i
    rw [norm_smul,Real.norm_eq_abs]
    rw [abs_of_nonneg (pow_nonneg (show 0 ≤ w.nodes g i from w.nonneg _) _)]
    have hμ : H*w.q (g.nodeTime i)^2 ≤ μ i := by
      dsimp [μ,TimeWeight.nodes]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hHL (sq_nonneg _)
    exact (WeakSobolevJet.parameterNorm_component (w.nonneg _) _ _ k).trans
      (hR w τ (g.nodeTime i) (μ i) hμ (pos.form_preserving _) (pos.domain_preserving _)
        (pos.inverse_preserving _) (pos.coercive _) (pos.commutator _) (u i))
  have hs := Finset.sum_le_sum (s := Finset.univ) fun k _ => hfield k
  have hsum : WeakSobolevJet.nodeParameterNorm g (w.nodes g)
      (fun i => ρ.multiplier w τ (g.nodeTime i)) (fun i => domainSobolevJet hS hν hD (u i)) ≤
      3*K*(g.l2Norm X+g.l2Norm Y) := by
    simpa only [WeakSobolevJet.nodeParameterNorm,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using hs
  have hg := hgraph g s w h L τ ((le_max_right _ _).trans hL) hmesh hτ
    (fun i => pos.form_preserving _) (fun i => pos.domain_preserving _)
    (fun i => pos.inverse_preserving _) (fun i => pos.coercive _) (fun i => pos.commutator _) u
  change g.l2Norm (M (s.difference g (fun i => (u i : Lp ℝ 2 ν))))+g.l2Norm X+g.l2Norm Y ≤ 12*F at hg
  have hd0 := g.l2Norm_nonneg (M (s.difference g (fun i => (u i : Lp ℝ 2 ν))))
  have hx0 := g.l2Norm_nonneg X
  have hy0 := g.l2Norm_nonneg Y
  change g.l2Norm (M (s.difference g (fun i => (u i : Lp ℝ 2 ν))))+_ ≤ (12+36*K)*F
  nlinarith [mul_le_mul_of_nonneg_left
    (show g.l2Norm X+g.l2Norm Y ≤ 12*F by linarith) (show 0 ≤ 3*K by positivity)]
end Carleman.CoerciveForm
