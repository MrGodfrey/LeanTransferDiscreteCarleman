module

public import Carleman.Spatial.InterpolatedParameterGraph
public import Carleman.Spatial.AllowedWeightData
public import Carleman.Weights.SecondOrderEulerSobolev

/-! General m manuscript R_{2m}: the sum of the actual derivative-field
sequence norms. Domain parameter interpolation remains an explicit premise. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hν : ∀ᵐ x ∂ν, x ∈ S)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  (b : CoerciveForm (Lp ℝ 2 ν) W)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hD : b.domain ≤ sobolevSubspace d (2*m) ν S) (a : V → V → ℝ)
  (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)

include hbounded hρ
theorem interpolated_weighted_euler_sobolev_uniform (hm : 0 < m)
    (Cinterp Creg c C Ccomm β τStar : ℝ) (hCi : 1 ≤ Cinterp) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hI : DomainParameterInterpolation hS hν hD Cinterp)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ δ K : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ 0 < K ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        AllowedWeightData hS hν hV hD a b.operator ρ w τ c C Ccomm →
        ∀ u : g.Sequence b.domain,
        g.l2Norm (ρ.nodeMap g w τ (s.difference g (fun i => (u i : Lp ℝ 2 ν)))) +
          WeakSobolevJet.nodeParameterNorm g (w.nodes g)
            (fun i => ρ.multiplier w τ (g.nodeTime i)) (fun i => domainSobolevJet hS hν hD (u i)) ≤
          K*g.l2Norm (ρ.nodeMap g w τ (b.eulerResidual g s (fun i => (L*w.nodes g i)^(2*m)) u)) := by
  obtain ⟨H,K,hH,hK,hR⟩ := interpolated_parameter_graph_uniform hS hν hD b.operator
    hbounded ρ hρ Cinterp Creg Ccomm hCi hCcomm hI hell
  obtain ⟨L₁,δ,hL₁,hδ,hgraph⟩ := b.interpolated_weighted_euler_graph_uniform
    hS hν hD ρ hm Cinterp Creg Ccomm β τStar hCi hCcomm hβ hτStar hI hell
  refine ⟨max H L₁,δ,12+12*(2*m+1)*K,hH.trans (le_max_left _ _),hδ,by positivity,?_⟩
  intro g s w h L τ hL hmesh hτ pos u
  let M := ρ.nodeMap (E := ℝ) g w τ
  let μ := fun i => (L*w.nodes g i)^(2*m)
  let X := M (fun i => b.operator (u i))
  let Y := fun i => μ i • M (fun j => (u j : Lp ℝ 2 ν)) i
  let F := g.l2Norm (M (b.eulerResidual g s μ u))
  have hL1 : 1 ≤ L := hH.trans ((le_max_left _ _).trans hL)
  have hHL : H ≤ L^(2*m) := ((le_max_left _ _).trans hL).trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hL1 (show 1 ≤ 2*m by omega))
  have hfield (k : Fin (2*m+1)) : g.l2Norm (fun i => (w.nodes g i)^(2*m-k.val) •
      (ρ.multiplier w τ (g.nodeTime i)).map (WeakSobolevJet.field k (domainSobolevJet hS hν hD (u i)))) ≤
      K*(g.l2Norm X+g.l2Norm Y) := by
    apply g.l2Norm_le_two _ X Y hK.le
    intro i
    rw [norm_smul,Real.norm_eq_abs]
    rw [abs_of_nonneg (pow_nonneg (show 0 ≤ w.nodes g i from w.nonneg _) _)]
    have hμ : H*w.q (g.nodeTime i)^(2*m) ≤ μ i := by
      dsimp [μ,TimeWeight.nodes]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hHL (pow_nonneg (w.nonneg _) _)
    exact (WeakSobolevJet.parameterNorm_component (w.nonneg _) _ _ k).trans
      (hR w τ (g.nodeTime i) (μ i) hμ (pos.domain_preserving _)
        (pos.inverse_preserving _) (pos.commutator _) (u i))
  have hs := Finset.sum_le_sum (s := Finset.univ) fun k _ => hfield k
  have hsum : WeakSobolevJet.nodeParameterNorm g (w.nodes g)
      (fun i => ρ.multiplier w τ (g.nodeTime i)) (fun i => domainSobolevJet hS hν hD (u i)) ≤
      (2*m+1)*K*(g.l2Norm X+g.l2Norm Y) := by
    simpa only [WeakSobolevJet.nodeParameterNorm,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_assoc] using hs
  have hg := hgraph g s w h L τ ((le_max_right _ _).trans hL) hmesh hτ
    (fun i => pos.domain_preserving _)
    (fun i => pos.inverse_preserving _) (fun i => pos.commutator _) u
  change g.l2Norm (M (s.difference g (fun i => (u i : Lp ℝ 2 ν))))+g.l2Norm X+g.l2Norm Y ≤ 12*F at hg
  have hd0 := g.l2Norm_nonneg (M (s.difference g (fun i => (u i : Lp ℝ 2 ν))))
  have hx0 := g.l2Norm_nonneg X
  have hy0 := g.l2Norm_nonneg Y
  change g.l2Norm (M (s.difference g (fun i => (u i : Lp ℝ 2 ν))))+_ ≤ (12+12*(2*m+1)*K)*F
  nlinarith [mul_le_mul_of_nonneg_left
    (show g.l2Norm X+g.l2Norm Y ≤ 12*F by linarith) (show 0 ≤ (2*m+1)*K by positivity)]
end Carleman.CoerciveForm
