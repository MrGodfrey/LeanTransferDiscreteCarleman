module

public import Carleman.Spatial.AllowedWeightData
public import Carleman.Spatial.SecondOrderWeightData
public import Carleman.Continuous.WeightedTemporalDuality

/-! General-order actual allowed-weight temporal L² error. The single remaining
geometric premise is the stated original-domain parameter interpolation.
Continuous and adjoint solutions are constructed on the full periodic weak graph. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] [SFinite ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
  (hν : ∀ᵐ x ∂ν, x ∈ S)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 ν) W)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hD : b.domain ≤ sobolevSubspace d (2*m) ν S)
  (a : V → V → ℝ)
  (ρ : SpatialProfile ν) (hρ : SmoothOnClosure ρ.value S)

include hbounded hρ
set_option maxHeartbeats 800000 in
theorem interpolated_weighted_temporal_l2_uniform (hm : 0 < m)
    (Cinterp Creg c C Ccomm β τStar : ℝ) (hCi : 1 ≤ Cinterp)
    (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
    (hI : DomainParameterInterpolation hS hν hD Cinterp)
    (hell : ∀ v : b.domain, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖b.operator v‖) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        AllowedWeightData hS hν hV hD a b.operator ρ w τ c C Ccomm →
        AllowedWeightData hS hν hV hD a b.operator ρ.neg w (-τ) c C Ccomm →
        ∀ f : g.Sequence (Lp ℝ 2 ν),
        let μ := fun i => (L*w.nodes g i)^(2*m)
        let hμ : ∀ i, 0 ≤ μ i := fun _i => (even_two_mul m).pow_nonneg _
        let u := fun i => (b.eulerSolution g s μ hμ f i : Lp ℝ 2 ν)
        ∃ p : b.PeriodicGraph g,
          b.evolution g s (s.frozenMultiplier g μ) p = s.extensionLp g f ∧
          ‖ρ.timeMap g w τ h.aestronglyMeasurable (g.pathL2 p.val.1 - s.extensionLp g u)‖ ≤
            2160*g.dt*g.l2Norm (ρ.nodeMap g w τ f) := by
  obtain ⟨L₁,δ₁,hL₁,hδ₁,hEuler⟩ := b.interpolated_weighted_euler_graph_uniform
    hS hν hD ρ hm Cinterp Creg Ccomm β τStar hCi hCcomm hβ hτStar hI hell
  obtain ⟨L₂,δ₂,hL₂,hδ₂,hAdj⟩ := b.interpolated_weighted_frozen_graph_uniform
    hS hbounded hν hD ρ.neg hρ.neg hm Cinterp Creg Ccomm β τStar hCi hCcomm hβ hτStar hI hell
  obtain ⟨δ₃,hδ₃,hdual⟩ := b.weighted_temporal_duality_uniform ρ β τStar hβ hτStar
  refine ⟨max L₁ L₂,min δ₁ (min δ₂ δ₃),hL₁.trans (le_max_left _ _),
    lt_min hδ₁ (lt_min hδ₂ hδ₃),?_⟩
  intro g s w h L τ hL hmesh hτ pos inv f μ hμ u
  obtain ⟨p,q,hp,hq,herror⟩ := hdual g s w h
    (hmesh.trans ((min_le_right _ _).trans (min_le_right _ _))) τ hτ μ hμ f
  refine ⟨p,hp,?_⟩
  let M := ρ.timeMap (E := ℝ) g w τ h.aestronglyMeasurable
  let I := ρ.neg.timeMap (E := ℝ) g w (-τ) h.aestronglyMeasurable
  let e := g.pathL2 p.val.1 - s.extensionLp g u
  let fN := g.l2Norm (ρ.nodeMap g w τ f)
  have hDu : g.weightedNorm (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm)
      (s.difference g u) ≤ 12*fN := by
    have he := hEuler g s w h L τ ((le_max_left _ _).trans hL)
      (hmesh.trans (min_le_left _ _)) hτ
      (fun i => pos.domain_preserving (g.nodeTime i))
      (fun i => pos.inverse_preserving (g.nodeTime i))
      (fun i => pos.commutator (g.nodeTime i))
      (b.eulerSolution g s μ hμ f)
    have hr : b.eulerResidual g s μ (b.eulerSolution g s μ hμ f) = f :=
      funext (b.eulerSolution_equation g s μ hμ f)
    change _ ≤ 12*g.l2Norm (ρ.nodeMap g w τ (b.eulerResidual g s μ (b.eulerSolution g s μ hμ f))) at he
    rw [hr] at he
    rw [← ρ.nodeMap_l2Norm g w τ]
    change g.l2Norm (ρ.nodeMap g w τ (s.difference g u)) ≤ 12*fN
    linarith [g.l2Norm_nonneg (ρ.nodeMap g w τ (fun i => b.operator (b.eulerSolution g s μ hμ f i))),
      g.l2Norm_nonneg (fun i => μ i • ρ.nodeMap g w τ u i)]
  have hY : ‖I q.val.2.1‖ ≤ 60*‖M e‖ := by
    have he := hAdj g s.opposite s w h L (-τ) ((le_max_right _ _).trans hL)
      (hmesh.trans ((min_le_right _ _).trans (min_le_left _ _))) (by simpa only [abs_neg] using hτ)
      inv.domain_preserving inv.inverse_preserving inv.commutator q
    have hcancel : I (b.evolution g s.opposite (s.frozenMultiplier g μ) q) = M e := by
      rw [hq]
      exact ρ.inverse_timeMap_left g w τ h.aestronglyMeasurable (M e)
    change ‖I q.val.2.1‖+‖I q.val.2.2‖+
      ‖(s.frozenMultiplier g μ).map (I (g.pathL2 q.val.1))‖ ≤
      60*‖I (b.evolution g s.opposite (s.frozenMultiplier g μ) q)‖ at he
    rw [hcancel] at he
    linarith [norm_nonneg (I q.val.2.2),norm_nonneg ((s.frozenMultiplier g μ).map (I (g.pathL2 q.val.1)))]
  change ‖M e‖ ≤ 2160*g.dt*fN
  change ‖M e‖^2 ≤ (3*g.dt*g.weightedNorm
    (fun i => (ρ.multiplier w τ (g.nodeTime i)).seminorm) (s.difference g u))*‖I q.val.2.1‖ at herror
  have he : ‖M e‖^2 ≤ (2160*g.dt*fN)*‖M e‖ := by
    apply herror.trans
    have hb := mul_le_mul (mul_le_mul_of_nonneg_left hDu (show 0 ≤ 3*g.dt by positivity [g.dt_pos]))
      hY (norm_nonneg _) (by dsimp [fN]; positivity [g.dt_pos,g.l2Norm_nonneg (ρ.nodeMap g w τ f)])
    nlinarith only [hb]
  by_cases hz : ‖M e‖ = 0
  · rw [hz]
    dsimp [fN]
    positivity [g.dt_pos,g.l2Norm_nonneg (ρ.nodeMap g w τ f)]
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp
      (by simpa only [pow_two] using he)
end Carleman.CoerciveForm
