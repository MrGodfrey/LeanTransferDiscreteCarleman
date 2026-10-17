module

public import Carleman.Weights.SecondOrderTemporalL2
public import Carleman.Weights.FrozenErrorEnergy
public import Carleman.Continuous.WeightedGraphErrorNorm

/-! Both manuscript temporal rates for m=1 in the actual allowed-weight
Bochner L² and N norms. A1 is used only for Sobolev finiteness, and A3 for
the energy product bound. The full higher-order theorem remains separate. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] [SFinite ν]
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
set_option maxHeartbeats 1200000 in
theorem secondOrder_weighted_temporal_error_uniform (c C Ccomm β τStar : ℝ)
    (hc : 0 < c) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        SecondOrderWeightData hS hν hV hD a b.operator ρ w τ c C Ccomm →
        SecondOrderWeightData hS hν hV hD a b.operator ρ.neg w (-τ) c C Ccomm →
        ∀ Creg : ℝ, (∀ v : b.domain, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖b.operator v‖) →
        ∀ f : g.Sequence (Lp ℝ 2 ν),
        let μ := fun i => (L*w.nodes g i)^2
        let hμ : ∀ i, 0 ≤ μ i := fun _i => sq_nonneg _
        let u := b.eulerSolution g s μ hμ f
        let F := g.l2Norm (ρ.nodeMap g w τ f)
        ∃ p : b.PeriodicGraph g,
          b.evolution g s (s.frozenMultiplier g μ) p = s.extensionLp g f ∧
          bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map
            (p.toTrajectory.value t-s.extension g (fun i => (u i : Lp ℝ 2 ν)) t)) ≤ 2160*g.dt*F ∧
          MemLp (fun t => domainSobolevJet hS hν hV
            (b.domain.inclusion hDV (p.toTrajectory.domainError s u t))) 2 g.timeMeasure ∧
          WeakSobolevJet.spacetimeWeightedNorm g w.q (ρ.multiplier w τ)
            (fun t => domainSobolevJet hS hν hV
              (b.domain.inclusion hDV (p.toTrajectory.domainError s u t))) ≤
            Real.sqrt (466560/c)*Real.sqrt g.dt*F := by
  obtain ⟨L₁,δ₁,hL₁,hδ₁,hl2⟩ := b.secondOrder_weighted_temporal_l2_uniform
    hS hbounded hν hV hDV hD a htest ρ hρ c C Ccomm β τStar hc hCcomm hβ hτStar
  obtain ⟨L₂,δ₂,hL₂,hδ₂,hEuler⟩ := b.secondOrder_weighted_euler_graph_uniform
    hS hbounded hν hV hDV hD a htest ρ hρ c C Ccomm β τStar hc hCcomm hβ hτStar
  obtain ⟨L₃,δ₃,hL₃,hδ₃,hCont⟩ := b.secondOrder_weighted_frozen_graph_uniform
    hS hbounded hν hV hDV hD a htest ρ hρ c C Ccomm β τStar hc hCcomm hβ hτStar
  obtain ⟨L₄,δ₄,hL₄,hδ₄,hEnergy⟩ := frozen_spacetime_operator_energy_uniform
    hS hν hV hDV a b.operator htest (by decide : 0 < 1) C β hβ
  let δ₅ := cellThreshold β τStar ρ.bound
  refine ⟨max L₁ (max L₂ (max L₃ L₄)),min δ₁ (min δ₂ (min δ₃ (min δ₄ δ₅))),
    hL₁.trans (le_max_left _ _),
    lt_min hδ₁ (lt_min hδ₂ (lt_min hδ₃ (lt_min hδ₄ (cellThreshold_pos hβ hτStar ρ.bound_nonneg)))),?_⟩
  intro g s w h L τ hL hmesh hτ pos inv Creg hell f μ hμ u F
  have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL2 : L₂ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL3 : L₃ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hL4 : L₄ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hm1 : g.dt*w.max^2 ≤ δ₁ := hmesh.trans (min_le_left _ _)
  have hm2 : g.dt*w.max^2 ≤ δ₂ := hmesh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 : g.dt*w.max^2 ≤ δ₃ := hmesh.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hm4 : g.dt*w.max^2 ≤ δ₄ := hmesh.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hm5 : g.dt*w.max^2 ≤ δ₅ := hmesh.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨p,hp,herr⟩ := hl2 g s w h L τ hL1 hm1 hτ pos inv Creg hell f
  let U := fun i => (u i : Lp ℝ 2 ν)
  let M := ρ.timeMap (E := ℝ) g w τ h.aestronglyMeasurable
  let J := fun t => domainSobolevJet hS hν hV (b.domain.inclusion hDV (p.toTrajectory.domainError s u t))
  let N := WeakSobolevJet.spacetimeWeightedNorm g w.q (ρ.multiplier w τ) J
  have hJ : MemLp J 2 g.timeMeasure :=
    p.toTrajectory.domainError_conforming_L2 hS hν hV hDV hD b.operator Creg hell s u
  refine ⟨p,hp,?_,hJ,?_⟩
  · rw [p.weighted_error_bochnerNorm ρ w τ h.aestronglyMeasurable]
    exact herr
  have hDu : g.l2Norm (ρ.nodeMap g w τ (s.difference g U)) ≤ 12*F := by
    have he := hEuler g s w h L τ hL2 hm2 hτ
      (fun i => pos.form_preserving (g.nodeTime i)) (fun i => pos.domain_preserving (g.nodeTime i))
      (fun i => pos.inverse_preserving (g.nodeTime i))
      (fun i => pos.coercive (g.nodeTime i)) (fun i => pos.commutator (g.nodeTime i)) u
    have hr : b.eulerResidual g s μ u = f := funext (b.eulerSolution_equation g s μ hμ f)
    change _ ≤ 12*g.l2Norm (ρ.nodeMap g w τ (b.eulerResidual g s μ u)) at he
    rw [hr] at he
    linarith [g.l2Norm_nonneg (ρ.nodeMap g w τ (fun i => b.operator (u i))),
      g.l2Norm_nonneg (fun i => μ i • ρ.nodeMap g w τ U i)]
  have hDt : ‖M (s.extensionLp g (s.difference g U))‖ ≤ 36*F := by
    have hh := (ρ.timeMap_extension_norm_comparison h s τ τStar hτStar hτ hm5 (s.difference g U)).1
    rw [← ρ.nodeMap_l2Norm g w τ] at hh
    linarith
  have hCt : ‖M p.val.2.1‖ ≤ 180*F := by
    have he := hCont g s s w h L τ hL3 hm3 hτ pos.form_preserving pos.domain_preserving
      pos.inverse_preserving pos.coercive pos.commutator Creg hell p
    change _ ≤ 60*‖M (b.evolution g s (s.frozenMultiplier g μ) p)‖ at he
    rw [hp] at he
    have hh := (ρ.timeMap_extension_norm_comparison h s τ τStar hτStar hτ hm5 f).1
    rw [← ρ.nodeMap_l2Norm g w τ] at hh
    linarith [norm_nonneg (M p.val.2.2),norm_nonneg ((s.frozenMultiplier g μ).map (M (g.pathL2 p.val.1)))]
  have henergy := hEnergy L hL4 g s ρ w τ c h hm4 pos.form_preserving
    (by simpa only [pow_one] using pos.coercive)
    (p.toTrajectory.domainError s u) hJ (p.toTrajectory.domainError_operator_L2 s u)
  let pair := p.frozenEulerPair s μ hμ f hp
  have hres := p.toTrajectory.domainError_residual_ae s u μ f pair.continuous_equation pair.discrete_equation
  have hresw : (fun t => (ρ.multiplier w τ t).map (b.operator (p.toTrajectory.domainError s u t)+
      s.extension g μ t • (p.toTrajectory.domainError s u t : Lp ℝ 2 ν))) =ᵐ[g.timeMeasure]
      (fun t => (ρ.multiplier w τ t).map (s.extension g (s.difference g U) t) -
        s.sign • (ρ.multiplier w τ t).map (p.toTrajectory.derivative t)) := by
    filter_upwards [hres] with t ht
    rw [ht]
    change (ρ.multiplier w τ t).linearMap (_ - _ • _) = _
    rw [map_sub,map_smul]
    rfl
  have hvalw : (fun t => (ρ.multiplier w τ t).map (p.toTrajectory.domainError s u t : Lp ℝ 2 ν)) =ᵐ[g.timeMeasure]
      (fun t => (ρ.multiplier w τ t).map (p.toTrajectory.value t-s.extension g U t)) :=
    (p.toTrajectory.domainError_value_ae s u).mono fun t ht => congrArg _ ht
  change c*N^2 ≤ bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map
    (b.operator (p.toTrajectory.domainError s u t)+s.extension g μ t •
      (p.toTrajectory.domainError s u t : Lp ℝ 2 ν))) *
    bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map
      (p.toTrajectory.domainError s u t : Lp ℝ 2 ν)) at henergy
  rw [bochnerL2Norm_congr_ae hresw,bochnerL2Norm_congr_ae hvalw,
    p.weighted_error_bochnerNorm ρ w τ h.aestronglyMeasurable] at henergy
  have hnorm := bochnerL2Norm_sub
    (ρ.memLp_map w τ h.aestronglyMeasurable (s.memLp_extension g (s.difference g U)))
    ((ρ.memLp_map w τ h.aestronglyMeasurable p.toTrajectory.derivative_L2).const_smul s.sign)
  rw [bochnerL2Norm_const_smul] at hnorm
  have hs : |s.sign| = 1 := by cases s <;> norm_num [Orientation.sign]
  rw [hs,one_mul,ρ.timeMap_extension_bochnerNorm g w τ h.aestronglyMeasurable,
    p.weighted_derivative_bochnerNorm ρ w τ h.aestronglyMeasurable] at hnorm
  have hN : c*N^2 ≤ 466560*g.dt*F^2 := by
    have hf0 : 0 ≤ F := g.l2Norm_nonneg _
    have hprod := mul_le_mul (hnorm.trans (add_le_add hDt hCt)) herr
      (norm_nonneg (M (g.pathL2 p.val.1-s.extensionLp g U))) (by positivity)
    calc
      c*N^2 ≤ _ := henergy
      _ ≤ (36*F+180*F)*(2160*g.dt*F) := hprod
      _ = 466560*g.dt*F^2 := by ring
  change N ≤ Real.sqrt (466560/c)*Real.sqrt g.dt*F
  apply (sq_le_sq₀ (WeakSobolevJet.spacetimeWeightedNorm_nonneg _ _ _ _)
    (by dsimp [F]; positivity [g.dt_pos,g.l2Norm_nonneg (ρ.nodeMap g w τ f)])).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt g.dt_pos.le]
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    c*N^2 ≤ 466560*g.dt*F^2 := hN
    _ = c*((466560/c)*g.dt*F^2) := by field_simp
end Carleman.CoerciveForm
