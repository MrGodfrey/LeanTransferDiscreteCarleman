module

public import Carleman.Section3.Statements

/-! Replace residuals by the actual loads, and use the independently proved
uniqueness to cover every original solution. All constants precede T and grids. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman.Section3
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (hΩ : IsBoundedLipschitzDomain S F)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  (b : CoerciveForm (Lp ℝ 2 (volume.restrict S)) W)
  {V : Submodule ℝ (Lp ℝ 2 (volume.restrict S))}
  (hV : V ≤ sobolevSubspace d m (volume.restrict S) S)
  (hDV : b.domain ≤ V) (hD : b.domain ≤ sobolevSubspace d (2*m) (volume.restrict S) S)
  (a : V → V → ℝ)
  (htest : ∀ u : b.domain, ∀ v : V, a (b.domain.inclusion hDV u) v = inner ℝ (b.operator u) (v : Lp ℝ 2 (volume.restrict S)))
  (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S)
  (hm : 0 < m) (Creg c C Ccomm β τStar : ℝ)
  (hc : 0 < c) (hCcomm : 0 ≤ Ccomm) (hβ : 0 < β) (hτStar : 0 ≤ τStar)
  (hell : ∀ v : b.domain, ‖domainSobolevJet hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hD v‖ ≤ Creg*‖b.operator v‖)

include hρ hm hCcomm hβ hτStar hell in
theorem euler_solved_uniform :
    ∃ L₀ δ K : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ 0 < K ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        AllowedWeightData hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hV hD a b.operator ρ w τ c C Ccomm →
        EulerEstimate hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) b hD g s w ρ L τ K := by
  obtain ⟨L₀,δ,K,hL,hδ,hK,hbound⟩ := b.lipschitz_weighted_euler_sobolev_uniform hΩ hV hD a ρ hρ
    hm Creg c C Ccomm β τStar hCcomm hβ hτStar hell
  refine ⟨L₀,δ,K,hL,hδ,hK,?_⟩
  intro g s w h L τ hLL hmesh hτ hd f
  have hμ : ∀ i, 0 ≤ (L*w.nodes g i)^(2*m) := fun _ => (even_two_mul m).pow_nonneg _
  obtain ⟨u,hu,hunique⟩ := b.existsUnique_periodicEuler g s _ hμ f
  refine ⟨⟨u,funext hu,fun v hv => hunique v (congrFun hv)⟩,?_⟩
  intro v hv
  have he := hbound g s w h L τ hLL hmesh hτ hd v
  rw [hv] at he
  exact he

include hρ hm hCcomm hβ hτStar hell in
theorem shift_solved_uniform :
    ∃ L₀ K : ℝ, 1 ≤ L₀ ∧ 0 < K ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
        (L τ : ℝ) (hLpos : 0 < L), L₀ ≤ L → |τ| ≤ τStar →
        AllowedWeightData hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hV hD a b.operator ρ w τ c C Ccomm →
        ContinuousEstimate hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) b hD g s w ρ τ K
          h.aestronglyMeasurable (h.shiftMultiplier m L hLpos) := by
  obtain ⟨L₀,K,hL,hK,hbound⟩ := b.lipschitz_weighted_shift_sobolev_uniform hΩ hD ρ hρ
    hm Creg Ccomm β τStar hCcomm hβ hτStar hell
  refine ⟨L₀,K,hL,hK,?_⟩
  intro g s w h L τ hLpos hLL hτ hd f
  refine ⟨b.existsUnique_variable_periodic g s _
    (Filter.Eventually.of_forall (h.shiftMultiplier_nonneg m L hLpos)) f,?_⟩
  intro p hp
  have he := hbound g s w h L τ hLpos hLL hτ hd.domain_preserving hd.inverse_preserving hd.commutator p
  dsimp only at he
  rw [hp] at he
  exact he

include hρ hm hCcomm hβ hτStar hell in
theorem frozen_solved_uniform :
    ∃ L₀ δ K : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ 0 < K ∧
      ∀ (g : TimeGrid) (s extension : Orientation) (w : TimeWeight) (h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        AllowedWeightData hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hV hD a b.operator ρ w τ c C Ccomm →
        ContinuousEstimate hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) b hD g s w ρ τ K
          h.aestronglyMeasurable (extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))) := by
  obtain ⟨L₀,δ,K,hL,hδ,hK,hbound⟩ := b.lipschitz_weighted_frozen_sobolev_uniform hΩ hD ρ hρ
    hm Creg Ccomm β τStar hCcomm hβ hτStar hell
  refine ⟨L₀,δ,K,hL,hδ,hK,?_⟩
  intro g s extension w h L τ hLL hmesh hτ hd f
  have hn : ∀ᵐ t ∂g.timeMeasure, 0 ≤ (extension.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).value t :=
    Filter.Eventually.of_forall fun t => by
      change 0 ≤ extension.extension g (fun i => (L*w.nodes g i)^(2*m)) t
      cases extension <;> exact (even_two_mul m).pow_nonneg _
  refine ⟨b.existsUnique_variable_periodic g s _ hn f,?_⟩
  intro p hp
  have he := hbound g s extension w h L τ hLL hmesh hτ hd.domain_preserving hd.inverse_preserving hd.commutator p
  dsimp only at he
  rw [hp] at he
  exact he

include hρ htest hm hc hCcomm hβ hτStar hell in
set_option maxHeartbeats 1600000 in
theorem temporal_arbitrary_uniform :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧
      ∀ (g : TimeGrid) (s : Orientation) (w : TimeWeight) (_h : TimeWeightRegularity w g β)
        (L τ : ℝ), L₀ ≤ L → g.dt*w.max^2 ≤ δ → |τ| ≤ τStar →
        AllowedWeightData hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hV hD a b.operator ρ w τ c C Ccomm →
        AllowedWeightData hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) hV hD a b.operator ρ.neg w (-τ) c C Ccomm →
        TemporalEstimate hΩ.isOpen (ae_restrict_mem hΩ.isOpen.measurableSet) b hV hDV g s w ρ L τ
          (max 2160 (Real.sqrt (466560/c))) := by
  obtain ⟨L₀,δ,hL,hδ,hbound⟩ := b.lipschitz_weighted_temporal_error_uniform hΩ hV hDV hD a htest ρ hρ
    hm Creg c C Ccomm β τStar hc hCcomm hβ hτStar hell
  refine ⟨L₀,δ,hL,hδ,?_⟩
  intro g s w h L τ hLL hmesh hτ hd hi f u p hu hp
  let μ := fun i => (L*w.nodes g i)^(2*m)
  have hμ : ∀ i, 0 ≤ μ i := fun _ => (even_two_mul m).pow_nonneg _
  have hue : u = b.eulerSolution g s μ hμ f := b.eulerSolution_unique g s μ hμ f u (congrFun hu)
  obtain ⟨q,hq,h1,h2,h3⟩ := hbound g s w h L τ hLL hmesh hτ hd hi f
  have hn : ∀ᵐ t ∂g.timeMeasure, 0 ≤ (s.frozenMultiplier g μ).value t :=
    Filter.Eventually.of_forall fun t => by
      change 0 ≤ s.extension g μ t
      cases s <;> exact hμ _
  have hpq : p = q := b.evolution_injective g s _ hn (hp.trans hq.symm)
  rw [hpq,hue]
  refine ⟨h1.trans ?_,h2,h3.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) g.dt_pos.le) (g.l2Norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)) (g.l2Norm_nonneg _)
end Carleman.Section3
