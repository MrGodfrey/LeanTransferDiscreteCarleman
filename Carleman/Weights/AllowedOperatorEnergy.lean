module

public import Carleman.Spatial.WeightedOperatorEnergy

/-! A3 gives the actual allowed-weight space-time N estimate on the original
operator graph. The shift threshold is uniform, and all weighted integrability
is derived from unweighted graph regularity. Either profile sign is permitted. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S) (hDV : D ≤ V)
  (a : V → V → ℝ) (A : D →ₗ[ℝ] Lp ℝ 2 ν)
  (htest : ∀ u : D, ∀ v : V, a (D.inclusion hDV u) v = inner ℝ (A u) (v : Lp ℝ 2 ν))

include htest
theorem allowed_spacetime_operator_energy_uniform (hm : 0 < m) (C : ℝ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∀ (g : TimeGrid) (ρ : SpatialProfile ν) (w : TimeWeight) (τ c : ℝ),
      AEStronglyMeasurable w.q g.timeMeasure →
      ∀ hw : ∀ t (v : V), (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V,
      (∀ t (v : V), c*(conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v)^2 -
        C*(w.q t^m*(ρ.multiplier w τ t).seminorm (v : Lp ℝ 2 ν))^2 ≤
          a v (conformingWeight (ρ.multiplier w τ t) (hw t)
            (conformingWeight (ρ.multiplier w τ t) (hw t) v))) →
      ∀ u : ℝ → D,
      MemLp (fun t => domainSobolevJet hS hν hV (D.inclusion hDV (u t))) 2 g.timeMeasure →
      MemLp (fun t => A (u t)) 2 g.timeMeasure →
      c*(WeakSobolevJet.spacetimeWeightedNorm g w.q (ρ.multiplier w τ)
        (fun t => domainSobolevJet hS hν hV (D.inclusion hDV (u t))))^2 ≤
        bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map
          (A (u t) + (L*w.q t)^(2*m) • (u t : Lp ℝ 2 ν)))*
        bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map (u t : Lp ℝ 2 ν)) := by
  obtain ⟨L₀, hL₀, hmargin⟩ := shiftedForm_margin_threshold m hm C 0
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL g ρ w τ c hq hw ha u hJ hA
  have hu : MemLp (fun t => (u t : Lp ℝ 2 ν)) 2 g.timeMeasure := by
    simpa only [WeakSobolevJet.valueCLM_apply, domainSobolevJet_value, Submodule.coe_inclusion] using
      hJ.continuousLinearMap_comp WeakSobolevJet.valueCLM
  have hμu : MemLp (fun t => (L*w.q t)^(2*m) • (u t : Lp ℝ 2 ν)) 2 g.timeMeasure := by
    apply hu.of_le_mul (c := (|L| * w.max)^(2*m))
      (((hq.const_mul L).pow _).smul hu.aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro t
    change ‖(L*w.q t)^(2*m) • (u t : Lp ℝ 2 ν)‖ ≤ (|L| * w.max)^(2*m)*‖(u t : Lp ℝ 2 ν)‖
    rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos (w.pos t)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity [w.pos t])
      (mul_le_mul_of_nonneg_left (w.upper t) (abs_nonneg L)) _) (norm_nonneg _)
  apply shiftedOperator_spacetime_energy hS hν hV hDV a A htest g w (ρ.multiplier w τ)
    hm (by simpa using hmargin L hL) hw ha u
  · intro k
    simpa only [one_mul] using WeakSobolevJet.memLp_parameterTimeField g w ρ τ 1 hq hJ k
  · exact ρ.memLp_map w τ hq hu
  · exact ρ.memLp_map w τ hq (hA.add hμu)

end Carleman
