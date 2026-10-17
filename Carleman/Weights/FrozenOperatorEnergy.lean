module

public import Carleman.Spatial.LowerShiftEnergy
public import Carleman.Weights.FrozenShiftLower
public import Carleman.Continuous.SobolevError

/-! A3 for the actual frozen shift, in either orientation. All weighted
integrability is derived from the original graph regularity, and the threshold
is chosen before T, the mesh, the weight family and the state. -/
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
theorem frozen_spacetime_operator_energy_uniform (hm : 0 < m) (C β : ℝ) (hβ : 0 < β) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∀ (g : TimeGrid) (s : Orientation) (ρ : SpatialProfile ν) (w : TimeWeight) (τ c : ℝ),
      TimeWeightRegularity w g β → g.dt*w.max^2 ≤ δ →
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
          (A (u t) + (s.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).value t • (u t : Lp ℝ 2 ν)))*
        bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map (u t : Lp ℝ 2 ν)) := by
  obtain ⟨L₀, δ, hL₀, hδ, hlower⟩ := frozen_shift_margin_uniform m hm β hβ C
  refine ⟨L₀, δ, hL₀, hδ, ?_⟩
  intro L hL g s ρ w τ c h hmesh hw ha u hJ hA
  have hu : MemLp (fun t => (u t : Lp ℝ 2 ν)) 2 g.timeMeasure := by
    simpa only [WeakSobolevJet.valueCLM_apply, domainSobolevJet_value, Submodule.coe_inclusion] using
      hJ.continuousLinearMap_comp WeakSobolevJet.valueCLM
  have hμu := s.memLp_smul_extension g (fun i => (L*w.nodes g i)^(2*m)) hu
  apply shiftedOperator_spacetime_energy_of_lower hS hν hV hDV a A htest g w
    (ρ.multiplier w τ) (s.frozenMultiplier g (fun i => (L*w.nodes g i)^(2*m))).value
    hm (hlower g s w h L hL hmesh) hw ha u
  · intro k
    simpa only [one_mul] using WeakSobolevJet.memLp_parameterTimeField g w ρ τ 1
      h.aestronglyMeasurable hJ k
  · exact ρ.memLp_map w τ h.aestronglyMeasurable hu
  · exact ρ.memLp_map w τ h.aestronglyMeasurable (hA.add hμu)

end Carleman
