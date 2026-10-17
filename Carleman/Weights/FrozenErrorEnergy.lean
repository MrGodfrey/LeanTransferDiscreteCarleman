module

public import Carleman.Weights.FrozenOperatorEnergy
public import Carleman.Continuous.FrozenErrorResidual
public import Carleman.Continuous.BochnerNormAlgebra
public import Carleman.Spatial.SobolevTruncation

/-! Weighted energy of the actual continuous-minus-Euler error. The right-hand
side retains the weighted time-derivative and error norms still needed for the
paper's weighted error rate; no estimate for them is assumed or claimed here. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S) (hDV : D ≤ V)
  (hD : D ≤ sobolevSubspace d (2*m) ν S)
  (a : V → V → ℝ) (A : D →ₗ[ℝ] Lp ℝ 2 ν)
  (htest : ∀ u : D, ∀ v : V, a (D.inclusion hDV u) v = inner ℝ (A u) (v : Lp ℝ 2 ν))
  (Creg : ℝ) (hell : ∀ v : D, ‖domainSobolevJet hS hν hD v‖ ≤ Creg*‖A v‖)

include hell in
theorem PeriodicWeakTrajectory.domainError_conforming_L2 {g : TimeGrid}
    (U : PeriodicWeakTrajectory g D A) (s : Orientation) (u : g.Sequence D) :
    MemLp (fun t => domainSobolevJet hS hν hV (D.inclusion hDV (U.domainError s u t)))
      2 g.timeMeasure := by
  have hlo := elliptic_bound_lower_order hS hν (show m ≤ 2*m by omega)
    (hDV.trans hV) hD A Creg hell
  have he : (fun t => domainSobolevJet hS hν hV (D.inclusion hDV (U.domainError s u t))) =
      (fun t => domainSobolevJet hS hν (hDV.trans hV) (U.domainError s u t)) := by
    funext t
    apply WeakSobolevJet.value_injective hS hν
    simp only [domainSobolevJet_value, Submodule.coe_inclusion]
  rw [he]
  exact memLp_domainSobolevJet_of_operator hS hν (hDV.trans hV) A Creg hlo
    (U.domainError_operator_L2 s u)

include htest hell
/-- Uniform in the period, grid, orientation, weight and load. The A1 elliptic
bound is used only in its original direction, to establish Sobolev finiteness. -/
theorem frozen_error_energy_uniform (hm : 0 < m) (C β : ℝ) (hβ : 0 < β) :
    ∃ L₀ δ : ℝ, 1 ≤ L₀ ∧ 0 < δ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∀ (g : TimeGrid) (s : Orientation) (ρ : SpatialProfile ν) (w : TimeWeight) (τ c : ℝ),
      TimeWeightRegularity w g β → g.dt*w.max^2 ≤ δ →
      ∀ hw : ∀ t (v : V), (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V,
      (∀ t (v : V), c*(conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v)^2 -
        C*(w.q t^m*(ρ.multiplier w τ t).seminorm (v : Lp ℝ 2 ν))^2 ≤
          a v (conformingWeight (ρ.multiplier w τ t) (hw t)
            (conformingWeight (ρ.multiplier w τ t) (hw t) v))) →
      ∀ (f : g.Sequence (Lp ℝ 2 ν))
        (p : FrozenEulerPair g s (fun i => (L*w.nodes g i)^(2*m)) A f),
      c*(WeakSobolevJet.spacetimeWeightedNorm g w.q (ρ.multiplier w τ)
        (fun t => domainSobolevJet hS hν hV
          (D.inclusion hDV (p.trajectory.domainError s p.nodes t))))^2 ≤
        (bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map
          (s.extension g (s.difference g (fun i => (p.nodes i : Lp ℝ 2 ν))) t)) +
         bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map (p.trajectory.derivative t)))*
        bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map
          (p.trajectory.value t - s.extension g (fun i => (p.nodes i : Lp ℝ 2 ν)) t)) := by
  obtain ⟨L₀, δ, hL₀, hδ, henergy⟩ :=
    frozen_spacetime_operator_energy_uniform hS hν hV hDV a A htest hm C β hβ
  refine ⟨L₀, δ, hL₀, hδ, ?_⟩
  intro L hL g s ρ w τ c h hmesh hw ha f p
  let σ := ρ.multiplier w τ
  let e := p.trajectory.domainError s p.nodes
  have he := henergy L hL g s ρ w τ c h hmesh hw ha e
    (p.trajectory.domainError_conforming_L2 hS hν hV hDV hD A Creg hell s p.nodes)
    (p.trajectory.domainError_operator_L2 s p.nodes)
  have hres := p.trajectory.domainError_residual_ae s p.nodes _ f
    p.continuous_equation p.discrete_equation
  have hresw : (fun t => (σ t).map (A (e t) + s.extension g
        (fun i => (L*w.nodes g i)^(2*m)) t • (e t : Lp ℝ 2 ν))) =ᵐ[g.timeMeasure]
      (fun t => (σ t).map (s.extension g (s.difference g
        (fun i => (p.nodes i : Lp ℝ 2 ν))) t) - s.sign • (σ t).map (p.trajectory.derivative t)) := by
    filter_upwards [hres] with t ht
    rw [ht]
    change (σ t).linearMap (_ - _ • _) = _
    rw [map_sub, map_smul]
    rfl
  have hval := p.trajectory.domainError_value_ae s p.nodes
  have hvalw : (fun t => (σ t).map (e t : Lp ℝ 2 ν)) =ᵐ[g.timeMeasure]
      (fun t => (σ t).map (p.trajectory.value t -
        s.extension g (fun i => (p.nodes i : Lp ℝ 2 ν)) t)) := by
    filter_upwards [hval] with t ht
    rw [ht]
  change c*(WeakSobolevJet.spacetimeWeightedNorm g w.q σ
    (fun t => domainSobolevJet hS hν hV (D.inclusion hDV (e t))))^2 ≤ _ at he
  change c*(WeakSobolevJet.spacetimeWeightedNorm g w.q σ
    (fun t => domainSobolevJet hS hν hV (D.inclusion hDV (e t))))^2 ≤
      bochnerL2Norm g.timeMeasure (fun t => (σ t).map (A (e t) + s.extension g
        (fun i => (L*w.nodes g i)^(2*m)) t • (e t : Lp ℝ 2 ν)))*
      bochnerL2Norm g.timeMeasure (fun t => (σ t).map (e t : Lp ℝ 2 ν)) at he
  rw [bochnerL2Norm_congr_ae hresw, bochnerL2Norm_congr_ae hvalw] at he
  have h₁ := ρ.memLp_map w τ h.aestronglyMeasurable
    (s.memLp_extension g (s.difference g (fun i => (p.nodes i : Lp ℝ 2 ν))))
  have h₂ := ρ.memLp_map w τ h.aestronglyMeasurable p.trajectory.derivative_L2
  have hsum := bochnerL2Norm_sub h₁ (h₂.const_smul s.sign)
  rw [bochnerL2Norm_const_smul] at hsum
  have hs : |s.sign| = 1 := by cases s <;> norm_num [Orientation.sign]
  rw [hs, one_mul] at hsum
  exact he.trans (mul_le_mul_of_nonneg_right hsum (bochnerL2Norm_nonneg _))

end Carleman
