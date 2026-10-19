module

public import Carleman.Spatial.CartesianNodalControl
public import Carleman.Spatial.Observation
public import Carleman.Spatial.HeatNormSquare

/-! Original eq:observationinterface for the actual nodal restriction and
the actual reconstructed state, uniformly for the full allowed weight family. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem cartesianKuhnReconstructionLp_observed_eq
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (ω₀ ω : Set (SpatialCoordinates d)) (hω₀ : MeasurableSet ω₀)
    (f : CartesianInteriorIndex N → ℝ)
    (he : EqOn (cartesianKuhnReconstruction o δ hδ N f)
      (cartesianKuhnReconstruction o δ hδ N (cartesianObservedState o δ N ω f)) ω₀) :
    (BoundedMultiplier.cutoff ω₀ hω₀).map (cartesianKuhnReconstructionLp o δ hδ N f)=
      (BoundedMultiplier.cutoff ω₀ hω₀).map
        (cartesianKuhnReconstructionLp o δ hδ N (cartesianObservedState o δ N ω f)) := by
  apply Lp.ext
  filter_upwards [(BoundedMultiplier.cutoff ω₀ hω₀).map_ae (cartesianKuhnReconstructionLp o δ hδ N f),
    (BoundedMultiplier.cutoff ω₀ hω₀).map_ae
      (cartesianKuhnReconstructionLp o δ hδ N (cartesianObservedState o δ N ω f)),
    cartesianKuhnReconstructionLp_ae o δ hδ N f,
    cartesianKuhnReconstructionLp_ae o δ hδ N (cartesianObservedState o δ N ω f)] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  by_cases hx : x ∈ ω₀
  · rw [he hx]
  · simp [BoundedMultiplier.cutoff,hx]

theorem allowed_weight_cartesian_observation
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (ρ : SpatialProfile (volume.restrict S)) (hρ : ContDiffOn ℝ 1 ρ.value (closure S))
    (ω₀ ω : Set (SpatialCoordinates d)) (hω₀ : MeasurableSet ω₀)
    (hcompact₀ : IsCompact (closure ω₀)) (hω : IsOpen ω) (hinc : closure ω₀ ⊆ ω) :
    ∃ h₀ > (0:ℝ), ∃ C > (0:ℝ),
    ∀ (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
      (hTS : openCoordinateBox o (fun j => o j+(N j:ℝ)*δ j) ⊆ S)
      (h : ℝ), 0 < h → h ≤ h₀ → (∀ j, δ j ≤ h) →
    ∀ (w : TimeWeight) (τ t η : ℝ), |η|=1 → h*w.q t ≤ 1 →
    ∀ f : CartesianInteriorIndex N → ℝ,
      let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
      σ.observation ω₀ hω₀ (cartesianKuhnReconstructionLp o δ hδ N f) ≤
        C*Real.sqrt (cartesianControlWeightedSq o δ N ω σ.value (cartesianControlRestriction o δ N ω f)) := by
  obtain ⟨h₀,hh₀,hlocal⟩ := cartesianKuhnReconstruction_observed_eq ω₀ ω hcompact₀ hω hinc
  obtain ⟨C,hC,hbound⟩ := allowed_weight_cartesianKuhn_stability hS hc hcompact ρ hρ
  refine ⟨h₀,hh₀,Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro o δ hδ N hTS h hh hmesh hstep w τ t η hη hsmall f
  let σ := (((ρ.scaled η).multiplier w τ t).onSubdomain hTS)
  let g := cartesianObservedState o δ N ω f
  have he := cartesianKuhnReconstructionLp_observed_eq o δ hδ N ω₀ ω hω₀ f
    (hlocal o δ hδ N h hh hmesh hstep f)
  have heq : σ.observation ω₀ hω₀ (cartesianKuhnReconstructionLp o δ hδ N f)=
      σ.observation ω₀ hω₀ (cartesianKuhnReconstructionLp o δ hδ N g) :=
    congrArg (σ.seminorm (E := ℝ)) he
  have hn := heq.le.trans (σ.observation_le ω₀ hω₀ (cartesianKuhnReconstructionLp o δ hδ N g))
  have hb := (hbound o δ hδ N hTS h hh hstep w τ t η hη hsmall g).2.1
  change (σ.seminorm (cartesianKuhnReconstructionLp o δ hδ N g))^2 ≤
    C*cartesianWeightedNodeEnergy o δ N σ.value g at hb
  have hE : 0 ≤ cartesianControlWeightedSq o δ N ω σ.value (cartesianControlRestriction o δ N ω f) := by
    rw [← cartesianObservedState_weighted_energy]
    exact cartesianWeightedNodeEnergy_nonneg o δ hδ N σ.value g
  rw [cartesianObservedState_weighted_energy] at hb
  apply hn.trans
  apply nonneg_le_sqrt_mul_of_sq_le (apply_nonneg _ _) hC.le (Real.sqrt_nonneg _)
  rwa [Real.sq_sqrt hE]

end Carleman
