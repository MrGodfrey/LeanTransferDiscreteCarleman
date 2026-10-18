module

public import Carleman.Control.ConformingProjectionError
public import Carleman.Section4.ApproximationData

/-! The original N3 bounds follow from actual interpolation errors, weighted
L² projection stability, and a weighted inverse estimate. The local estimates
are explicit inputs; no concrete mesh is asserted here. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (hD : D ≤ sobolevSubspace d (2*m) ν S) (hDV : D ≤ V)
  (X : Submodule ℝ (Lp ℝ 2 ν)) [CompleteSpace X] (hX : X ≤ V)
  (g : TimeGrid) (ρ : SpatialProfile ν) (w : TimeWeight) (τ : ℝ)

/-- The interpolant can be the actual nodal interpolant; linearity is not
needed for this projection-error step. ζ is the auxiliary mesh-weight. -/
structure ConformingInterpolationBounds (I : D → X) (ζ : ℝ → BoundedMultiplier ν)
    (CI Cp CE C0 Cζ mesh : ℝ) : Prop where
  projection : ∀ t ∈ Icc 0 g.period, ∀ u : Lp ℝ 2 ν,
    (ρ.multiplier w τ t).seminorm (X.orthogonalProjectionOnto u : Lp ℝ 2 ν) ≤
      Cp*(ρ.multiplier w τ t).seminorm u
  auxiliary_projection : ∀ t ∈ Icc 0 g.period, ∀ u : Lp ℝ 2 ν,
    (ζ t).seminorm (X.orthogonalProjectionOnto u : Lp ℝ 2 ν) ≤ Cp*(ζ t).seminorm u
  inverse : ∀ t ∈ Icc 0 g.period, ∀ x : X,
    conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) (X.inclusion hX x) ≤
      CI*(ζ t).seminorm (x : Lp ℝ 2 ν)
  energy : ∀ t ∈ Icc 0 g.period, ∀ v : D,
    conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t)
      (Submodule.inclusion hDV v-X.inclusion hX (I v)) ≤
      CE*mesh*conformingParameterNorm hS hν hD (w.q t) (ρ.multiplier w τ t) v
  l2 : ∀ t ∈ Icc 0 g.period, ∀ v : D,
    (ρ.multiplier w τ t).seminorm ((v : Lp ℝ 2 ν)-(I v : Lp ℝ 2 ν)) ≤
      C0*mesh^2*conformingParameterNorm hS hν hD (w.q t) (ρ.multiplier w τ t) v
  auxiliary : ∀ t ∈ Icc 0 g.period, ∀ v : D,
    (ζ t).seminorm ((v : Lp ℝ 2 ν)-(I v : Lp ℝ 2 ν)) ≤
      Cζ*mesh*conformingParameterNorm hS hν hD (w.q t) (ρ.multiplier w τ t) v

/-- Both orders and their mesh-independent constants are derived, not fields. -/
theorem conformingWeightedApproximation_of_interpolation
    (I : D → X) (ζ : ℝ → BoundedMultiplier ν)
    (CI Cp CE C0 Cζ mesh : ℝ) (hCI : 0 ≤ CI) (hCp : 0 ≤ Cp)
    (H : ConformingInterpolationBounds hS hν hV hD hDV X hX g ρ w τ I ζ CI Cp CE C0 Cζ mesh) :
    Section4.WeightedApproximation hS hν hV hD hDV (conformingReconstruction V X hX)
      g ρ w τ ((CE+CI*Cp*Cζ)*mesh) ((1+Cp)*C0*mesh^2) where
  energy t ht v := by
    have hh := conformingProjector_energy_error V X hX
      (conformingWeightedSeminorm hS hν hV (w.q t) (ρ.multiplier w τ t))
      (ζ t) CI Cp hCI (H.auxiliary_projection t ht)
      (by simpa only [conformingWeightedSeminorm_apply hS hν hV (w.nonneg t)] using H.inverse t ht)
      (Submodule.inclusion hDV v) (I v)
    simp only [conformingWeightedSeminorm_apply hS hν hV (w.nonneg t)] at hh
    apply hh.trans
    have he := H.energy t ht v
    have hz := mul_le_mul_of_nonneg_left (H.auxiliary t ht v) (mul_nonneg hCI hCp)
    exact (add_le_add he hz).trans_eq (by ring)
  l2 t ht v := by
    have hh := conformingProjector_l2_error V X hX (ρ.multiplier w τ t) Cp
      (H.projection t ht) (Submodule.inclusion hDV v) (I v)
    apply hh.trans
    exact (mul_le_mul_of_nonneg_left (H.l2 t ht v) (by linarith : 0 ≤ 1+Cp)).trans_eq (by ring)

end Carleman.Physical
