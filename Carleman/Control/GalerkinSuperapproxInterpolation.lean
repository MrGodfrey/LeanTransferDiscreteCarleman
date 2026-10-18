module

public import Carleman.Control.ConformingProjectionError
public import Carleman.Control.GalerkinTestData

/-! The original projected weighted test's spatial error follows from the
interpolation error of σ²z, weighted projection stability and an inverse bound. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  (X : Submodule ℝ (Lp ℝ 2 ν)) [CompleteSpace X] (hX : X ≤ V)
  (g : TimeGrid) (ρ : SpatialProfile ν) (w : TimeWeight) (τ : ℝ)

/-- The interpolated vector is the actual double weighted state in V. -/
structure GalerkinSuperapproxInterpolation (I : V → X) (ζ : ℝ → BoundedMultiplier ν)
    (CI Cp CE Cζ mesh : ℝ) : Prop where
  projection : ∀ t ∈ Icc 0 g.period, ∀ u : Lp ℝ 2 ν,
    (ζ t).seminorm (X.orthogonalProjectionOnto u : Lp ℝ 2 ν) ≤ Cp*(ζ t).seminorm u
  inverse : ∀ t ∈ Icc 0 g.period, ∀ x : X,
    conformingWeightedNorm hS hν hV (w.q t) (ρ.neg.multiplier w (-τ) t) (X.inclusion hX x) ≤
      CI*(ζ t).seminorm (x : Lp ℝ 2 ν)
  energy : ∀ t ∈ Icc 0 g.period,
    ∀ hw : ∀ v : V, (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V, ∀ z : X,
    let v := conformingWeight (ρ.multiplier w τ t) hw
      (conformingWeight (ρ.multiplier w τ t) hw (X.inclusion hX z))
    conformingWeightedNorm hS hν hV (w.q t) (ρ.neg.multiplier w (-τ) t)
      (v-X.inclusion hX (I v)) ≤
      CE*mesh*w.max*conformingWeightedNorm hS hν hV (w.q t)
        (ρ.multiplier w τ t) (X.inclusion hX z)
  auxiliary : ∀ t ∈ Icc 0 g.period,
    ∀ hw : ∀ v : V, (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V, ∀ z : X,
    let v := conformingWeight (ρ.multiplier w τ t) hw
      (conformingWeight (ρ.multiplier w τ t) hw (X.inclusion hX z))
    (ζ t).seminorm ((v : Lp ℝ 2 ν)-(I v : Lp ℝ 2 ν)) ≤
      Cζ*mesh*w.max*conformingWeightedNorm hS hν hV (w.q t)
        (ρ.multiplier w τ t) (X.inclusion hX z)

theorem galerkinSuperapprox_of_interpolation
    (I : V → X) (ζ : ℝ → BoundedMultiplier ν)
    (CI Cp CE Cζ mesh : ℝ) (hCI : 0 ≤ CI) (hCp : 0 ≤ Cp)
    (H : GalerkinSuperapproxInterpolation hS hν hV X hX g ρ w τ I ζ CI Cp CE Cζ mesh) :
    GalerkinSuperapprox hS hν hV X hX g ρ w τ (CE+CI*Cp*Cζ) mesh := by
  intro t ht hw z
  let σ := ρ.multiplier w τ t
  let v := conformingWeight σ hw (conformingWeight σ hw (X.inclusion hX z))
  let p := conformingWeightedSeminorm hS hν hV (w.q t) (ρ.neg.multiplier w (-τ) t)
  have hp : conformingProjector V X hX v = X.inclusion hX (galerkinWeightedTest X ρ w τ t z) := by
    apply Subtype.ext
    change (X.orthogonalProjectionOnto (σ.map (σ.map (z : Lp ℝ 2 ν))) : Lp ℝ 2 ν) = _
    rw [galerkinWeightedTest_apply]
    rfl
  have hh := conformingProjector_energy_error V X hX p (ζ t) CI Cp hCI
    (H.projection t ht)
    (by simpa only [p,conformingWeightedSeminorm_apply hS hν hV (w.nonneg t)] using H.inverse t ht)
    v (I v)
  have he := H.energy t ht hw z
  have hz := mul_le_mul_of_nonneg_left (H.auxiliary t ht hw z) (mul_nonneg hCI hCp)
  have hbound : p (v-conformingProjector V X hX v) ≤
      ((CE+CI*Cp*Cζ)*mesh*w.max)*conformingWeightedNorm hS hν hV (w.q t)
        (ρ.multiplier w τ t) (X.inclusion hX z) := by
    apply hh.trans
    simpa only [p,v,σ,Submodule.coe_sub,Submodule.coe_inclusion,conformingWeightedSeminorm_apply hS hν hV (w.nonneg t)] using
      (add_le_add he hz).trans_eq (by ring)
  rw [hp,← map_sub_rev p] at hbound
  simpa only [p,conformingWeightedSeminorm_apply hS hν hV (w.nonneg t)] using hbound

end Carleman.Physical
