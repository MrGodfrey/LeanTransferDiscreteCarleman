module

public import Carleman.Section4.SpatialEnergy

/-! N4's original test-operator data. There is no coercivity, stability,
Cea or error-estimate field. Those conclusions are proved from these data. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Section4
variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  (r : Reconstruction V X) (g : TimeGrid) (ρ : SpatialProfile ν) (w : TimeWeight)
  (τ Ctime Csuper mesh : ℝ)

/-- Original N4 consequences needed for the proof, on the closed period.
`mesh` is h; the superapproximation scale remains exactly Csuper*h*qmax. -/
structure WeightedTest where
  op : ℝ → X →ₗ[ℝ] X
  derivative : ℝ → X →ₗ[ℝ] X
  endpoint : op 0 = op g.period
  hasDeriv : ∀ z t, t ∈ Icc 0 g.period →
    HasDerivWithinAt (fun x => inner ℝ z (op x z)) (inner ℝ z (derivative t z)) (Icc 0 g.period) t
  symmetric : ∀ t ∈ Icc 0 g.period, ∀ v z, inner ℝ v (op t z) = inner ℝ z (op t v)
  nonneg : ∀ t ∈ Icc 0 g.period, ∀ z, 0 ≤ inner ℝ z (op t z)
  time_bound : ∀ z t, t ∈ Icc 0 g.period →
    |inner ℝ z (derivative t z)| ≤ Ctime*(w.q t*(ρ.multiplier w τ t).seminorm (r.RH z))^2
  superapprox : ∀ t ∈ Icc 0 g.period,
    ∀ hw : ∀ v : V, (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V, ∀ z,
    conformingWeightedNorm hS hν hV (w.q t) (ρ.neg.multiplier w (-τ) t)
      (r.R (op t z)-conformingWeight (ρ.multiplier w τ t) hw
        (conformingWeight (ρ.multiplier w τ t) hw (r.R z))) ≤
      (Csuper*mesh*w.max)*conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) (r.R z)

/-- Explicit original mesh/stiffness thresholds supply the Cea absorption
condition. They are chosen before h, qmax, grid, period, weight and states. -/
theorem spatial_smallness_thresholds {c Cf CM Csuper δnum : ℝ}
    (hc : 0 < c) (hCf : 0 ≤ Cf) (hCM : 0 ≤ CM) (hCs : 0 ≤ Csuper) (hδnum : 0 < δnum) :
    ∃ δx ηstar : ℝ, 0 < δx ∧ δx ≤ δnum ∧ 0 < ηstar ∧ ηstar ≤ 1 ∧
      ∀ hQ ηA : ℝ, 0 ≤ hQ → hQ ≤ δx → 0 ≤ ηA → ηA ≤ ηstar →
        Csuper*hQ ≤ 1 ∧ Cf*(Csuper*hQ)+ηA*(Csuper*hQ+CM) ≤ c/2 := by
  let εstar := min 1 (c/(4*(Cf+1)))
  let δx := min δnum (εstar/(Csuper+1))
  let ηstar := min 1 (c/(4*(1+CM)))
  have hε : 0 < εstar := lt_min zero_lt_one (div_pos hc (by positivity))
  have hx : 0 < δx := lt_min hδnum (div_pos hε (by positivity))
  have hη : 0 < ηstar := lt_min zero_lt_one (div_pos hc (by positivity))
  refine ⟨δx,ηstar,hx,min_le_left _ _,hη,min_le_left _ _,?_⟩
  intro hQ ηA hhQ hhδ hηA hηs
  have hεb : Csuper*hQ ≤ εstar := by
    have he : hQ*(Csuper+1) ≤ εstar :=
      (le_div_iff₀ (show 0 < Csuper+1 by positivity)).mp (hhδ.trans (min_le_right _ _))
    nlinarith only [he,hhQ]
  have he1 := hεb.trans (min_le_left _ _)
  have hec : Cf*(Csuper*hQ) ≤ c/4 := by
    have he : εstar*(4*(Cf+1)) ≤ c :=
      (le_div_iff₀ (show 0 < 4*(Cf+1) by positivity)).mp (min_le_right _ _)
    have hprod := mul_le_mul_of_nonneg_left hεb hCf
    nlinarith only [he,hprod,hε.le]
  have hηc : ηA*(Csuper*hQ+CM) ≤ c/4 := by
    have he : ηA*(4*(1+CM)) ≤ c :=
      (le_div_iff₀ (show 0 < 4*(1+CM) by positivity)).mp (hηs.trans (min_le_right _ _))
    have hp := mul_le_mul_of_nonneg_left he1 hηA
    nlinarith only [he,hp]
  exact ⟨he1,by linarith only [hec,hηc]⟩

end Carleman.Section4
