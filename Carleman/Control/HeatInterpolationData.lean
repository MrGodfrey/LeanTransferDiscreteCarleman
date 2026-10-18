module

public import Carleman.Control.ConformingHeatGradient
public import Carleman.Control.GalerkinSuperapproxInterpolation

/-! Reduction of the heat N3 and N4 spatial estimates to the original
weighted gradient interpolation, projection and inverse estimates. The
auxiliary weights are explicit; their concrete mesh construction remains open. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V D : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d 1 ν S)
  (hD : D ≤ sobolevSubspace d 2 ν S) (hDV : D ≤ V)
  (X : Submodule ℝ (Lp ℝ 2 ν)) [CompleteSpace X] (hX : X ≤ V)
  (g : TimeGrid) (ρ : SpatialProfile ν) (w : TimeWeight) (τ : ℝ)

/-- Original Step 2 input estimates, with actual weak gradients. -/
structure HeatInterpolationData (I : D → X) (ζ : ℝ → BoundedMultiplier ν)
    (CI Cp CE C0 mesh : ℝ) : Prop where
  projection : ∀ t ∈ Icc 0 g.period, ∀ u : Lp ℝ 2 ν,
    (ρ.multiplier w τ t).seminorm (X.orthogonalProjectionOnto u : Lp ℝ 2 ν) ≤
      Cp*(ρ.multiplier w τ t).seminorm u
  auxiliary_projection : ∀ t ∈ Icc 0 g.period, ∀ u : Lp ℝ 2 ν,
    (ζ t).seminorm (X.orthogonalProjectionOnto u : Lp ℝ 2 ν) ≤ Cp*(ζ t).seminorm u
  domination : ∀ t ∈ Icc 0 g.period,
    ∀ᵐ x ∂ν, w.q t*|(ρ.multiplier w τ t).value x| ≤ |(ζ t).value x|
  inverse : ∀ t ∈ Icc 0 g.period, ∀ x : X,
    conformingHeatGradient hS hν hV (ρ.multiplier w τ t) (X.inclusion hX x) ≤
      CI*(ζ t).seminorm (x : Lp ℝ 2 ν)
  gradient_interpolation : ∀ t ∈ Icc 0 g.period, ∀ v : D,
    conformingHeatGradient hS hν hV (ρ.multiplier w τ t)
      (Submodule.inclusion hDV v-X.inclusion hX (I v)) +
      (ζ t).seminorm ((v : Lp ℝ 2 ν)-(I v : Lp ℝ 2 ν)) ≤
      CE*mesh*conformingParameterNorm hS hν hD (w.q t) (ρ.multiplier w τ t) v
  l2 : ∀ t ∈ Icc 0 g.period, ∀ v : D,
    (ρ.multiplier w τ t).seminorm ((v : Lp ℝ 2 ν)-(I v : Lp ℝ 2 ν)) ≤
      C0*mesh^2*conformingParameterNorm hS hν hD (w.q t) (ρ.multiplier w τ t) v

theorem HeatInterpolationData.toBounds
    {I : D → X} {ζ : ℝ → BoundedMultiplier ν} {CI Cp CE C0 mesh : ℝ}
    (H : HeatInterpolationData hS hν hV hD hDV X hX g ρ w τ I ζ CI Cp CE C0 mesh) :
    ConformingInterpolationBounds hS hν hV hD hDV X hX g ρ w τ I ζ
      (1+CI) Cp CE C0 CE mesh where
  projection := H.projection
  auxiliary_projection := H.auxiliary_projection
  inverse t ht x := conformingHeatInverse_of_gradient hS hν hV (w.pos t)
    _ _ (H.domination t ht) CI _ (H.inverse t ht x)
  energy t ht v := (conformingHeatNorm_le_auxiliary hS hν hV (w.pos t)
    _ _ (H.domination t ht) _).trans (H.gradient_interpolation t ht v)
  l2 := H.l2
  auxiliary t ht v := by
    have hn := conformingHeatGradient_nonneg hS hν hV (ρ.multiplier w τ t)
      (Submodule.inclusion hDV v-X.inclusion hX (I v))
    linarith only [H.gradient_interpolation t ht v,hn]

theorem HeatInterpolationData.approximation
    {I : D → X} {ζ : ℝ → BoundedMultiplier ν} {CI Cp CE C0 mesh : ℝ}
    (H : HeatInterpolationData hS hν hV hD hDV X hX g ρ w τ I ζ CI Cp CE C0 mesh)
    (hCI : 0 ≤ CI) (hCp : 0 ≤ Cp) :
    Section4.WeightedApproximation hS hν hV hD hDV (conformingReconstruction V X hX)
      g ρ w τ ((CE+(1+CI)*Cp*CE)*mesh) ((1+Cp)*C0*mesh^2) :=
  conformingWeightedApproximation_of_interpolation hS hν hV hD hDV X hX g ρ w τ
    I ζ (1+CI) Cp CE C0 CE mesh (by linarith) hCp
    (H.toBounds hS hν hV hD hDV X hX g ρ w τ)

/-- Original Step 3 gradient interpolation budget for σ²z. -/
structure HeatSuperapproxData (I : V → X) (ζ : ℝ → BoundedMultiplier ν)
    (CI Cp CE mesh : ℝ) : Prop where
  projection : ∀ t ∈ Icc 0 g.period, ∀ u : Lp ℝ 2 ν,
    (ζ t).seminorm (X.orthogonalProjectionOnto u : Lp ℝ 2 ν) ≤ Cp*(ζ t).seminorm u
  domination : ∀ t ∈ Icc 0 g.period,
    ∀ᵐ x ∂ν, w.q t*|(ρ.neg.multiplier w (-τ) t).value x| ≤ |(ζ t).value x|
  inverse : ∀ t ∈ Icc 0 g.period, ∀ x : X,
    conformingHeatGradient hS hν hV (ρ.neg.multiplier w (-τ) t) (X.inclusion hX x) ≤
      CI*(ζ t).seminorm (x : Lp ℝ 2 ν)
  gradient_interpolation : ∀ t ∈ Icc 0 g.period,
    ∀ hw : ∀ v : V, (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V, ∀ z : X,
    let v := conformingWeight (ρ.multiplier w τ t) hw
      (conformingWeight (ρ.multiplier w τ t) hw (X.inclusion hX z))
    conformingHeatGradient hS hν hV (ρ.neg.multiplier w (-τ) t) (v-X.inclusion hX (I v)) +
      (ζ t).seminorm ((v : Lp ℝ 2 ν)-(I v : Lp ℝ 2 ν)) ≤
      CE*mesh*w.max*conformingWeightedNorm hS hν hV (w.q t)
        (ρ.multiplier w τ t) (X.inclusion hX z)

theorem HeatSuperapproxData.toBounds
    {I : V → X} {ζ : ℝ → BoundedMultiplier ν} {CI Cp CE mesh : ℝ}
    (H : HeatSuperapproxData hS hν hV X hX g ρ w τ I ζ CI Cp CE mesh) :
    GalerkinSuperapproxInterpolation hS hν hV X hX g ρ w τ I ζ (1+CI) Cp CE CE mesh where
  projection := H.projection
  inverse t ht x := conformingHeatInverse_of_gradient hS hν hV (w.pos t)
    _ _ (H.domination t ht) CI _ (H.inverse t ht x)
  energy t ht hw z := (conformingHeatNorm_le_auxiliary hS hν hV (w.pos t)
    _ _ (H.domination t ht) _).trans (H.gradient_interpolation t ht hw z)
  auxiliary t ht hw z := by
    have hn := conformingHeatGradient_nonneg hS hν hV (ρ.neg.multiplier w (-τ) t)
      (conformingWeight (ρ.multiplier w τ t) hw
        (conformingWeight (ρ.multiplier w τ t) hw (X.inclusion hX z)) - X.inclusion hX
          (I (conformingWeight (ρ.multiplier w τ t) hw
            (conformingWeight (ρ.multiplier w τ t) hw (X.inclusion hX z)))))
    linarith only [H.gradient_interpolation t ht hw z,hn]

theorem HeatSuperapproxData.superapprox
    {I : V → X} {ζ : ℝ → BoundedMultiplier ν} {CI Cp CE mesh : ℝ}
    (H : HeatSuperapproxData hS hν hV X hX g ρ w τ I ζ CI Cp CE mesh)
    (hCI : 0 ≤ CI) (hCp : 0 ≤ Cp) :
    GalerkinSuperapprox hS hν hV X hX g ρ w τ (CE+(1+CI)*Cp*CE) mesh :=
  galerkinSuperapprox_of_interpolation hS hν hV X hX g ρ w τ I ζ (1+CI) Cp CE CE mesh
    (by linarith) hCp (H.toBounds hS hν hV X hX g ρ w τ)

end Carleman.Physical
