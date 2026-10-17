module

public import Carleman.Spatial.ShiftedFormBounds
public import Carleman.Spatial.MultiplierAlgebra

/-! Original allowed weights and the uniform shifted form conclusions.
The shift threshold is chosen before every time weight and spatial state. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
namespace SpatialProfile
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem multiplier_inverse (ρ : SpatialProfile ν) (w : TimeWeight) (τ t : ℝ) (x : Ω) :
    (ρ.multiplier w τ t).value x*(ρ.neg.multiplier w (-τ) t).value x=1 := by
  rw [ρ.multiplier_neg_value]
  change (w.q t^τ*Real.exp (ρ.value x*w.q t)) *
    (w.q t^(-τ)*(Real.exp (ρ.value x*w.q t))⁻¹)=1
  rw [Real.rpow_neg (w.nonneg t)]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos (w.pos t) τ)]

theorem multiplier_inverse_map (ρ : SpatialProfile ν) (w : TimeWeight) (τ t : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : Lp E 2 ν) :
    (ρ.multiplier w τ t).map ((ρ.neg.multiplier w (-τ) t).map u)=u :=
  BoundedMultiplier.map_inverse _ _ (Filter.Eventually.of_forall (ρ.multiplier_inverse w τ t)) u
end SpatialProfile

variable {d m : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d m ν S)

/-- Full spatial form-bound conclusion for the original exponential weight and its inverse. -/
theorem allowed_shiftedForm_bound (a : V → V → ℝ) (ρ : SpatialProfile ν)
    (w : TimeWeight) (τ t : ℝ) {L C : ℝ} (hL : 0 ≤ L)
    (ha : ∀ v z, |a v z| ≤ C * conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v *
      conformingWeightedNorm hS hν hV (w.q t) (ρ.neg.multiplier w (-τ) t) z)
    (v z : V) : |shiftedForm a ((L*w.q t)^(2*m)) v z| ≤
      (C+L^(2*m))*conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v *
        conformingWeightedNorm hS hν hV (w.q t) (ρ.neg.multiplier w (-τ) t) z :=
  shiftedForm_bound hS hν hV a (w.nonneg t) hL _ _
    (Filter.Eventually.of_forall (ρ.multiplier_inverse w τ t)) ha v z

/-- Every prescribed positive margin is retained with L₀ independent of T,
qmax, tau, either profile sign, and the conforming state. A3 is the sole form premise. -/
theorem allowed_shiftedForm_coercive_uniform (hm : 0 < m) (C : ℝ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∀ (a : V → V → ℝ) (ρ : SpatialProfile ν) (w : TimeWeight) (τ t c : ℝ),
      ∀ hw : ∀ v : V, (ρ.multiplier w τ t).map (v : Lp ℝ 2 ν) ∈ V,
      (∀ v, c*(conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v)^2 -
        C*(w.q t^m*(ρ.multiplier w τ t).seminorm (v : Lp ℝ 2 ν))^2 ≤
          a v (conformingWeight (ρ.multiplier w τ t) hw
            (conformingWeight (ρ.multiplier w τ t) hw v))) →
      ∀ v : V, c*(conformingWeightedNorm hS hν hV (w.q t) (ρ.multiplier w τ t) v)^2 +
        B*(w.q t*(ρ.multiplier w τ t).seminorm (v : Lp ℝ 2 ν))^2 ≤
          shiftedForm a ((L*w.q t)^(2*m)) v (conformingWeight (ρ.multiplier w τ t) hw
            (conformingWeight (ρ.multiplier w τ t) hw v)) := by
  obtain ⟨L₀, hL₀, hmargin⟩ := shiftedForm_margin_threshold m hm C B
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL a ρ w τ t c hw ha v
  exact shiftedForm_coercive hS hν hV a hm (w.lower t) hB (hmargin L hL) _ hw ha v
end Carleman
