module

public import Carleman.Spatial.SubdomainContinuity
public import Carleman.Spatial.MultiplierAlgebra

/-! Restriction of the actual multiplier and comparison with a positive local
anchor, for arbitrary genuine scalar or vector L² fields. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.BoundedMultiplier
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def onSubdomain (hTS : T ⊆ S) (w : BoundedMultiplier (volume.restrict S)) :
    BoundedMultiplier (volume.restrict T) where
  value := w.value
  measurable := w.measurable.mono_measure (Measure.restrict_mono hTS le_rfl)
  bound := w.bound
  bound_nonneg := w.bound_nonneg
  bounded := w.bounded.filter_mono (ae_mono (Measure.restrict_mono hTS le_rfl))

theorem onSubdomain_map (hTS : T ⊆ S) (w : BoundedMultiplier (volume.restrict S))
    (u : Lp E 2 (volume.restrict S)) :
    (w.onSubdomain hTS).map (subdomainLp hTS u)=subdomainLp hTS (w.map u) := by
  apply Lp.ext
  filter_upwards [(w.onSubdomain hTS).map_ae (subdomainLp hTS u),subdomainLp_ae hTS u,
    subdomainLp_ae hTS (w.map u),
    (w.map_ae u).filter_mono (ae_mono (Measure.restrict_mono hTS le_rfl))] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  rfl

theorem onSubdomain_seminorm (hTS : T ⊆ S) (w : BoundedMultiplier (volume.restrict S))
    (u : Lp E 2 (volume.restrict S)) :
    (w.onSubdomain hTS).seminorm (subdomainLp hTS u)=‖subdomainLp hTS (w.map u)‖ := by
  rw [seminorm_apply,onSubdomain_map]

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem seminorm_le_anchor (w : BoundedMultiplier ν) (W s : ℝ)
    (hw : ∀ᵐ x ∂ν, |w.value x| ≤ W*s) (u : Lp E 2 ν) :
    w.seminorm u ≤ W*s*‖u‖ := by
  have h := w.seminorm_le_of_weight_le one (W*s) (by
    filter_upwards [hw] with x hx
    simpa only [one,abs_one,mul_one] using hx) u
  simpa only [one_seminorm] using h

theorem norm_le_seminorm_anchor (w : BoundedMultiplier ν) (W s : ℝ) (hs : 0 < s)
    (hw : ∀ᵐ x ∂ν, s ≤ W*|w.value x|) (u : Lp E 2 ν) :
    ‖u‖ ≤ (W/s)*w.seminorm u := by
  have h := one.seminorm_le_of_weight_le w (W/s) (by
    filter_upwards [hw] with x hx
    change |(1:ℝ)| ≤ W/s*|w.value x|
    rw [abs_one,div_mul_eq_mul_div]
    exact (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hx)) u
  simpa only [one_seminorm] using h

end Carleman.BoundedMultiplier
