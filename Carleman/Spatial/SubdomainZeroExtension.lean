module

public import Carleman.Spatial.SubdomainContinuity

/-! Actual extension by zero between nested spatial L² spaces. It is an
isometry and is adjoint to restriction, including for vector fields. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def subdomainZeroExtend (S : Set (SpatialCoordinates d)) (hT : MeasurableSet T)
    (u : Lp E 2 (volume.restrict T)) : Lp E 2 (volume.restrict S) :=
  Physical.restrictRegionLp S (zeroExtendLp hT u)

omit [InnerProductSpace ℝ E] in
theorem subdomainZeroExtend_ae (hT : MeasurableSet T) (u : Lp E 2 (volume.restrict T)) :
    subdomainZeroExtend S hT u =ᵐ[volume.restrict S] T.indicator u :=
  (Physical.restrictRegionLp_ae S _).trans ((zeroExtendLp_ae hT u).filter_mono ae_restrict_le)

omit [InnerProductSpace ℝ E] in
theorem subdomainLp_zeroExtend (hT : MeasurableSet T) (hTS : T ⊆ S)
    (u : Lp E 2 (volume.restrict T)) :
    subdomainLp hTS (subdomainZeroExtend S hT u) = u := by
  apply Lp.ext
  filter_upwards [subdomainLp_ae hTS (subdomainZeroExtend S hT u),
    (Physical.restrictRegionLp_ae S (zeroExtendLp hT u)).filter_mono
      (ae_mono (Measure.restrict_mono hTS le_rfl)),zeroExtendLp_ae_restrict hT u] with x h1 h2 h3
  exact h1.trans (h2.trans h3)

omit [InnerProductSpace ℝ E] in
theorem subdomainZeroExtend_norm (hT : MeasurableSet T) (hTS : T ⊆ S)
    (u : Lp E 2 (volume.restrict T)) : ‖subdomainZeroExtend S hT u‖ = ‖u‖ := by
  apply le_antisymm
  · exact (Physical.restrictRegionLp_norm_le S _).trans_eq (zeroExtendLp_norm hT u)
  · have he := subdomainLp_norm_le hTS (subdomainZeroExtend S hT u)
    rwa [subdomainLp_zeroExtend hT hTS] at he

theorem subdomainZeroExtend_inner (hT : MeasurableSet T) (hTS : T ⊆ S)
    (u : Lp E 2 (volume.restrict T)) (v : Lp E 2 (volume.restrict S)) :
    inner ℝ (subdomainZeroExtend S hT u) v = inner ℝ u (subdomainLp hTS v) := by
  simp only [L2.inner_def]
  calc
    _ = ∫ x, T.indicator (fun x => inner ℝ (u x) (v x)) x ∂volume.restrict S := by
      apply integral_congr_ae
      filter_upwards [subdomainZeroExtend_ae hT u] with x hx
      rw [hx]
      by_cases ht : x ∈ T
      · simp only [indicator_of_mem ht]
      · simp only [indicator_of_notMem ht,inner_zero_left]
    _ = ∫ x in T, inner ℝ (u x) (v x) := by
      rw [integral_indicator hT,Measure.restrict_restrict hT,inter_eq_left.mpr hTS]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [subdomainLp_ae hTS v] with x hx
      rw [hx]

end Carleman
