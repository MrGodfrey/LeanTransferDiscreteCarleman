module
public import Carleman.Spatial.SubdomainLpLimit
public import Carleman.Spatial.WeightedTimeContinuity
public import Carleman.Control.ObservedRegionLp
/-! Actual zero extension and identical spatial weights preserve the genuine energy squares. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def subdomainZeroExtendCLM [CompleteSpace E] (S T : Set (SpatialCoordinates d)) :
    Lp E 2 (volume.restrict T) →L[ℝ] Lp E 2 (volume.restrict S) :=
  (Physical.restrictRegionCLM (ν := volume) (E := E) S).comp
    (Physical.restrictRegionCLM (ν := volume) (E := E) T).adjoint

theorem subdomainZeroExtendCLM_apply [CompleteSpace E] (hT : MeasurableSet T)
    (u : Lp E 2 (volume.restrict T)) :
    subdomainZeroExtendCLM S T u=subdomainZeroExtend S hT u := by
  simp only [subdomainZeroExtendCLM,ContinuousLinearMap.comp_apply,Physical.restrictRegion_adjoint T hT]
  rfl

theorem subdomainZeroExtend_multiplier (hT : MeasurableSet T)
    (wS : BoundedMultiplier (volume.restrict S)) (wT : BoundedMultiplier (volume.restrict T))
    (hw : wS.value=ᵐ[volume.restrict T] wT.value) (u : Lp E 2 (volume.restrict T)) :
    wS.map (subdomainZeroExtend S hT u)=subdomainZeroExtend S hT (wT.map u) := by
  have hm := (ae_restrict_iff' hT).mp (wT.map_ae u)
  have hh := (ae_restrict_iff' hT).mp hw
  apply Lp.ext
  filter_upwards [wS.map_ae (subdomainZeroExtend S hT u),subdomainZeroExtend_ae hT u,
    subdomainZeroExtend_ae hT (wT.map u),hm.filter_mono ae_restrict_le,hh.filter_mono ae_restrict_le]
    with x h1 h2 h3 h4 h5
  rw [h1,h2,h3]
  by_cases ht : x∈T
  · simp only [indicator_of_mem ht,h4 ht,h5 ht]
  · simp only [indicator_of_notMem ht,smul_zero]

theorem subdomainZeroExtend_seminorm (hT : MeasurableSet T) (hTS : T⊆S)
    (wS : BoundedMultiplier (volume.restrict S)) (wT : BoundedMultiplier (volume.restrict T))
    (hw : wS.value=ᵐ[volume.restrict T] wT.value) (u : Lp E 2 (volume.restrict T)) :
    wS.seminorm (subdomainZeroExtend S hT u)=wT.seminorm u := by
  rw [BoundedMultiplier.seminorm_apply,subdomainZeroExtend_multiplier hT wS wT hw,
    subdomainZeroExtend_norm hT hTS,BoundedMultiplier.seminorm_apply]

theorem subdomainZeroExtend_cutoff (hT : MeasurableSet T)
    (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W) (u : Lp E 2 (volume.restrict T)) :
    (BoundedMultiplier.cutoff W hW).map (subdomainZeroExtend S hT u)=
      subdomainZeroExtend S hT ((BoundedMultiplier.cutoff W hW).map u) :=
  subdomainZeroExtend_multiplier hT (BoundedMultiplier.cutoff (ν := volume.restrict S) W hW)
    (BoundedMultiplier.cutoff (ν := volume.restrict T) W hW) (Eventually.of_forall fun _ => rfl) u

theorem timeSq_subdomainZeroExtend [CompleteSpace E] (hT : MeasurableSet T) (hTS : T⊆S)
    (g : TimeGrid) (ρS : SpatialProfile (volume.restrict S)) (ρT : SpatialProfile (volume.restrict T))
    (hρ : ρS.value=ᵐ[volume.restrict T] ρT.value) (w : TimeWeight) (τ s : ℝ)
    (u : Lp (Lp E 2 (volume.restrict T)) 2 g.timeMeasure) :
    timeSq g w.q s (fun t => (ρS.multiplier w τ t).seminorm)
      ((subdomainZeroExtendCLM S T).compLp u)=
      timeSq g w.q s (fun t => (ρT.multiplier w τ t).seminorm) u := by
  unfold timeSq
  apply integral_congr_ae
  filter_upwards [(subdomainZeroExtendCLM S T).coeFn_compLp u] with t ht
  unfold timeDensity
  rw [ht,subdomainZeroExtendCLM_apply hT]
  have he := subdomainZeroExtend_seminorm hT hTS (ρS.multiplier w τ t) (ρT.multiplier w τ t)
    (by filter_upwards [hρ] with x hx; simp only [SpatialProfile.multiplier,hx]) (u t)
  rw [he]

theorem subdomainTimeZeroExtend_cutoff [CompleteSpace E] (hT : MeasurableSet T)
    (g : TimeGrid) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (u : Lp (Lp E 2 (volume.restrict T)) 2 g.timeMeasure) :
    (BoundedMultiplier.cutoff W hW).continuousLinearMap.compLp ((subdomainZeroExtendCLM S T).compLp u)=
      (subdomainZeroExtendCLM S T).compLp ((BoundedMultiplier.cutoff W hW).continuousLinearMap.compLp u) := by
  apply Lp.ext
  filter_upwards [(BoundedMultiplier.cutoff W hW).continuousLinearMap.coeFn_compLp
      ((subdomainZeroExtendCLM S T).compLp u),
    (subdomainZeroExtendCLM S T).coeFn_compLp u,
    (subdomainZeroExtendCLM S T).coeFn_compLp ((BoundedMultiplier.cutoff W hW).continuousLinearMap.compLp u),
    (BoundedMultiplier.cutoff W hW).continuousLinearMap.coeFn_compLp u] with t h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  simpa only [subdomainZeroExtendCLM_apply hT,BoundedMultiplier.continuousLinearMap_apply] using subdomainZeroExtend_cutoff hT W hW (u t)

end Carleman
