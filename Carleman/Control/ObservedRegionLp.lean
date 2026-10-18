module

public import Carleman.Control.ConformingPhysicalOperators
public import Carleman.Spatial.ZeroExtensionLp

/-! Actual restriction and zero extension between L2(Omega) and L2(omega).
The adjoint and norm identities use a.e. classes, including null regions. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω}

def restrictRegionLp (ω : Set Ω) (u : Lp E 2 ν) : Lp E 2 (ν.restrict ω) :=
  ((Lp.memLp u).mono_measure Measure.restrict_le_self).toLp u

omit [InnerProductSpace ℝ E] in
theorem restrictRegionLp_ae (ω : Set Ω) (u : Lp E 2 ν) :
    restrictRegionLp ω u =ᵐ[ν.restrict ω] u := MemLp.coeFn_toLp _

omit [InnerProductSpace ℝ E] in
theorem restrictRegionLp_norm_le (ω : Set Ω) (u : Lp E 2 ν) :
    ‖restrictRegionLp ω u‖ ≤ ‖u‖ := by
  rw [Lp.norm_def,Lp.norm_def,eLpNorm_congr_ae (restrictRegionLp_ae ω u)]
  exact ENNReal.toReal_mono (Lp.memLp u).ne (eLpNorm_mono_measure u Measure.restrict_le_self)

def restrictRegionLinear (ω : Set Ω) : Lp E 2 ν →ₗ[ℝ] Lp E 2 (ν.restrict ω) where
  toFun := restrictRegionLp ω
  map_add' u v := by
    apply Lp.ext
    filter_upwards [restrictRegionLp_ae ω (u+v),restrictRegionLp_ae ω u,restrictRegionLp_ae ω v,
      (Lp.coeFn_add u v).filter_mono ae_restrict_le,
      Lp.coeFn_add (restrictRegionLp ω u) (restrictRegionLp ω v)] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1,h5,h2,h3,h4]
  map_smul' c u := by
    change restrictRegionLp ω (c • u) = c • restrictRegionLp ω u
    apply Lp.ext
    filter_upwards [restrictRegionLp_ae ω (c • u),restrictRegionLp_ae ω u,
      (Lp.coeFn_smul c u).filter_mono ae_restrict_le,
      Lp.coeFn_smul c (restrictRegionLp ω u)] with x h1 h2 h3 h4
    simp only [Pi.smul_apply] at h3 h4
    rw [h1,h4,h2,h3]

def restrictRegionCLM (ω : Set Ω) : Lp E 2 ν →L[ℝ] Lp E 2 (ν.restrict ω) :=
  (restrictRegionLinear ω).mkContinuous 1 (fun u => by
    change ‖restrictRegionLp ω u‖ ≤ 1*‖u‖
    simpa only [one_mul] using restrictRegionLp_norm_le ω u)

theorem integral_inner_zeroExtend (ω : Set Ω) (hω : MeasurableSet ω)
    (u : Lp E 2 (ν.restrict ω)) (v : Ω → E) :
    (∫ x, inner ℝ (zeroExtendLp hω u x) (v x) ∂ν) =
      ∫ x in ω, inner ℝ (u x) (v x) ∂ν := by
  rw [← integral_indicator hω]
  apply integral_congr_ae
  filter_upwards [zeroExtendLp_ae hω u] with x hx
  rw [hx]
  by_cases hxω : x ∈ ω
  · simp only [indicator_of_mem hxω]
  · simp only [indicator_of_notMem hxω,inner_zero_left]

theorem restrictRegion_adjoint [CompleteSpace E] (ω : Set Ω) (hω : MeasurableSet ω)
    (u : Lp E 2 (ν.restrict ω)) :
    (restrictRegionCLM (ν := ν) ω).adjoint u = zeroExtendLp hω u := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ u (restrictRegionLp ω v) = inner ℝ (zeroExtendLp hω u) v
  simp only [L2.inner_def]
  rw [integral_inner_zeroExtend]
  apply integral_congr_ae
  filter_upwards [restrictRegionLp_ae ω v] with x hx
  rw [hx]

theorem zeroExtend_restrictRegion (ω : Set Ω) (hω : MeasurableSet ω) (u : Lp E 2 ν) :
    zeroExtendLp hω (restrictRegionLp ω u) = (BoundedMultiplier.cutoff ω hω).map u := by
  apply Lp.ext
  filter_upwards [zeroExtendLp_ae hω (restrictRegionLp ω u),
    (ae_restrict_iff' hω).mp (restrictRegionLp_ae ω u),
    (BoundedMultiplier.cutoff ω hω).map_ae u] with x he hr hc
  rw [he,hc]
  by_cases hx : x ∈ ω
  · simp only [indicator_of_mem hx,BoundedMultiplier.cutoff,one_smul,hr hx]
  · simp only [indicator_of_notMem hx,BoundedMultiplier.cutoff,zero_smul]

theorem restrictRegion_norm_eq_cutoff (ω : Set Ω) (hω : MeasurableSet ω) (u : Lp E 2 ν) :
    ‖restrictRegionLp ω u‖ = ‖(BoundedMultiplier.cutoff ω hω).map u‖ := by
  rw [← zeroExtendLp_norm hω,zeroExtend_restrictRegion]

theorem restrictRegionCLM_norm (ω : Set Ω) : ‖restrictRegionCLM (ν := ν) (E := E) ω‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖restrictRegionLp ω u‖ ≤ 1*‖u‖
  simpa only [one_mul] using restrictRegionLp_norm_le ω u

end Carleman.Physical
