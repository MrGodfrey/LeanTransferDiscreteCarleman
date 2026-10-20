module

public import Carleman.Spatial.InteriorWeakPoincare
public import Carleman.Spatial.StrongMollifierLimit
public import Carleman.Spatial.SobolevRestriction
public import Carleman.Spatial.WeakProduct
public import Carleman.Spatial.SpatialTestDerivative

/-! Actual compact tests built from local mollification converge together
with their weak directional derivatives, without an exterior Sobolev extension. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
namespace Carleman
open Physical
variable {d : ℕ} {S : Set (SpatialCoordinates d)}
namespace SpatialTest

def valueMultiplier (φ : SpatialTest S) (ν : Measure (SpatialCoordinates d)) : BoundedMultiplier ν where
  value := φ.value
  measurable := φ.smooth.continuous.aestronglyMeasurable
  bound := (φ.compact.exists_bound_of_continuous φ.smooth.continuous).choose
  bound_nonneg := (norm_nonneg (φ.value 0)).trans
    ((φ.compact.exists_bound_of_continuous φ.smooth.continuous).choose_spec 0)
  bounded := Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using
      (φ.compact.exists_bound_of_continuous φ.smooth.continuous).choose_spec x

def mollifiedProduct (φ : SpatialTest S) (hS : IsOpen S)
    (u : Lp ℝ 2 (volume.restrict S)) (n : ℕ) : SpatialTest S :=
  φ.mulOn hS ((spatialMollifier d n).smooth_convolution (zeroExtendLp hS.measurableSet u)).contDiffOn

theorem mollifiedProduct_toLp (φ : SpatialTest S) (hS : IsOpen S)
    (u : Lp ℝ 2 (volume.restrict S)) (n : ℕ) :
    (φ.mollifiedProduct hS u n).toLp (volume.restrict S)=
      (φ.valueMultiplier (volume.restrict S)).map
        (restrictRegionLp S (spatialMollificationLp n (zeroExtendLp hS.measurableSet u))) := by
  apply Lp.ext
  filter_upwards [(φ.mollifiedProduct hS u n).toLp_ae (volume.restrict S),
    (φ.valueMultiplier (volume.restrict S)).map_ae
      (restrictRegionLp S (spatialMollificationLp n (zeroExtendLp hS.measurableSet u))),
    restrictRegionLp_ae S (spatialMollificationLp n (zeroExtendLp hS.measurableSet u)),
    (spatialMollificationLp_ae n (zeroExtendLp hS.measurableSet u)).filter_mono ae_restrict_le]
    with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  change _*φ.value x=φ.value x*_
  ring

theorem mollifiedProduct_derivativeLp_eventually (φ : SpatialTest S) (hS : IsOpen S)
    {u v : Lp ℝ 2 (volume.restrict S)} {e : SpatialCoordinates d}
    (huv : IsWeakSpatialDerivative (volume.restrict S) S e u v) :
    ∀ᶠ n in atTop, (φ.mollifiedProduct hS u n).derivativeLp (volume.restrict S) e=
      (φ.valueMultiplier (volume.restrict S)).map
        (restrictRegionLp S (spatialMollificationLp n (zeroExtendLp hS.measurableSet v)))+
      ((φ.derivativeTest e).valueMultiplier (volume.restrict S)).map
        (restrictRegionLp S (spatialMollificationLp n (zeroExtendLp hS.measurableSet u))) := by
  filter_upwards [compact_mollifier_eventually_inside hS φ.compact φ.support] with n hn
  let U := spatialMollificationLp n (zeroExtendLp hS.measurableSet u)
  let V := spatialMollificationLp n (zeroExtendLp hS.measurableSet v)
  let F := zeroExtendLp hS.measurableSet u ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (spatialMollifier d n).value
  have hF : ContDiff ℝ ∞ F := (spatialMollifier d n).smooth_convolution _
  apply Lp.ext
  filter_upwards [(φ.mollifiedProduct hS u n).derivativeLp_ae (volume.restrict S) e,
    Lp.coeFn_add ((φ.valueMultiplier (volume.restrict S)).map (restrictRegionLp S V))
      (((φ.derivativeTest e).valueMultiplier (volume.restrict S)).map (restrictRegionLp S U)),
    (φ.valueMultiplier (volume.restrict S)).map_ae (restrictRegionLp S V),
    ((φ.derivativeTest e).valueMultiplier (volume.restrict S)).map_ae (restrictRegionLp S U),
    restrictRegionLp_ae S V,restrictRegionLp_ae S U,
    (spatialMollificationLp_ae n (zeroExtendLp hS.measurableSet v)).filter_mono ae_restrict_le,
    (spatialMollificationLp_ae n (zeroExtendLp hS.measurableSet u)).filter_mono ae_restrict_le]
    with x h1 h2 h3 h4 h5 h6 h7 h8
  rw [h1,h2,Pi.add_apply,h3,h4,h5,h6,h7,h8]
  change fderiv ℝ (F*φ.value) x e=φ.value x*_+fderiv ℝ φ.value x e*F x
  rw [fderiv_mul (hF.differentiable (by simp) x) (φ.smooth.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  by_cases hx : x ∈ tsupport φ.value
  · rw [(huv.zeroExtend hS.measurableSet).fderiv_convolution_local (spatialMollifier d n) x (hn x hx)]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hx,fderiv_of_notMem_tsupport ℝ hx]
    simp

theorem mollifiedProduct_toLp_tendsto (φ : SpatialTest S) (hS : IsOpen S)
    (u : Lp ℝ 2 (volume.restrict S)) :
    Tendsto (fun n => (φ.mollifiedProduct hS u n).toLp (volume.restrict S)) atTop
      (𝓝 ((φ.valueMultiplier (volume.restrict S)).map u)) := by
  have he : restrictRegionLp S (zeroExtendLp hS.measurableSet u)=u := by
    apply Lp.ext
    exact (restrictRegionLp_ae S _).trans (zeroExtendLp_ae_restrict hS.measurableSet u)
  have ht := ((φ.valueMultiplier (volume.restrict S)).continuousLinearMap.continuous.tendsto _).comp
    (((restrictRegionCLM S).continuous.tendsto _).comp
      (spatialMollificationLp_tendsto (zeroExtendLp hS.measurableSet u)))
  change Tendsto (fun n => (φ.valueMultiplier (volume.restrict S)).map
    (restrictRegionLp S (spatialMollificationLp n (zeroExtendLp hS.measurableSet u)))) atTop
    (𝓝 ((φ.valueMultiplier (volume.restrict S)).map (restrictRegionLp S (zeroExtendLp hS.measurableSet u)))) at ht
  simpa only [mollifiedProduct_toLp,he] using ht

theorem mollifiedProduct_derivativeLp_tendsto (φ : SpatialTest S) (hS : IsOpen S)
    {u v : Lp ℝ 2 (volume.restrict S)} {e : SpatialCoordinates d}
    (huv : IsWeakSpatialDerivative (volume.restrict S) S e u v) :
    Tendsto (fun n => (φ.mollifiedProduct hS u n).derivativeLp (volume.restrict S) e) atTop
      (𝓝 ((φ.valueMultiplier (volume.restrict S)).map v+
        ((φ.derivativeTest e).valueMultiplier (volume.restrict S)).map u)) := by
  have ht := (φ.mollifiedProduct_toLp_tendsto hS v).add
    ((φ.derivativeTest e).mollifiedProduct_toLp_tendsto hS u)
  apply ht.congr'
  filter_upwards [φ.mollifiedProduct_derivativeLp_eventually hS huv] with n hn
  simpa only [mollifiedProduct_toLp] using hn.symm
end SpatialTest
end Carleman
