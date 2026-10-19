module

public import Carleman.Spatial.CutoffPoissonConvolution
public import Carleman.Spatial.StrongMollifierLimit
public import Carleman.Spatial.InteriorWeakPoincare
public import Carleman.Spatial.SubdomainContinuity

/-! The actual gradients of a localized mollification converge strongly on
any open subdomain where the fixed cutoff is identically one. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Convolution ContDiff Topology
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

theorem cutoff_fderiv_eq (hT : IsOpen T) (η : SpatialTest S)
    (hη : ∀ x ∈ T, η.value x = 1) (F : SpatialCoordinates d → ℝ)
    {x : SpatialCoordinates d} (hx : x ∈ T) :
    fderiv ℝ (fun y => η.value y*F y) x = fderiv ℝ F x := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hT.mem_nhds hx] with y hy
  rw [hη y hy,one_mul]

theorem cutoff_mollifier_gradient_tendsto (hS : IsOpen S) (hT : IsOpen T)
    (hTS : T ⊆ S) (η : SpatialTest S) (hη : ∀ x ∈ T, η.value x = 1)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (i : Fin d) :
    let φ := fun n => η.mulSmooth ((spatialMollifier d n).smooth_convolution
      (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)));
    Tendsto (fun n => subdomainLp hTS ((φ n).derivativeLp (volume.restrict S)
      (EuclideanSpace.basisFun (Fin d) ℝ i))) atTop
      (𝓝 (derivativeComponent (Sym.cons i Sym.nil)
        (WeakSobolevJet.field 1 (WeakSobolevJet.restrictSubdomain hTS u)))) := by
  intro φ
  let g := derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)
  have hge : Physical.restrictRegionLp T (zeroExtendLp hS.measurableSet g) =
      derivativeComponent (Sym.cons i Sym.nil)
        (WeakSobolevJet.field 1 (WeakSobolevJet.restrictSubdomain hTS u)) := by
    change Physical.restrictRegionLp T (zeroExtendLp hS.measurableSet g) =
      derivativeComponent (Sym.cons i Sym.nil) (subdomainLp hTS (WeakSobolevJet.field 1 u))
    rw [derivativeComponent_subdomain]
    apply Lp.ext
    exact (Physical.restrictRegionLp_ae T _).trans
      (((zeroExtendLp_ae_restrict hS.measurableSet g).filter_mono
        (ae_mono (Measure.restrict_mono hTS le_rfl))).trans (subdomainLp_ae hTS g).symm)
  have ht := (Physical.restrictRegionCLM (E := ℝ) T).continuous.tendsto
    (zeroExtendLp hS.measurableSet g) |>.comp (spatialMollificationLp_tendsto (zeroExtendLp hS.measurableSet g))
  change Tendsto (fun n => Physical.restrictRegionLp T
    (spatialMollificationLp n (zeroExtendLp hS.measurableSet g))) atTop
    (𝓝 (Physical.restrictRegionLp T (zeroExtendLp hS.measurableSet g))) at ht
  rw [hge] at ht
  apply ht.congr'
  filter_upwards [compact_mollifier_eventually_inside hS η.compact η.support] with n hn
  apply Lp.ext
  filter_upwards [Physical.restrictRegionLp_ae T (spatialMollificationLp n (zeroExtendLp hS.measurableSet g)),
    (spatialMollificationLp_ae n (zeroExtendLp hS.measurableSet g)).filter_mono ae_restrict_le,
    subdomainLp_ae hTS ((φ n).derivativeLp (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)),
    ((φ n).derivativeLp_ae (volume.restrict S) (EuclideanSpace.basisFun (Fin d) ℝ i)).filter_mono
      (ae_mono (Measure.restrict_mono hTS le_rfl)),ae_restrict_mem hT.measurableSet] with x h1 h2 h3 h4 hx
  rw [h1,h2,h3,h4]
  change _ = fderiv ℝ (fun y => η.value y *
    (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (spatialMollifier d n).value) y) x (EuclideanSpace.basisFun (Fin d) ℝ i)
  rw [cutoff_fderiv_eq hT η hη _ hx]
  have hxη : x ∈ tsupport η.value := subset_tsupport _ (by rw [Function.mem_support,hη x hx]; norm_num)
  exact (((u.property 0 Sym.nil i).zeroExtend hS.measurableSet).fderiv_convolution_local
    (spatialMollifier d n) x (hn x hxη)).symm

end Carleman
