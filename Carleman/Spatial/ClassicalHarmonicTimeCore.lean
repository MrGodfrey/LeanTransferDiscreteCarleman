module

public import Carleman.Spatial.ClassicalDirichletTimeCore

/-! Actual smooth harmonic functions realize the derivative and operator fields of the same graph. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0 < d)
  (hb : Bornology.IsBounded S) (g : TimeGrid)

theorem harmonicGraph_mem_classicalDirichletTimeCore (n : ℤ)
    (x y : (boundedDirichletOriginalForm hS hd hb).model.operatorGraph)
    (φ ψ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hx : (boundedDirichletOriginalForm hS hd hb).model.graphH x=φ.toLp (volume.restrict S))
    (hy : (boundedDirichletOriginalForm hS hd hb).model.graphH y=ψ.toLp (volume.restrict S))
    (hAx : (boundedDirichletOriginalForm hS hd hb).model.graphA x= -φ.laplacianOnLp S)
    (hAy : (boundedDirichletOriginalForm hS hd hb).model.graphA y= -ψ.laplacianOnLp S)
    (hφ : ∀ z ∈ frontier S, φ.value z=0) (hψ : ∀ z ∈ frontier S, ψ.value z=0) :
    (boundedDirichletOriginalForm hS hd hb).model.harmonicGraph g n x y ∈
      classicalDirichletTimeCore hS hd hb g := by
  let B := (boundedDirichletOriginalForm hS hd hb).model
  let freq := g.angularFrequency n
  let F := fun tx : ℝ × SpatialCoordinates d =>
    Real.cos (freq*tx.1)*φ.value tx.2 + Real.sin (freq*tx.1)*ψ.value tx.2
  have hF : ContDiff ℝ ∞ F :=
    ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_fst)).mul (φ.smooth.comp contDiff_snd)).add
      ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_fst)).mul (ψ.smooth.comp contDiff_snd))
  refine ⟨F,hF,?_,?_,?_,?_⟩
  · intro tx
    change Real.cos (freq*(tx.1+g.period))*φ.value (tx.2+0) +
      Real.sin (freq*(tx.1+g.period))*ψ.value (tx.2+0)=F tx
    rw [add_zero,mul_add,g.angularFrequency_period,Real.cos_add_int_mul_two_pi,Real.sin_add_int_mul_two_pi]
  · intro t z hz
    change Real.cos (freq*t)*φ.value z+Real.sin (freq*t)*ψ.value z=0
    rw [hφ z hz,hψ z hz,mul_zero,mul_zero,add_zero]
  · intro t
    rw [B.harmonicGraph_trace,hx,hy]
    change (Real.cos (freq*t) • φ.toLp (volume.restrict S)+Real.sin (freq*t) • ψ.toLp (volume.restrict S) :
      Lp ℝ 2 (volume.restrict S)) =ᵐ[volume.restrict S] (fun z => F (t,z))
    filter_upwards [Lp.coeFn_add (Real.cos (freq*t) • φ.toLp (volume.restrict S))
      (Real.sin (freq*t) • ψ.toLp (volume.restrict S)),
      Lp.coeFn_smul (Real.cos (freq*t)) (φ.toLp (volume.restrict S)),
      Lp.coeFn_smul (Real.sin (freq*t)) (ψ.toLp (volume.restrict S)),
      φ.toLp_ae (volume.restrict S),ψ.toLp_ae (volume.restrict S)] with z ha hc hs hφz hψz
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hc,hs,hφz,hψz,F] using ha
  · filter_upwards [B.harmonicGraph_derivative_ae g n x y,B.harmonicGraph_operator_ae g n x y]
      with t hdt hat
    rw [hdt,hat,hx,hy,hAx,hAy]
    constructor
    · change ((-freq*Real.sin (freq*t)) • φ.toLp (volume.restrict S)+
        (freq*Real.cos (freq*t)) • ψ.toLp (volume.restrict S) : Lp ℝ 2 (volume.restrict S))
          =ᵐ[volume.restrict S] (fun z => smoothD (1,0) F (t,z))
      filter_upwards [Lp.coeFn_add ((-freq*Real.sin (freq*t)) • φ.toLp (volume.restrict S))
        ((freq*Real.cos (freq*t)) • ψ.toLp (volume.restrict S)),
        Lp.coeFn_smul (-freq*Real.sin (freq*t)) (φ.toLp (volume.restrict S)),
        Lp.coeFn_smul (freq*Real.cos (freq*t)) (ψ.toLp (volume.restrict S)),
        φ.toLp_ae (volume.restrict S),ψ.toLp_ae (volume.restrict S)] with z ha hc hs hφz hψz
      rw [spaceTime_timeD hF]
      change _=deriv (fun s => Real.cos (freq*s)*φ.value z+Real.sin (freq*s)*ψ.value z) t
      rw [smooth_harmonic_time_derivative]
      simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hc,hs,hφz,hψz] using ha
    · change (Real.cos (freq*t) • -φ.laplacianOnLp S+Real.sin (freq*t) • -ψ.laplacianOnLp S :
        Lp ℝ 2 (volume.restrict S)) =ᵐ[volume.restrict S]
          (fun z => -directionalLap spaceTimeSpatialDirection F (t,z))
      filter_upwards [Lp.coeFn_add (Real.cos (freq*t) • -φ.laplacianOnLp S)
        (Real.sin (freq*t) • -ψ.laplacianOnLp S),
        Lp.coeFn_smul (Real.cos (freq*t)) (-φ.laplacianOnLp S),
        Lp.coeFn_smul (Real.sin (freq*t)) (-ψ.laplacianOnLp S),
        Lp.coeFn_neg (φ.laplacianOnLp S),Lp.coeFn_neg (ψ.laplacianOnLp S),
        φ.laplacianOnLp_ae S,ψ.laplacianOnLp_ae S] with z ha hc hs hnegφ hnegψ hφz hψz
      rw [spaceTime_directionalLap hF]
      change _= -spatialLaplacian (fun w => Real.cos (freq*t)*φ.value w+Real.sin (freq*t)*ψ.value w) z
      rw [smooth_harmonic_spatial_laplacian freq φ.smooth ψ.smooth]
      simpa only [Pi.add_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul,hc,hs,hnegφ,hnegψ,hφz,hψz,
        mul_neg,neg_add] using ha

end Carleman
