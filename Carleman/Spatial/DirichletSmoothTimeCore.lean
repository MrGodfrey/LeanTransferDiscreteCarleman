module

public import Carleman.Spatial.SmoothDirichletGraph
public import Carleman.Continuous.HarmonicStateDensity

/-! Actual globally smooth periodic functions with zero boundary, inside the original time graph. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0 < d)
  (hb : Bornology.IsBounded S) (g : TimeGrid)

def smoothDirichletTimeCore :
    Submodule ℝ ((boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) where
  carrier := fun p => ∃ F : (ℝ × SpatialCoordinates d) → ℝ,
    ContDiff ℝ ∞ F ∧ Function.Periodic F (g.period,0) ∧
    (∀ t : ℝ, ∀ x ∈ frontier S, F (t,x)=0) ∧
    ∀ t : Icc 0 g.period, p.val.1 t =ᵐ[volume.restrict S] (fun x => F (t,x))
  zero_mem' := by
    refine ⟨0,contDiff_const,fun _ => rfl,fun _ _ _ => rfl,?_⟩
    intro t
    exact Lp.coeFn_zero ℝ 2 (volume.restrict S)
  add_mem' := by
    rintro p q ⟨F,hF,hFp,hFb,hFt⟩ ⟨G,hG,hGp,hGb,hGt⟩
    refine ⟨F+G,hF.add hG,hFp.add hGp,?_,?_⟩
    · intro t x hx
      change F (t,x)+G (t,x)=0
      rw [hFb t x hx,hGb t x hx,add_zero]
    · intro t
      change (p.val.1 t+q.val.1 t : Lp ℝ 2 (volume.restrict S)) =ᵐ[volume.restrict S] _
      filter_upwards [Lp.coeFn_add (p.val.1 t) (q.val.1 t),hFt t,hGt t] with x hx hp hq
      simpa only [Pi.add_apply,hp,hq] using hx
  smul_mem' := by
    rintro c p ⟨F,hF,hFp,hFb,hFt⟩
    refine ⟨fun tx => c*F tx,contDiff_const.mul hF,?_,?_,?_⟩
    · intro tx
      change c*F (tx+(g.period,0))=c*F tx
      rw [hFp tx]
    · intro t x hx
      change c*F (t,x)=0
      rw [hFb t x hx,mul_zero]
    · intro t
      change (c • p.val.1 t : Lp ℝ 2 (volume.restrict S)) =ᵐ[volume.restrict S] _
      filter_upwards [Lp.coeFn_smul c (p.val.1 t),hFt t] with x hx hp
      simpa only [Pi.smul_apply,smul_eq_mul,hp] using hx

theorem harmonicGraph_mem_smoothDirichletTimeCore (n : ℤ)
    (x y : (boundedDirichletOriginalForm hS hd hb).model.operatorGraph)
    (φ ψ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hx : (boundedDirichletOriginalForm hS hd hb).model.graphH x=φ.toLp (volume.restrict S))
    (hy : (boundedDirichletOriginalForm hS hd hb).model.graphH y=ψ.toLp (volume.restrict S))
    (hφ : ∀ z ∈ frontier S, φ.value z=0) (hψ : ∀ z ∈ frontier S, ψ.value z=0) :
    (boundedDirichletOriginalForm hS hd hb).model.harmonicGraph g n x y ∈
      smoothDirichletTimeCore hS hd hb g := by
  let B := (boundedDirichletOriginalForm hS hd hb).model
  let freq := g.angularFrequency n
  let F := fun tx : ℝ × SpatialCoordinates d =>
    Real.cos (freq*tx.1)*φ.value tx.2 + Real.sin (freq*tx.1)*ψ.value tx.2
  refine ⟨F,?_,?_,?_,?_⟩
  · exact ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_fst)).mul (φ.smooth.comp contDiff_snd)).add
      ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_fst)).mul (ψ.smooth.comp contDiff_snd))
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

end Carleman
