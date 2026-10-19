module

public import Carleman.Spatial.DirichletSmoothTimeCore
public import Carleman.Spatial.SmoothDifferentialLinearity
public import Carleman.Continuous.HarmonicGraphFields

/-! A smooth time core with explicit identities for both actual Bochner graph fields. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0 < d)
  (hb : Bornology.IsBounded S) (g : TimeGrid)

def classicalDirichletTimeCore :
    Submodule ℝ ((boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) where
  carrier := fun p => ∃ F : (ℝ × SpatialCoordinates d) → ℝ,
    ContDiff ℝ ∞ F ∧ Function.Periodic F (g.period,0) ∧
    (∀ t : ℝ, ∀ x ∈ frontier S, F (t,x)=0) ∧
    (∀ t : Icc 0 g.period, p.val.1 t =ᵐ[volume.restrict S] (fun x => F (t,x))) ∧
    ∀ᵐ t ∂g.timeMeasure,
      (p.val.2.1 t =ᵐ[volume.restrict S] (fun x => smoothD (1,0) F (t,x))) ∧
      (p.val.2.2 t =ᵐ[volume.restrict S] (fun x => -directionalLap spaceTimeSpatialDirection F (t,x)))
  zero_mem' := by
    refine ⟨0,contDiff_const,fun _ => rfl,fun _ _ _ => rfl,?_,?_⟩
    · intro t
      exact Lp.coeFn_zero ℝ 2 (volume.restrict S)
    · filter_upwards [Lp.coeFn_zero (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure] with t ht
      change ((0 : Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure) t =ᵐ[volume.restrict S] _) ∧
        ((0 : Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure) t =ᵐ[volume.restrict S] _)
      rw [ht]
      constructor
      · filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict S)] with x hx
        simpa [smoothD] using hx
      · filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict S)] with x hx
        change (0 : Lp ℝ 2 (volume.restrict S)) x= -directionalLap spaceTimeSpatialDirection (fun _ => 0) (t,x)
        simpa only [directionalLap_zero,neg_zero,Pi.zero_apply] using hx
  add_mem' := by
    rintro p q ⟨F,hF,hFp,hFb,hFt,hFd⟩ ⟨G,hG,hGp,hGb,hGt,hGd⟩
    refine ⟨F+G,hF.add hG,hFp.add hGp,?_,?_,?_⟩
    · intro t x hx
      change F (t,x)+G (t,x)=0
      rw [hFb t x hx,hGb t x hx,add_zero]
    · intro t
      change (p.val.1 t+q.val.1 t : Lp ℝ 2 (volume.restrict S)) =ᵐ[volume.restrict S] _
      filter_upwards [Lp.coeFn_add (p.val.1 t) (q.val.1 t),hFt t,hGt t] with x hx hp hq
      simpa only [Pi.add_apply,hp,hq] using hx
    · filter_upwards [hFd,hGd,Lp.coeFn_add p.val.2.1 q.val.2.1,Lp.coeFn_add p.val.2.2 q.val.2.2]
        with t hf hg hdt hat
      change ((p.val.2.1+q.val.2.1 : Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure) t =ᵐ[volume.restrict S] _) ∧
        ((p.val.2.2+q.val.2.2 : Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure) t =ᵐ[volume.restrict S] _)
      rw [hdt,hat]
      constructor
      · filter_upwards [Lp.coeFn_add (p.val.2.1 t) (q.val.2.1 t),hf.1,hg.1] with x hx hp hq
        change (p.val.2.1 t+q.val.2.1 t : Lp ℝ 2 (volume.restrict S)) x=
          smoothD (1,0) (fun tx => F tx+G tx) (t,x)
        simpa only [Pi.add_apply,hp,hq,smoothD_add hF hG] using hx
      · filter_upwards [Lp.coeFn_add (p.val.2.2 t) (q.val.2.2 t),hf.2,hg.2] with x hx hp hq
        change (p.val.2.2 t+q.val.2.2 t : Lp ℝ 2 (volume.restrict S)) x=
          -directionalLap spaceTimeSpatialDirection (fun tx => F tx+G tx) (t,x)
        simpa only [Pi.add_apply,hp,hq,directionalLap_add _ hF hG,neg_add] using hx
  smul_mem' := by
    rintro c p ⟨F,hF,hFp,hFb,hFt,hFd⟩
    refine ⟨fun tx => c*F tx,contDiff_const.mul hF,?_,?_,?_,?_⟩
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
    · filter_upwards [hFd,Lp.coeFn_smul c p.val.2.1,Lp.coeFn_smul c p.val.2.2] with t hf hdt hat
      change ((c • p.val.2.1 : Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure) t =ᵐ[volume.restrict S] _) ∧
        ((c • p.val.2.2 : Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure) t =ᵐ[volume.restrict S] _)
      rw [hdt,hat]
      constructor
      · filter_upwards [Lp.coeFn_smul c (p.val.2.1 t),hf.1] with x hx hp
        simpa only [Pi.smul_apply,smul_eq_mul,hp,smoothD_const_mul hF] using hx
      · filter_upwards [Lp.coeFn_smul c (p.val.2.2 t),hf.2] with x hx hp
        simpa only [Pi.smul_apply,smul_eq_mul,hp,directionalLap_const_mul _ hF,mul_neg] using hx

end Carleman
