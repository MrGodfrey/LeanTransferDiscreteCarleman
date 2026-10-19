module

public import Carleman.Spatial.DirichletHeatContinuity
public import Carleman.Spatial.BoxSmoothHeatBothSigns

/-! Two-layer representatives of values, observations and the genuine oriented heat residual. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0 < d)
  (hb : Bornology.IsBounded S) (g : TimeGrid)
  (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g)
  {F : (ℝ × SpatialCoordinates d) → ℝ}

theorem periodicGraph_value_classical_ae
    (htrace : ∀ t : Icc 0 g.period, p.val.1 t =ᵐ[volume.restrict S] (fun x => F (t,x))) :
    ∀ᵐ t ∂g.timeMeasure, g.pathL2 p.val.1 t =ᵐ[volume.restrict S] (fun x => F (t,x)) := by
  filter_upwards [g.pathL2_ae p.val.1,ae_restrict_mem measurableSet_Ioo] with t ht hmem
  rw [ht,g.clampPath_on _ t ⟨hmem.1.le,hmem.2.le⟩]
  exact htrace ⟨t,⟨hmem.1.le,hmem.2.le⟩⟩

theorem periodicGraph_residual_classical_ae (ε : ℝ) (hF : ContDiff ℝ ∞ F)
    (hfields : ∀ᵐ t ∂g.timeMeasure,
      (p.val.2.1 t =ᵐ[volume.restrict S] (fun x => smoothD (1,0) F (t,x))) ∧
      (p.val.2.2 t =ᵐ[volume.restrict S] (fun x => -directionalLap spaceTimeSpatialDirection F (t,x)))) :
    ∀ᵐ t ∂g.timeMeasure,
      (ε • p.val.2.1+p.val.2.2 : Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure) t
        =ᵐ[volume.restrict S] (fun x => spaceTimeOrientedHeat ε F (t,x)) := by
  filter_upwards [hfields,Lp.coeFn_add (ε • p.val.2.1) p.val.2.2,Lp.coeFn_smul ε p.val.2.1]
    with t hf ha hs
  rw [ha]
  simp only [Pi.add_apply,hs,Pi.smul_apply]
  filter_upwards [Lp.coeFn_add (ε • p.val.2.1 t) (p.val.2.2 t),Lp.coeFn_smul ε (p.val.2.1 t),hf.1,hf.2]
    with x hadd hsmul hdt hA
  rw [hadd]
  simp only [Pi.add_apply,hsmul,Pi.smul_apply,smul_eq_mul,hdt,hA,
    spaceTime_timeD hF,spaceTime_directionalLap hF]
  rfl

theorem periodicGraph_observation_classical_ae (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (htrace : ∀ t : Icc 0 g.period, p.val.1 t =ᵐ[volume.restrict S] (fun x => F (t,x))) :
    ∀ᵐ t ∂g.timeMeasure,
      ((BoundedMultiplier.cutoff W hW).continuousLinearMap.compLp (g.pathL2 p.val.1)) t
        =ᵐ[volume.restrict S] (fun x => W.indicator (fun y => F (t,y)) x) := by
  filter_upwards [periodicGraph_value_classical_ae hS hd hb g p htrace,
    (BoundedMultiplier.cutoff W hW).continuousLinearMap.coeFn_compLp (g.pathL2 p.val.1)]
    with t hv ho
  rw [ho]
  filter_upwards [(BoundedMultiplier.cutoff W hW).map_ae (g.pathL2 p.val.1 t),hv] with x hx hval
  change (BoundedMultiplier.cutoff W hW).map (g.pathL2 p.val.1 t) x=_
  rw [hx,hval]
  by_cases hw : x ∈ W <;> simp [BoundedMultiplier.cutoff,hw]

end Carleman
