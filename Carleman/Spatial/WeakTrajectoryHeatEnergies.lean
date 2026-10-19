module

public import Carleman.Spatial.IntervalHeatEnergies
public import Carleman.Spatial.DirichletCommutatorIdentity
public import Carleman.Continuous.PeriodicGraphEquivalence

/-! Exact identities with the original weak trajectory's values, derivatives, operator and weak spatial jet. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0 < d)
  (hb : Bornology.IsBounded S) (g : TimeGrid)
  (u : PeriodicWeakTrajectory g (boundedDirichletOriginalForm hS hd hb).model.domain
    (boundedDirichletOriginalForm hS hd hb).model.operator)

theorem dirichletTrajectory_gradient_ae :
    dirichletPeriodicGradient hS hd hb g u.toPeriodicGraph =ᵐ[g.timeMeasure]
      (fun t => WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb (u.domainValue t))) := by
  let B := (boundedDirichletOriginalForm hS hd hb).model
  filter_upwards [dirichletPeriodicGradient_ae hS hd hb g u.toPeriodicGraph,
    B.periodicEnergy_embed_ae g u.toPeriodicGraph,u.tracePathL2_ae,u.domainValue_ae]
    with t hg he hv hdv
  rw [hg]
  have hj : SobolevHilbert.toJet (B.periodicEnergy g u.toPeriodicGraph t).val=
      dirichletDomainJet hS hd hb (u.domainValue t) := by
    apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
    exact he.trans (hv.trans (hdv.symm.trans (dirichletDomainJet_value hS hd hb (u.domainValue t)).symm))
  exact congrArg (WeakSobolevJet.field 1) hj

include u in
theorem dirichletTrajectory_gradient_memLp :
    MemLp (fun t => WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb (u.domainValue t))) 2 g.timeMeasure :=
  (Lp.memLp (dirichletPeriodicGradient hS hd hb g u.toPeriodicGraph)).ae_eq
    (dirichletTrajectory_gradient_ae hS hd hb g u)

theorem dirichletIntervalHeatLeft_trajectory (ρ : SpatialProfile (volume.restrict S)) (q : ℝ → ℝ) :
    dirichletIntervalHeatLeft hS hd hb g ρ q u.toPeriodicGraph=
      timeSq g q 3 (fun t => (ρ.expMultiplier (q t)).seminorm) u.value+
      timeSq g q 1 (fun t => (ρ.expMultiplier (q t)).seminorm)
        (fun t => WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb (u.domainValue t))) := by
  unfold dirichletIntervalHeatLeft
  exact congrArg₂ (fun x y : ℝ => x+y)
    (timeSq_congr_ae g q 3 _ u.tracePathL2_ae)
    (timeSq_congr_ae g q 1 _ (dirichletTrajectory_gradient_ae hS hd hb g u))

theorem dirichletIntervalHeatRight_trajectory (ρ : SpatialProfile (volume.restrict S)) (q : ℝ → ℝ)
    (ε : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W) :
    dirichletIntervalHeatRight hS hd hb g ρ q ε W hW u.toPeriodicGraph=
      timeSq g q 0 (fun t => (ρ.expMultiplier (q t)).seminorm)
        (fun t => ε • u.derivative t+(boundedDirichletOriginalForm hS hd hb).model.operator (u.domainValue t))+
      timeSq g q 3 (fun t => (ρ.expMultiplier (q t)).seminorm)
        (fun t => (BoundedMultiplier.cutoff W hW).map (u.value t)) := by
  have hr : (ε • u.toPeriodicGraph.val.2.1+u.toPeriodicGraph.val.2.2 :
      Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure) =ᵐ[g.timeMeasure]
      (fun t => ε • u.derivative t+(boundedDirichletOriginalForm hS hd hb).model.operator (u.domainValue t)) := by
    filter_upwards [Lp.coeFn_add (ε • u.toPeriodicGraph.val.2.1) u.toPeriodicGraph.val.2.2,
      Lp.coeFn_smul ε u.toPeriodicGraph.val.2.1,u.derivative_L2.coeFn_toLp,u.operator_L2.coeFn_toLp]
      with t ha hs hdtime hop
    rw [ha]
    simp only [Pi.add_apply,hs,Pi.smul_apply]
    change u.toPeriodicGraph.val.2.1 t=u.derivative t at hdtime
    change u.toPeriodicGraph.val.2.2 t=(boundedDirichletOriginalForm hS hd hb).model.operator (u.domainValue t) at hop
    rw [hdtime,hop]
  have ho : (BoundedMultiplier.cutoff W hW).continuousLinearMap.compLp (g.pathL2 u.toPeriodicGraph.val.1)
      =ᵐ[g.timeMeasure] (fun t => (BoundedMultiplier.cutoff W hW).map (u.value t)) := by
    filter_upwards [(BoundedMultiplier.cutoff W hW).continuousLinearMap.coeFn_compLp
      (g.pathL2 u.toPeriodicGraph.val.1),u.tracePathL2_ae] with t ht hv
    change g.pathL2 u.toPeriodicGraph.val.1 t=u.value t at hv
    rw [ht,hv]
    rfl
  unfold dirichletIntervalHeatRight
  exact congrArg₂ (fun x y : ℝ => x+y) (timeSq_congr_ae g q 0 _ hr) (timeSq_congr_ae g q 3 _ ho)

end Carleman
