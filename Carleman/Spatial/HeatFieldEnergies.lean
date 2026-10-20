module
public import Carleman.Spatial.DirichletHeatFields
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

def heatFieldsLeft (g : TimeGrid) (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight)
    (p : DirichletHeatFields S g) : ℝ :=
  timeSq g w.q 3 (fun t => (ρ.multiplier w 0 t).seminorm) p.1+
    timeSq g w.q 1 (fun t => (ρ.multiplier w 0 t).seminorm) p.2.2.2

def heatFieldsRight (g : TimeGrid) (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight)
    (ε : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (p : DirichletHeatFields S g) : ℝ :=
  timeSq g w.q 0 (fun t => (ρ.multiplier w 0 t).seminorm) (ε • p.2.1+p.2.2.1)+
    timeSq g w.q 3 (fun t => (ρ.multiplier w 0 t).seminorm)
      ((BoundedMultiplier.cutoff W hW).continuousLinearMap.compLp p.1)

theorem continuous_heatFieldsLeft (g : TimeGrid) (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) : Continuous (heatFieldsLeft g ρ w) := by
  exact ((ρ.continuous_timeSq g w 0 hq 3).comp continuous_fst).add
    ((ρ.continuous_timeSq g w 0 hq 1).comp continuous_snd.snd.snd)

theorem continuous_heatFieldsRight (g : TimeGrid) (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight)
    (hq : AEStronglyMeasurable w.q g.timeMeasure) (ε : ℝ)
    (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W) :
    Continuous (heatFieldsRight g ρ w ε W hW) := by
  let o : DirichletHeatFields S g →L[ℝ] Lp (Lp ℝ 2 (volume.restrict S)) 2 g.timeMeasure :=
    ((BoundedMultiplier.cutoff W hW).continuousLinearMap.compLpL 2 g.timeMeasure).comp
      (ContinuousLinearMap.fst ℝ _ _)
  exact ((ρ.continuous_timeSq g w 0 hq 0).comp
    ((continuous_snd.fst.const_smul ε).add continuous_snd.snd.fst)).add
    ((ρ.continuous_timeSq g w 0 hq 3).comp o.continuous)

theorem heatFieldsLeft_dirichlet (hS : IsOpen S) (hd : 0<d) (hb : Bornology.IsBounded S)
    (g : TimeGrid) (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight)
    (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) :
    heatFieldsLeft g ρ w (dirichletHeatFields hS hd hb g p)=dirichletHeatLeft hS hd hb g ρ w p := rfl

theorem heatFieldsRight_dirichlet (hS : IsOpen S) (hd : 0<d) (hb : Bornology.IsBounded S)
    (g : TimeGrid) (ρ : SpatialProfile (volume.restrict S)) (w : TimeWeight)
    (ε : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) :
    heatFieldsRight g ρ w ε W hW (dirichletHeatFields hS hd hb g p)=dirichletHeatRight hS hd hb g ρ w ε W hW p := rfl

theorem heatFieldsLeft_subdomain (hT : MeasurableSet T) (hTS : T⊆S)
    (g : TimeGrid) (ρS : SpatialProfile (volume.restrict S)) (ρT : SpatialProfile (volume.restrict T))
    (hρ : ρS.value=ᵐ[volume.restrict T] ρT.value) (w : TimeWeight)
    (p : DirichletHeatFields T g) :
    heatFieldsLeft g ρS w (subdomainHeatFields S T g p)=heatFieldsLeft g ρT w p := by
  simp only [heatFieldsLeft,subdomainHeatFields_apply]
  rw [timeSq_subdomainZeroExtend hT hTS g ρS ρT hρ,
    timeSq_subdomainZeroExtend hT hTS g ρS ρT hρ]

theorem heatFieldsRight_subdomain (hT : MeasurableSet T) (hTS : T⊆S)
    (g : TimeGrid) (ρS : SpatialProfile (volume.restrict S)) (ρT : SpatialProfile (volume.restrict T))
    (hρ : ρS.value=ᵐ[volume.restrict T] ρT.value) (w : TimeWeight)
    (ε : ℝ) (W : Set (SpatialCoordinates d)) (hW : MeasurableSet W)
    (p : DirichletHeatFields T g) :
    heatFieldsRight g ρS w ε W hW (subdomainHeatFields S T g p)=heatFieldsRight g ρT w ε W hW p := by
  have hr : ε • (subdomainZeroExtendCLM S T).compLp p.2.1+
      (subdomainZeroExtendCLM S T).compLp p.2.2.1=
      (subdomainZeroExtendCLM S T).compLp (ε • p.2.1+p.2.2.1) := by
    change ε • (subdomainZeroExtendCLM S T).compLpL 2 g.timeMeasure p.2.1+
      (subdomainZeroExtendCLM S T).compLpL 2 g.timeMeasure p.2.2.1=
      (subdomainZeroExtendCLM S T).compLpL 2 g.timeMeasure (ε • p.2.1+p.2.2.1)
    simp only [map_add,map_smul]
  simp only [heatFieldsRight,subdomainHeatFields_apply]
  rw [hr,subdomainTimeZeroExtend_cutoff hT g W hW]
  exact congrArg₂ (·+·)
    (timeSq_subdomainZeroExtend (E := ℝ) hT hTS g ρS ρT hρ w 0 0 (ε • p.2.1+p.2.2.1))
    (timeSq_subdomainZeroExtend (E := ℝ) hT hTS g ρS ρT hρ w 0 3
      (((BoundedMultiplier.cutoff (ν := volume.restrict T) W hW).continuousLinearMap (E := ℝ)).compLp p.1))

end Carleman
