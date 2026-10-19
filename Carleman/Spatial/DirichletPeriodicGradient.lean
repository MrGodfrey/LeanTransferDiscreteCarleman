module

public import Carleman.Continuous.PeriodicEnergyField
public import Carleman.Spatial.SmoothWeakGradientIdentity

/-! The genuine spatial gradient is a continuous Bochner field on the original weak periodic graph. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hd : 0 < d)
  (hb : Bornology.IsBounded S) (g : TimeGrid)

def dirichletPeriodicGradient :
    (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g →L[ℝ]
      Lp (Lp (DerivativeFiber d 1) 2 (volume.restrict S)) 2 g.timeMeasure :=
  ((dirichletGradient S).compLpL 2 g.timeMeasure).comp
    ((boundedDirichletOriginalForm hS hd hb).model.periodicEnergy g)

theorem dirichletPeriodicGradient_ae
    (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g) :
    dirichletPeriodicGradient hS hd hb g p =ᵐ[g.timeMeasure]
      (fun t => dirichletGradient S ((boundedDirichletOriginalForm hS hd hb).model.periodicEnergy g p t)) :=
  (dirichletGradient S).coeFn_compLp _

theorem dirichletPeriodicGradient_smooth_norm
    (p : (boundedDirichletOriginalForm hS hd hb).model.PeriodicGraph g)
    {F : (ℝ × SpatialCoordinates d) → ℝ} (hF : ContDiff ℝ ∞ F)
    (htrace : ∀ t : Icc 0 g.period, p.val.1 t =ᵐ[volume.restrict S] (fun x => F (t,x))) :
    ∀ᵐ t ∂g.timeMeasure,
      (fun x => ‖dirichletPeriodicGradient hS hd hb g p t x‖^2) =ᵐ[volume.restrict S]
        (fun x => ‖gradient (fun y => F (t,y)) x‖^2) := by
  let B := (boundedDirichletOriginalForm hS hd hb).model
  filter_upwards [dirichletPeriodicGradient_ae hS hd hb g p,
    B.periodicEnergy_embed_ae g p,g.pathL2_ae p.val.1,ae_restrict_mem measurableSet_Ioo]
    with t hgrad henergy hpath ht
  let u : WeakSobolevJet d 1 (volume.restrict S) S := SobolevHilbert.toJet (B.periodicEnergy g p t).val
  have hu : WeakSobolevJet.value u=p.val.1 ⟨t,⟨ht.1.le,ht.2.le⟩⟩ := by
    change B.embed (B.periodicEnergy g p t)=_
    rw [henergy,hpath,g.clampPath_on _ t ⟨ht.1.le,ht.2.le⟩]
  have hv : WeakSobolevJet.value u =ᵐ[volume.restrict S] (fun x => F (t,x)) := by
    rw [hu]
    exact htrace ⟨t,⟨ht.1.le,ht.2.le⟩⟩
  rw [hgrad]
  exact WeakSobolevJet.gradient_norm_sq_eq_smooth hS hb u (hF.comp (contDiff_const.prodMk contDiff_id)) hv

end Carleman
