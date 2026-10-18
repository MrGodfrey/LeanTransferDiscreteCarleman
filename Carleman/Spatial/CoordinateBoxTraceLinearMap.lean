module

public import Carleman.Spatial.CoordinateBoxSobolevTrace
public import Carleman.Spatial.FaceTraceLinearity

/-! Linear maps for the actual coordinate-box transports and face traces. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def coordinateBoxTransportLinearMap (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i) :
    Lp ℝ 2 (volume.restrict (openCoordinateBox a b)) →ₗ[ℝ]
      Lp ℝ 2 ((volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))).prod
        (coordinateBoxAxisGrid i a b hi).timeMeasure) :=
  Lp.compMeasurePreservingₗ ℝ (coordinateBoxChart i (a i)).symm
    (MeasurePreserving.symm (coordinateBoxChart i (a i)).toMeasurableEquiv
      (coordinateBoxChart_timeMeasure i a b hi))

theorem coordinateBoxTransportLinearMap_apply (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) :
    coordinateBoxTransportLinearMap i a b hi u=coordinateBoxLp i a b hi u := rfl

def coordinateBoxFaceLinearMap (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i) (upper : Bool) :
    (Lp ℝ 2 (volume.restrict (openCoordinateBox a b)) ×
      Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))) :=
  let g := coordinateBoxAxisGrid i a b hi
  let L := coordinateBoxTransportLinearMap i a b hi
  (fiberEndpointLinearMap g (if upper then ⟨0,le_rfl,g.period_pos.le⟩
    else ⟨g.period,g.period_pos.le,le_rfl⟩)).comp (L.prodMap L)

theorem coordinateBoxFaceLinearMap_apply (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (upper : Bool) (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) :
    coordinateBoxFaceLinearMap i a b hi upper (u,v)=coordinateBoxFaceTrace i a b hi upper u v := rfl

def weakJetBoxFaceLinearMap (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i) (upper : Bool) :
    WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))) :=
  (coordinateBoxFaceLinearMap i a b hi upper).comp
    (WeakSobolevJet.value.prod ((derivativeComponent (Sym.cons i Sym.nil)).comp (WeakSobolevJet.field 1)))

theorem weakJetBoxFaceLinearMap_apply (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (upper : Bool)
    (u : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)) :
    weakJetBoxFaceLinearMap i a b hi upper u=weakJetBoxFaceTrace i a b hi upper u := rfl

end Carleman
