module

public import Carleman.Geometry.CoordinateBoxChart
public import Carleman.Spatial.ProductFaceTrace

/-! Genuine face traces on the original Euclidean box. The source may be any
L² function with its full weak coordinate derivative; no smooth representative
or separate slice condition is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def coordinateBoxAxisGrid (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i) : TimeGrid :=
  ⟨1,by decide,b i-a i,sub_pos.mpr hi⟩

theorem coordinateBoxAxisGrid_period (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i) :
    (coordinateBoxAxisGrid i a b hi).period=b i-a i := by
  simp [coordinateBoxAxisGrid,TimeGrid.period]

theorem coordinateBoxChart_timeMeasure (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i) :
    MeasurePreserving (coordinateBoxChart i (a i)) (volume.restrict (openCoordinateBox a b))
      ((volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))).prod
        (coordinateBoxAxisGrid i a b hi).timeMeasure) := by
  simpa only [TimeGrid.timeMeasure,coordinateBoxAxisGrid_period] using coordinateBoxChart_restrict i a b

def coordinateBoxLp (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i) :
    Lp ℝ 2 (volume.restrict (openCoordinateBox a b)) →+
      Lp ℝ 2 ((volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))).prod
        (coordinateBoxAxisGrid i a b hi).timeMeasure) :=
  affineTransportLp (coordinateSplit i) (0,-a i) (coordinateBoxChart_timeMeasure i a b hi)

theorem coordinateBoxLp_norm (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) :
    ‖coordinateBoxLp i a b hi u‖=‖u‖ := affineTransportLp_norm _ _ _ _

theorem coordinateBoxLp_ae (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (u : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) :
    coordinateBoxLp i a b hi u =ᵐ[
      (volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))).prod
        (coordinateBoxAxisGrid i a b hi).timeMeasure]
      (fun x => u (WithLp.toLp 2 (i.insertNth (x.2+a i) (fun j => x.1 j)))) := by
  have h := affineTransportLp_ae (coordinateSplit i) (0,-a i) (coordinateBoxChart_timeMeasure i a b hi) u
  change coordinateBoxLp i a b hi u =ᵐ[_] u ∘ (coordinateBoxChart i (a i)).symm at h
  filter_upwards [h] with x hx
  simpa only [Function.comp_apply,coordinateBoxChart_symm_apply] using hx

theorem coordinateBox_weak_transport (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox a b)))
    (hw : IsWeakSpatialDerivative (volume.restrict (openCoordinateBox a b))
      (openCoordinateBox a b) (EuclideanSpace.basisFun (Fin (d+1)) ℝ i) u v) :
    IsWeakSpatialDerivative
      ((volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))).prod
        (coordinateBoxAxisGrid i a b hi).timeMeasure)
      (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove) ×ˢ Ioo 0 (coordinateBoxAxisGrid i a b hi).period)
      (0,1) (coordinateBoxLp i a b hi u) (coordinateBoxLp i a b hi v) := by
  have hST : (coordinateBoxChart i (a i)) ⁻¹'
      (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove) ×ˢ
        Ioo 0 (coordinateBoxAxisGrid i a b hi).period) ⊆ openCoordinateBox a b := by
    rw [coordinateBoxAxisGrid_period,coordinateBoxChart_preimage]
  have h := hw.affine_transport (coordinateSplit i) (0,-a i)
    (coordinateBoxChart_timeMeasure i a b hi) hST
  rw [coordinateSplit_basis] at h
  exact h

def coordinateBoxFaceTrace (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (upper : Bool) (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) :
    Lp ℝ 2 (volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))) :=
  let g := coordinateBoxAxisGrid i a b hi
  fiberEndpointLp g (if upper then ⟨0,le_rfl,g.period_pos.le⟩ else ⟨g.period,g.period_pos.le,le_rfl⟩)
    (coordinateBoxLp i a b hi u) (coordinateBoxLp i a b hi v)

theorem coordinateBoxFaceTrace_norm_sq (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (upper : Bool) (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) :
    ‖coordinateBoxFaceTrace i a b hi upper u v‖^2 ≤
      2/(b i-a i)*‖u‖^2+2*(b i-a i)*‖v‖^2 := by
  have h := fiberEndpointLp_norm_sq (coordinateBoxAxisGrid i a b hi)
    (if upper then ⟨0,le_rfl,(coordinateBoxAxisGrid i a b hi).period_pos.le⟩
      else ⟨_,(coordinateBoxAxisGrid i a b hi).period_pos.le,le_rfl⟩)
    (coordinateBoxLp i a b hi u) (coordinateBoxLp i a b hi v)
  change ‖coordinateBoxFaceTrace i a b hi upper u v‖^2 ≤ _ at h
  simpa only [coordinateBoxAxisGrid_period,coordinateBoxLp_norm] using h

theorem coordinateBoxFaceTrace_representatives (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox a b)))
    (hw : IsWeakSpatialDerivative (volume.restrict (openCoordinateBox a b))
      (openCoordinateBox a b) (EuclideanSpace.basisFun (Fin (d+1)) ℝ i) u v) :
    ∀ᵐ x ∂volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove)),
      ∃ U : ℝ → ℝ, ContinuousOn U (Icc 0 (b i-a i)) ∧
        ((fun t => u (WithLp.toLp 2 (i.insertNth (t+a i) (fun j => x j))))
          =ᵐ[(coordinateBoxAxisGrid i a b hi).timeMeasure] U) ∧
        HasWeakTimeDerivative (coordinateBoxAxisGrid i a b hi) U
          (fun t => v (WithLp.toLp 2 (i.insertNth (t+a i) (fun j => x j)))) ∧
        coordinateBoxFaceTrace i a b hi false u v x=U 0 ∧
        coordinateBoxFaceTrace i a b hi true u v x=U (b i-a i) := by
  have h := product_weak_face_trace_representatives
    (openCoordinateBox_isOpen (a ∘ i.succAbove) (b ∘ i.succAbove))
    (coordinateBoxAxisGrid i a b hi) (coordinateBoxLp i a b hi u) (coordinateBoxLp i a b hi v)
    (coordinateBox_weak_transport i a b hi u v hw)
  filter_upwards [h,Measure.ae_ae_of_ae_prod (coordinateBoxLp_ae i a b hi u),
    Measure.ae_ae_of_ae_prod (coordinateBoxLp_ae i a b hi v)] with x hx hu hv
  obtain ⟨U,hc,ha,hd,h0,hL⟩ := hx
  have hu' : (fun t => coordinateBoxLp i a b hi u (x,t)) =ᵐ[(coordinateBoxAxisGrid i a b hi).timeMeasure]
      (fun t => u (WithLp.toLp 2 (i.insertNth (t+a i) (fun j => x j)))) := hu
  refine ⟨U,?_,hu'.symm.trans ha,hd.congr_derivative hv,?_,?_⟩
  · simpa only [coordinateBoxAxisGrid_period] using hc
  · exact h0
  · change coordinateBoxFaceTrace i a b hi true u v x = _ at hL
    simpa only [coordinateBoxAxisGrid_period] using hL

end Carleman
