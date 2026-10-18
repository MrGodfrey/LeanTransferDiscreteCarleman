module

public import Carleman.Spatial.CoordinateBoxTrace
public import Carleman.Spatial.SobolevRealization

/-! The face trace of every genuine H¹ jet, its full-gradient bound, and
agreement with the actual face restriction of any continuous representative. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem coordinateBoxFaceTrace_eq_continuous (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hi : a i < b i) (upper : Bool)
    (u v : Lp ℝ 2 (volume.restrict (openCoordinateBox a b)))
    (hw : IsWeakSpatialDerivative (volume.restrict (openCoordinateBox a b))
      (openCoordinateBox a b) (EuclideanSpace.basisFun (Fin (d+1)) ℝ i) u v)
    (F : SpatialCoordinates (d+1) → ℝ) (hF : Continuous F)
    (hu : u =ᵐ[volume.restrict (openCoordinateBox a b)] F) :
    coordinateBoxFaceTrace i a b hi upper u v =ᵐ[
      volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))]
      (fun x => F (WithLp.toLp 2 (i.insertNth (if upper then b i else a i) (fun j => x j)))) := by
  let g := coordinateBoxAxisGrid i a b hi
  have hp := (MeasurePreserving.symm (coordinateBoxChart i (a i)).toMeasurableEquiv
    (coordinateBoxChart_timeMeasure i a b hi)).quasiMeasurePreserving.ae_eq_comp hu
  have hs := coordinateBoxFaceTrace_representatives i a b hi u v hw
  filter_upwards [hs,Measure.ae_ae_of_ae_prod hp] with x hx hpx
  obtain ⟨U,hc,ha,_,h0,hL⟩ := hx
  have hcx : Continuous (fun t : ℝ => F ((coordinateBoxChart i (a i)).symm (x,t))) :=
    hF.comp ((coordinateBoxChart i (a i)).symm.continuous.comp (continuous_const.prodMk continuous_id))
  have he : U =ᵐ[g.timeMeasure] (fun t => F ((coordinateBoxChart i (a i)).symm (x,t))) := by
    apply ha.symm.trans
    change (fun t => u ((coordinateBoxChart i (a i)).symm (x,t))) =ᵐ[g.timeMeasure]
      (fun t => F ((coordinateBoxChart i (a i)).symm (x,t))) at hpx
    simpa only [Function.comp_apply,coordinateBoxChart_symm_apply] using hpx
  have hc' : ContinuousOn U (Icc 0 g.period) := by
    simpa only [g,coordinateBoxAxisGrid_period] using hc
  have eqn := g.continuous_representative_unique hc' hcx.continuousOn he
  cases upper with
  | false =>
    have hz := eqn (show (0:ℝ) ∈ Icc 0 g.period from ⟨le_rfl,g.period_pos.le⟩)
    simpa only [coordinateBoxChart_symm_apply,zero_add,Bool.false_eq_true,ite_false] using h0.trans hz
  | true =>
    have hz := eqn (show g.period ∈ Icc 0 g.period from ⟨g.period_pos.le,le_rfl⟩)
    rw [show g.period=b i-a i from coordinateBoxAxisGrid_period i a b hi] at hz
    simpa only [coordinateBoxChart_symm_apply,sub_add_cancel,ite_true] using hL.trans hz

def weakJetBoxFaceTrace (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i) (upper : Bool)
    (u : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)) :
    Lp ℝ 2 (volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))) :=
  coordinateBoxFaceTrace i a b hi upper (WeakSobolevJet.value u)
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))

theorem weakJetBoxFaceTrace_norm_sq (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (upper : Bool)
    (u : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)) :
    ‖weakJetBoxFaceTrace i a b hi upper u‖^2 ≤
      2/(b i-a i)*‖WeakSobolevJet.value u‖^2+2*(b i-a i)*‖WeakSobolevJet.field 1 u‖^2 := by
  have hn : ‖derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)‖ ≤
      ‖WeakSobolevJet.field 1 u‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [derivativeComponent_ae (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u)] with x hx
    rw [hx]
    exact PiLp.norm_apply_le _ _
  have he := coordinateBoxFaceTrace_norm_sq i a b hi upper (WeakSobolevJet.value u)
    (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
  apply he.trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn)
    (show 0 ≤ (2:ℝ)*(b i-a i) from mul_nonneg (by norm_num) (sub_pos.mpr hi).le))

theorem weakJetBoxFaceTrace_eq_continuous (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hi : a i < b i) (upper : Bool)
    (u : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (F : SpatialCoordinates (d+1) → ℝ) (hF : Continuous F)
    (hu : WeakSobolevJet.value u =ᵐ[volume.restrict (openCoordinateBox a b)] F) :
    weakJetBoxFaceTrace i a b hi upper u =ᵐ[
      volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))]
      (fun x => F (WithLp.toLp 2 (i.insertNth (if upper then b i else a i) (fun j => x j)))) :=
  coordinateBoxFaceTrace_eq_continuous i a b hi upper _ _
    (WeakSobolevJet.field_weak_derivative u (0 : Fin 1) Sym.nil i) F hF hu

end Carleman
