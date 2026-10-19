module

public import Carleman.Geometry.CoordinateReflection
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Genuine convolution vanishes on a reflecting plane under local oddness and an even kernel. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution
namespace Carleman
variable {d : ℕ}

theorem coordinateReflection_zero (r : Fin d) (x : SpatialCoordinates d) :
    coordinateReflection r 0 x=coordinateSignFlip r x := by
  change coordinateSignFlip r x+(2*(0:ℝ)) • EuclideanSpace.basisFun (Fin d) ℝ r=_
  simp only [mul_zero,zero_smul,add_zero]

theorem coordinateSignFlip_involutive (r : Fin d) : Function.Involutive (coordinateSignFlip r) := by
  intro x
  ext j
  simp only [coordinateSignFlip_apply]
  split <;> simp_all

theorem coordinateReflection_sub_fixed (r : Fin d) (c : ℝ) {x : SpatialCoordinates d}
    (hx : x r=c) (y : SpatialCoordinates d) :
    x-coordinateReflection r c y=coordinateSignFlip r (x-y) := by
  classical
  ext j
  change x j-coordinateReflection r c y j=coordinateSignFlip r (x-y) j
  rw [coordinateReflection_apply,coordinateSignFlip_apply]
  change x j-(if j=r then 2*c-y j else y j)=if j=r then -(x j-y j) else x j-y j
  by_cases hj : j=r
  · subst j
    simp only [ite_true,hx]
    ring
  · simp only [hj,ite_false]

theorem convolution_zero_of_local_odd (r : Fin d) (c δ : ℝ)
    {κ f : SpatialCoordinates d → ℝ}
    (hκ : ∀ y, κ (coordinateSignFlip r y)=κ y)
    (hsupp : Function.support κ ⊆ Metric.ball 0 δ)
    {x : SpatialCoordinates d} (hx : x r=c)
    (hodd : ∀ᵐ y ∂(volume : Measure (SpatialCoordinates d)), y ∈ Metric.ball x δ →
      f (coordinateReflection r c y)= -f y) :
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] f) x=0 := by
  rw [convolution_eq_swap (μ := (volume : Measure (SpatialCoordinates d)))]
  change (∫ y, κ (x-y)*f y)=0
  have he : (∫ y, κ (x-y)*f y)=∫ y, κ (x-coordinateReflection r c y)*f (coordinateReflection r c y) :=
    ((coordinateReflection_measurePreserving r c).integral_comp
      (coordinateReflection r c).toMeasurableEquiv.measurableEmbedding _).symm
  have hneg : (∫ y, κ (x-coordinateReflection r c y)*f (coordinateReflection r c y))=
      -(∫ y, κ (x-y)*f y) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hodd] with y hy
    rw [coordinateReflection_sub_fixed r c hx,hκ]
    by_cases hk : κ (x-y)=0
    · simp only [hk,zero_mul,neg_zero]
    · have hm : y ∈ Metric.ball x δ := by
        have hh := hsupp (show x-y ∈ Function.support κ from hk)
        simpa only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev] using hh
      rw [hy hm]
      ring
  linarith

end Carleman
