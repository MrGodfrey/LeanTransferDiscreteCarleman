module

public import Carleman.Spatial.ConvexWeakPoincare

/-! On an actual bounded open convex domain, vanishing full weak gradient
forces a scalar L² state to equal one constant almost everywhere. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem weak_zero_gradient_ae_constant (hS : IsOpen S) (hc : Convex ℝ S)
    (hb : Bornology.IsBounded S) (u : Lp ℝ 2 (volume.restrict S))
    (hu : ∀ i : Fin d, IsWeakSpatialDerivative (volume.restrict S) S
      (EuclideanSpace.basisFun (Fin d) ℝ i) u 0) :
    ∃ c : ℝ, u =ᵐ[volume.restrict S] (fun _ => c) := by
  rcases eq_empty_or_nonempty S with he | hne
  · refine ⟨0,?_⟩
    simp only [he,Measure.restrict_empty,ae_zero,Filter.EventuallyEq,Filter.eventually_bot]
  let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hb.measure_lt_top (μ := volume)⟩
  have hvol : 0 < volume.real S := ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior volume (hS.interior_eq.symm ▸ hne)).ne'
    (hb.measure_lt_top (μ := volume)).ne
  let c := (∫ x in S, u x)/volume.real S
  have hm : MemLp (fun x => u x-c) 2 (volume.restrict S) := (Lp.memLp u).sub (memLp_const c)
  have hp := convex_weak_mean_poincare hS hc hb hvol u (fun _ => 0) hu
    Metric.diam_nonneg (fun _ hx _ hy => Metric.dist_le_diam_of_mem hb hx hy)
  have hi : (∫ x in S, (u x-c)^2)=0 := by
    apply le_antisymm _ (integral_nonneg fun x => sq_nonneg _)
    simpa only [norm_zero,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,mul_zero] using hp
  refine ⟨c,?_⟩
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (u x-c)) hm.integrable_sq).mp hi
  filter_upwards [ha] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

end Carleman
