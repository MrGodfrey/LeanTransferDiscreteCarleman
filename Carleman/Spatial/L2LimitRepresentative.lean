module

public import Carleman.Spatial.PairwiseL2Limit
public import Carleman.Spatial.SmoothH2PointBound

/-! A pointwise limit and a strong L² limit of the same actual sequence
represent the same L² class. All participating functions have genuine MemLp. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman

theorem continuousOn_memLp_compact {d : ℕ} {K : Set (SpatialCoordinates d)}
    (hK : IsCompact K) {f : SpatialCoordinates d → ℝ} (hf : ContinuousOn f K) :
    MemLp f 2 (volume.restrict K) :=
  (memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable hK.measurableSet)).mpr
    ((hf.norm.pow 2).integrableOn_compact hK)

theorem l2_limit_ae_eq_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {f g : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (ht : Tendsto (fun n => bochnerL2Norm ν (fun x => F n x-f x)) atTop (𝓝 0))
    (hl : ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 (g x))) : g =ᵐ[ν] f := by
  have hs (n : ℕ) : (∫ x, (F n x-f x)^2 ∂ν)=
      (bochnerL2Norm ν (fun x => F n x-f x))^2 := integral_sq_eq_bochnerL2Norm_sq ((hF n).sub hf)
  have hsq : Tendsto (fun n => ∫ x, (F n x-f x)^2 ∂ν) atTop (𝓝 0) := by
    simpa only [hs,zero_pow (by decide : 2≠0)] using ht.pow 2
  have hl' : ∀ᵐ x ∂ν, Tendsto (fun n => F n x-f x) atTop (𝓝 (g x-f x)) := by
    filter_upwards [hl] with x hx
    exact hx.sub_const (f x)
  have hzero : (∫ x, (g x-f x)^2 ∂ν)=0 := by
    apply le_antisymm _ (integral_nonneg fun x => sq_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    have hb : ∀ᶠ n in atTop, (∫ x, (F n x-f x)^2 ∂ν) ≤ ε :=
      (hsq.eventually (gt_mem_nhds hε)).mono fun _ hn => hn.le
    simpa only [zero_add,Pi.sub_apply] using
      l2_square_bound_of_ae_tendsto (hg.sub hf) (fun n => (hF n).sub hf) hl' hε.le hb
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (g x-f x))
    (hg.sub hf).integrable_sq).mp hzero
  filter_upwards [ha] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

end Carleman
