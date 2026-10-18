module

public import Carleman.Weights.SpatialDerivatives
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Actual spatial comparisons for both signs of the allowed exponential.
The fixed profile supplies the Lipschitz constant; the power q^tau cancels. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniqueDiffOn_closure_open_convex {S : Set E} (hS : IsOpen S) (hc : Convex ℝ S) :
    UniqueDiffOn ℝ (closure S) := by
  by_cases hn : S.Nonempty
  · apply uniqueDiffOn_convex hc.closure
    exact hn.mono (by simpa only [hS.interior_eq] using interior_mono (subset_closure : S ⊆ closure S))
  · rw [Set.not_nonempty_iff_eq_empty.mp hn,closure_empty]
    exact fun _ hx => False.elim hx

theorem smooth_profile_lipschitz {S : Set E} {ρ : E → ℝ}
    (hS : IsOpen S) (hc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hρ : ContDiffOn ℝ 1 ρ (closure S)) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x ∈ closure S, ∀ y ∈ closure S,
      |ρ x-ρ y| ≤ L*dist x y := by
  have hu := uniqueDiffOn_closure_open_convex hS hc
  obtain ⟨L,hL,hb⟩ := exists_profile_derivative_bound hρ hu hcompact
  refine ⟨L,hL,?_⟩
  intro x hx y hy
  have hd : ∀ z ∈ closure S, ‖fderivWithin ℝ ρ (closure S) z‖ ≤ L := by
    intro z hz
    simpa only [norm_iteratedFDerivWithin_one ρ (hu z hz)] using hb 1 le_rfl z hz
  simpa only [Real.norm_eq_abs,dist_eq_norm] using
    hc.closure.norm_image_sub_le_of_norm_fderivWithin_le (hρ.differentiableOn (by norm_num)) hd hy hx

theorem allowedWeight_spatial_ratio (q τ η a b : ℝ) (hq : 0 < q) :
    (q^τ*Real.exp (η*a*q))/(q^τ*Real.exp (η*b*q)) = Real.exp (η*(a-b)*q) := by
  rw [mul_div_mul_left _ _ (ne_of_gt (Real.rpow_pos_of_pos hq τ)),← Real.exp_sub]
  congr 1
  ring

theorem allowedWeight_spatial_comparison {q η a b D : ℝ} (hq : 0 < q)
    (hη : |η|=1) (hab : |a-b| ≤ D) (τ : ℝ) :
    Real.exp (-D*q) ≤ (q^τ*Real.exp (η*a*q))/(q^τ*Real.exp (η*b*q)) ∧
      (q^τ*Real.exp (η*a*q))/(q^τ*Real.exp (η*b*q)) ≤ Real.exp (D*q) := by
  rw [allowedWeight_spatial_ratio q τ η a b hq]
  have hh : |η*(a-b)| ≤ D := by simpa only [abs_mul,hη,one_mul] using hab
  constructor
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (abs_le.mp hh).1 hq.le)
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (abs_le.mp hh).2 hq.le)

end Carleman

namespace Carleman.SpatialProfile
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

def scaled (ρ : SpatialProfile ν) (η : ℝ) : SpatialProfile ν where
  value x := η*ρ.value x
  measurable := ρ.measurable.const_mul η
  bound := |η| * ρ.bound
  bound_nonneg := mul_nonneg (abs_nonneg _) ρ.bound_nonneg
  bounded := by
    filter_upwards [ρ.bounded] with x hx
    simpa only [abs_mul] using mul_le_mul_of_nonneg_left hx (abs_nonneg η)

theorem scaled_multiplier_value (ρ : SpatialProfile ν) (η : ℝ) (w : TimeWeight) (τ t : ℝ) (x : Ω) :
    ((ρ.scaled η).multiplier w τ t).value x = w.q t^τ*Real.exp (η*ρ.value x*w.q t) := rfl

theorem scaled_one (ρ : SpatialProfile ν) : ρ.scaled 1=ρ := by
  cases ρ
  simp only [scaled,one_mul,abs_one]

theorem scaled_neg_one (ρ : SpatialProfile ν) : ρ.scaled (-1)=ρ.neg := by
  cases ρ
  simp only [scaled,neg,neg_one_mul,abs_neg,abs_one,one_mul,Pi.neg_def]

theorem scaled_multiplier_pos (ρ : SpatialProfile ν) (η : ℝ) (w : TimeWeight) (τ t : ℝ) (x : Ω) :
    0 < ((ρ.scaled η).multiplier w τ t).value x :=
  mul_pos (Real.rpow_pos_of_pos (w.pos t) τ) (Real.exp_pos _)

theorem scaled_multiplier_spatial_le (ρ : SpatialProfile ν) (η : ℝ) (hη : |η|=1)
    (w : TimeWeight) (τ t : ℝ) {x y : Ω} {D : ℝ} (hxy : |ρ.value x-ρ.value y| ≤ D) :
    ((ρ.scaled η).multiplier w τ t).value x ≤
      Real.exp (D*w.q t)*((ρ.scaled η).multiplier w τ t).value y := by
  have hh := (allowedWeight_spatial_comparison (w.pos t) hη hxy τ).2
  exact (div_le_iff₀ (ρ.scaled_multiplier_pos η w τ t y)).mp hh

end Carleman.SpatialProfile
