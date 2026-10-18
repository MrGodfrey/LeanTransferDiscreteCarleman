module

public import Carleman.Section3.ContinuousInterval

/-! The original interval weight and smooth spatial profile supply the bounded
representatives used by the library. Off-interval values are never extra data. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

namespace TimeWeight
variable {T : ℝ} (hT : 0 < T) (q : ℝ → ℝ) (qmax : ℝ)
  (hb : ∀ t ∈ Icc 0 T, 1 ≤ q t ∧ q t ≤ qmax)

def ofInterval : TimeWeight where
  q t := q (Max.max 0 (min t T))
  max := qmax
  lower _t := (hb _ ⟨le_max_left _ _,max_le hT.le (min_le_right _ _)⟩).1
  upper _t := (hb _ ⟨le_max_left _ _,max_le hT.le (min_le_right _ _)⟩).2

theorem ofInterval_on (t : ℝ) (ht : t ∈ Icc 0 T) :
    (ofInterval hT q qmax hb).q t = q t := by
  simp only [ofInterval,min_eq_left ht.2,max_eq_right ht.1]

/-- Original C² and periodic endpoint hypotheses produce the needed weak
coefficient regularity for any encoding of the same time interval. -/
def ofInterval_regularity (g : TimeGrid) (hg : g.period = T) {β : ℝ}
    (hβ : 0 < β) (hc : ContDiffOn ℝ 2 q (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, |derivWithin q (Icc 0 T) t| ≤ β*q t^2)
    (he : q 0 = q T) : TimeWeightRegularity (ofInterval hT q qmax hb) g β where
  beta_pos := hβ
  derivative := derivWithin q (Icc 0 T)
  hasDeriv := by
    intro t ht
    rw [hg] at ht ⊢
    exact ((hc.differentiableOn (by norm_num) t ht).hasDerivWithinAt).congr_of_mem
      (fun x hx => ofInterval_on hT q qmax hb x hx) ht
  derivative_bound := by
    intro t ht
    rw [hg] at ht
    rw [ofInterval_on hT q qmax hb t ht]
    exact hd t ht
  endpoint := by
    rw [hg,ofInterval_on hT q qmax hb 0 ⟨le_rfl,hT.le⟩,
      ofInterval_on hT q qmax hb T ⟨hT.le,le_rfl⟩,he]
end TimeWeight

/-- Compactness of the original bounded domain supplies the profile bound;
no independent bounded-measurable-profile assumption is needed. -/
theorem exists_profile_of_smooth {d : ℕ} {S : Set (SpatialCoordinates d)}
    (hS : IsOpen S) (hbounded : Bornology.IsBounded S) (f : SpatialCoordinates d → ℝ)
    (hf : SmoothOnClosure f S) :
    ∃ ρ : SpatialProfile (volume.restrict S), ρ.value = f := by
  obtain ⟨C,hC⟩ := hbounded.isCompact_closure.exists_bound_of_continuousOn hf.1
  refine ⟨⟨f,(hf.1.mono subset_closure).aestronglyMeasurable hS.measurableSet,
    max 0 C,le_max_left _ _,?_⟩,rfl⟩
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  have hh : |f x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x (subset_closure hx)
  exact hh.trans (le_max_right _ _)
end Carleman
