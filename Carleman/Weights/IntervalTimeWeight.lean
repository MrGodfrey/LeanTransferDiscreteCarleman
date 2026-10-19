module

public import Carleman.Continuous.TimeInterval
public import Carleman.Transfer.Weights
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Every original positive continuous interval weight has a bounded representative preserving both within derivatives. -/
@[expose] public noncomputable section
open Set
namespace Carleman

theorem exists_timeWeight_eqOn_interval (g : TimeGrid) {q : ℝ → ℝ}
    (hq : ContinuousOn q (Icc 0 g.period)) (hlo : ∀ t ∈ Icc 0 g.period, 1 ≤ q t) :
    ∃ w : TimeWeight, Continuous w.q ∧ EqOn w.q q (Icc 0 g.period) := by
  let Q : g.TracePath (H := ℝ) :=
    ⟨(Icc 0 g.period).domRestrict q,continuousOn_iff_continuous_domRestrict.mp hq⟩
  let V := g.clampPath Q
  let w : TimeWeight :=
    { q := V
      max := ‖V‖
      lower := fun t => hlo _ (projIcc 0 g.period g.period_pos.le t).property
      upper := fun t => (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using V.norm_coe_le_norm t) }
  refine ⟨w,V.continuous,?_⟩
  intro t ht
  exact g.clampPath_on Q t ht

theorem eqOn_interval_within_derivatives {f q : ℝ → ℝ} {S : Set ℝ} (he : EqOn f q S) :
    ∀ t ∈ S, f t=q t ∧ derivWithin f S t=derivWithin q S t ∧
      derivWithin (derivWithin f S) S t=derivWithin (derivWithin q S) S t := by
  have hd : EqOn (derivWithin f S) (derivWithin q S) S :=
    fun t ht => derivWithin_congr he (he ht)
  exact fun t ht => ⟨he ht,hd ht,derivWithin_congr hd (hd ht)⟩

end Carleman
