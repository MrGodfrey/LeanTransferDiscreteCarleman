module

public import Carleman.Continuous.ClassicalWeakTime
public import Carleman.Continuous.WeakTimeSpace
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! Compactly supported primitives of zero-mean time tests. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman

theorem compact_subset_period_bounds {g : TimeGrid} {K : Set ℝ}
    (hK : IsCompact K) (hsub : K ⊆ Ioo 0 g.period) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < g.period ∧ K ⊆ Ioo a b := by
  let L := K ∪ {g.period / 2}
  have hc : IsCompact L := hK.union (isCompact_singleton)
  have hn : L.Nonempty := ⟨g.period / 2, Or.inr rfl⟩
  have hs : L ⊆ Ioo 0 g.period := by
    intro x hx
    rcases hx with hx | hx
    · exact hsub hx
    · have hx' : x = g.period / 2 := hx
      subst x
      constructor <;> linarith [g.period_pos]
  obtain ⟨c, hcmin⟩ := hc.exists_isLeast hn
  obtain ⟨d, hdmax⟩ := hc.exists_isGreatest hn
  refine ⟨c/2, (d+g.period)/2, ?_, ?_, ?_, ?_⟩
  · linarith [(hs hcmin.1).1]
  · have := hcmin.2 hdmax.1
    linarith [(hs hcmin.1).1, (hs hdmax.1).2]
  · linarith [(hs hdmax.1).2]
  · intro x hx
    have hcx := hcmin.2 (Or.inl hx)
    have hxd := hdmax.2 (Or.inl hx)
    constructor <;> linarith [(hs hcmin.1).1, (hs hdmax.1).2]

/-- Every smooth zero-mean test has a smooth compact primitive in the same open period. -/
theorem exists_time_test_primitive {g : TimeGrid} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo 0 g.period) (hi : ∫ t, f t = 0) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ Ioo 0 g.period ∧ deriv F = f := by
  obtain ⟨a, b, ha, hab, hb, hsup⟩ := compact_subset_period_bounds hc hs
  let F : ℝ → ℝ := fun x => ∫ t in a..x, f t
  have hd (x : ℝ) : HasDerivAt F (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable _ _)
      hf.continuous.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuous.continuousAt
  have hder : deriv F = f := funext fun x => (hd x).deriv
  have hsm : ContDiff ℝ ∞ F := contDiff_infty_iff_deriv.mpr
    ⟨fun x => (hd x).differentiableAt, hder ▸ hf⟩
  have hzero (x : ℝ) (hx : x ∉ Icc a b) : F x = 0 := by
    rcases lt_or_ge x a with hxa | hax
    · change (∫ t in a..x, f t) = 0
      rw [intervalIntegral.integral_symm]
      suffices (∫ t in x..a, f t) = 0 by rw [this, neg_zero]
      calc
        (∫ t in x..a, f t) = ∫ t in x..a, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hxa.le] at ht
          apply image_eq_zero_of_notMem_tsupport
          intro ht'
          exact (not_lt_of_ge ht.2) (hsup ht').1
        _ = 0 := by simp
    · have hbx : b < x := lt_of_not_ge (fun hxb => hx ⟨hax, hxb⟩)
      change (∫ t in a..x, f t) = 0
      rw [intervalIntegral.integral_eq_integral_of_support_subset, hi]
      intro t ht
      have h := hsup (subset_tsupport f ht)
      exact ⟨h.1, h.2.le.trans hbx.le⟩
  have hsF : tsupport F ⊆ Icc a b :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hzero x hn)) isClosed_Icc
  refine ⟨F, hsm, isCompact_Icc.of_isClosed_subset isClosed_closure hsF, ?_, hder⟩
  intro x hx
  have h := hsF hx
  exact ⟨ha.trans_le h.1, h.2.trans_lt hb⟩

/-- An actual normalized smooth scalar test strictly inside the period. -/
theorem exists_time_test_integral_one (g : TimeGrid) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo 0 g.period ∧ (∫ t, ψ t) = 1 := by
  let f : ContDiffBump (g.period / 2) :=
    ⟨g.period / 8, g.period / 4, by linarith [g.period_pos], by linarith [g.period_pos]⟩
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, ?_, f.integral_normed⟩
  rw [f.tsupport_normed_eq, Real.closedBall_eq_Icc]
  intro x hx
  change g.period / 2 - g.period / 4 ≤ x ∧ x ≤ g.period / 2 + g.period / 4 at hx
  constructor <;> linarith [g.period_pos]

end Carleman
