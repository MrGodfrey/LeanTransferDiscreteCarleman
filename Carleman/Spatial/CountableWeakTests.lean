module

public import Carleman.Continuous.WeakIntervalRepresentative
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! A single null set suffices for all weak tests: use the separability of
the actual L² test/derivative pairs and continuity of each slice pairing. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem ae_forall_continuous_zero_on {X Z : Type*} [MeasurableSpace X]
    [TopologicalSpace Z] {μ : Measure X} (B : Set Z) [TopologicalSpace.SeparableSpace B]
    (f : X → Z → ℝ) (hf : ∀ x, Continuous (f x))
    (hz : ∀ z ∈ B, ∀ᵐ x ∂μ, f x z=0) :
    ∀ᵐ x ∂μ, ∀ z ∈ B, f x z=0 := by
  obtain ⟨D,hD,hsub,hdense⟩ := TopologicalSpace.exists_countable_dense_subset B
  have hcount : ∀ᵐ x ∂μ, ∀ z ∈ D, f x z=0 := (ae_ball_iff hD).mpr (fun z hzD => hz z (hsub hzD))
  filter_upwards [hcount] with x hx
  have hclosed : IsClosed {z | f x z=0} := isClosed_eq (hf x) continuous_const
  exact fun z hzB => closure_minimal hx hclosed (hdense hzB)

theorem scalar_weak_interval_iff (g : TimeGrid) (u v : Lp ℝ 2 g.timeMeasure) :
    IsWeakSpatialDerivative g.timeMeasure (Ioo 0 g.period) 1 u v ↔ HasWeakTimeDerivative g u v := by
  rw [IsWeakSpatialDerivative.iff_integral]
  constructor
  · intro h φ hs hc hsup
    exact h ⟨φ,hs,hc,hsup⟩
  · intro h φ
    exact h φ.value φ.smooth φ.compact φ.support

theorem ae_weak_interval_of_ae_tests {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (g : TimeGrid) (u v : X → Lp ℝ 2 g.timeMeasure)
    (h : ∀ φ : SpatialTest (Ioo 0 g.period), ∀ᵐ x ∂μ,
      inner ℝ (u x) (φ.derivativeLp g.timeMeasure 1)= -inner ℝ (v x) (φ.toLp g.timeMeasure)) :
    ∀ᵐ x ∂μ, HasWeakTimeDerivative g (u x) (v x) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let B : Set (Lp ℝ 2 g.timeMeasure × Lp ℝ 2 g.timeMeasure) :=
    range (fun φ : SpatialTest (Ioo 0 g.period) => (φ.derivativeLp g.timeMeasure 1,φ.toLp g.timeMeasure))
  have he := ae_forall_continuous_zero_on B
    (fun x p => inner ℝ (u x) p.1+inner ℝ (v x) p.2)
    (fun _ => (continuous_const.inner continuous_fst).add (continuous_const.inner continuous_snd))
    (by
      rintro _ ⟨φ,rfl⟩
      filter_upwards [h φ] with x hx
      rw [hx,neg_add_cancel])
  filter_upwards [he] with x hx
  apply (scalar_weak_interval_iff g (u x) (v x)).mp
  intro φ
  exact eq_neg_of_add_eq_zero_left (hx _ ⟨φ,rfl⟩)

end Carleman
