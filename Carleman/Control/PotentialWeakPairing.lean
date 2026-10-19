module

public import Carleman.Control.PotentialTestConsistency
public import Carleman.Spatial.WeakProduct

/-! The genuine potential term passes to weak state limits against consistent bounded tests. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace Carleman

theorem hilbert_weak_strong_pairing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : ℕ → H) (y z : H) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ w : H, Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ y w)))
    (hstrong : Tendsto v atTop (𝓝 z)) :
    Tendsto (fun n => inner ℝ (u n) (v n)) atTop (𝓝 (inner ℝ y z)) := by
  have hmajor : Tendsto (fun n => C*‖v n-z‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := C)).mul (tendsto_iff_norm_sub_tendsto_zero.mp hstrong)
  have he : Tendsto (fun n => inner ℝ (u n) (v n-z)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hmajor
    intro n
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _))
  have hs := he.add (hweak z)
  simpa only [inner_sub_right,sub_add_cancel,zero_add] using hs

theorem potential_weak_pairing_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    (a : ℕ → BoundedMultiplier ν) (b φ : BoundedMultiplier ν)
    {M C : ℝ} (ha : ∀ n, (a n).bound ≤ M)
    (hb : Tendsto (fun n => (a n).toL2) atTop (𝓝 b.toL2))
    (u v : ℕ → Lp ℝ 2 ν) (y : Lp ℝ 2 ν) (hu : ∀ n, ‖u n‖ ≤ C)
    (hweak : ∀ w : Lp ℝ 2 ν,
      Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ y w)))
    (hv : Tendsto v atTop (𝓝 φ.toL2)) :
    Tendsto (fun n => inner ℝ ((a n).map (u n)) (v n)) atTop (𝓝 (inner ℝ (b.map y) φ.toL2)) := by
  simp_rw [BoundedMultiplier.inner_map_left]
  exact hilbert_weak_strong_pairing u (fun n => (a n).map (v n)) y (b.map φ.toL2) hu hweak
    (BoundedMultiplier.test_product_strong_convergence a b φ ha hb v hv)

end Carleman
