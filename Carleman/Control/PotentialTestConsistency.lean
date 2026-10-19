module

public import Carleman.Control.TimePotentialStrongConvergence

/-! Actual multiplication of approximating tests by the original bounded potentials. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace Carleman.BoundedMultiplier
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]

theorem map_toL2_comm (b φ : BoundedMultiplier ν) : b.map φ.toL2=φ.map b.toL2 := by
  apply Lp.ext
  filter_upwards [b.map_ae φ.toL2,φ.map_ae b.toL2,b.toL2_ae,φ.toL2_ae] with x hb hφ hbx hφx
  rw [hb,hφ,hbx,hφx,smul_eq_mul,smul_eq_mul,mul_comm]

theorem test_product_error (a b φ : BoundedMultiplier ν) (v : Lp ℝ 2 ν) :
    ‖a.map v-b.map φ.toL2‖ ≤ a.bound*‖v-φ.toL2‖+φ.bound*‖a.toL2-b.toL2‖ := by
  have hsplit : a.map v-b.map φ.toL2=a.map (v-φ.toL2)+φ.map (a.toL2-b.toL2) := by
    have ha : a.map (v-φ.toL2)=a.map v-a.map φ.toL2 := a.linearMap.map_sub v φ.toL2
    have hφ : φ.map (a.toL2-b.toL2)=φ.map a.toL2-φ.map b.toL2 := φ.linearMap.map_sub a.toL2 b.toL2
    rw [ha,hφ,map_toL2_comm a φ,map_toL2_comm b φ]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add (a.seminorm_le _) (φ.seminorm_le _))

theorem test_product_strong_convergence (a : ℕ → BoundedMultiplier ν) (b φ : BoundedMultiplier ν)
    {M : ℝ} (hbound : ∀ n, (a n).bound ≤ M)
    (hb : Tendsto (fun n => (a n).toL2) atTop (𝓝 b.toL2))
    (v : ℕ → Lp ℝ 2 ν) (hv : Tendsto v atTop (𝓝 φ.toL2)) :
    Tendsto (fun n => (a n).map (v n)) atTop (𝓝 (b.map φ.toL2)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hmajor : Tendsto (fun n => M*‖v n-φ.toL2‖+φ.bound*‖(a n).toL2-b.toL2‖) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((tendsto_const_nhds (x := M)).mul (tendsto_iff_norm_sub_tendsto_zero.mp hv)).add
        ((tendsto_const_nhds (x := φ.bound)).mul (tendsto_iff_norm_sub_tendsto_zero.mp hb))
  apply squeeze_zero (fun _ => norm_nonneg _) _ hmajor
  intro n
  exact (test_product_error (a n) b φ (v n)).trans
    (add_le_add (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)) le_rfl)

end Carleman.BoundedMultiplier
