module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! A strong zero perturbation preserves genuine Hilbert weak limits. -/
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace Carleman

theorem hilbert_weak_of_norm_sub_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : ℕ → H) (y : H)
    (he : Tendsto (fun n => ‖u n-v n‖) atTop (𝓝 0))
    (hv : ∀ w : H, Tendsto (fun n => inner ℝ (v n) w) atTop (𝓝 (inner ℝ y w))) :
    ∀ w : H, Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ y w)) := by
  intro w
  have hb : Tendsto (fun n => ‖u n-v n‖*‖w‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using he.mul_const ‖w‖
  have hh : Tendsto (fun n => inner ℝ (u n-v n) w) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => norm_inner_le_norm (u n-v n) w) hb
  simpa only [inner_sub_left,sub_add_cancel,zero_add] using hh.add (hv w)

end Carleman
