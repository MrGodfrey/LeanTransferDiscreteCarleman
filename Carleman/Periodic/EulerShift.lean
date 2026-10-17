module

public import Carleman.Periodic.EulerEnergy
public import Carleman.Weights.CellBounds

/-! Discharge the cyclic increment bound for the actual manuscript shift.
Both orientations use the same constant and no qmax-dependent graph constant. -/
@[expose] public noncomputable section
open Set
namespace Carleman
namespace TimeWeightRegularity
variable {w : TimeWeight} {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)
include h

theorem shift_node_decrement (L : ℝ) (hL : 0 ≤ L) (k : ℕ) (hk : 1 ≤ k)
    (hm : β*g.dt*w.max^2 ≤ 1/2) (i : g.Index) :
    |(L*w.nodes g (g.prev i))^k - (L*w.nodes g i)^k| ≤
      (2*(k:ℝ)*2^(k-1)*β) * L^k * g.dt * w.nodes g i^(k+1) := by
  let j := g.prev i
  have hs := g.cellTime_mem j.val (Nat.le_of_lt j.isLt)
  have ht := g.cellTime_mem (j.val+1) (Nat.succ_le_of_lt j.isLt)
  have hd : |g.cellTime j.val - g.cellTime (j.val+1)| ≤ g.dt := by
    rw [abs_sub_comm, g.cellTime_succ_sub, abs_of_pos g.dt_pos]
  have he := h.shift_difference L hL k hk ht hs hd hm
  rw [g.next_node_value w.q h.endpoint j] at he
  simpa only [j, TimeGrid.next_prev, TimeWeight.nodes, TimeGrid.cellTime, TimeGrid.nodeTime] using he

theorem shift_oriented_increment (s : Orientation) (L : ℝ) (hL : 0 ≤ L)
    (k : ℕ) (hk : 1 ≤ k) (hm : β*g.dt*w.max^2 ≤ 1/2) (i : g.Index) :
    |(L*w.nodes g ((s.neighbor g).symm i))^k - (L*w.nodes g i)^k| ≤
      (2*(k:ℝ)*2^(k-1)*β) * L^k * g.dt * w.nodes g i^(k+1) := by
  cases s
  · exact h.shift_node_increment L hL k hk hm i
  · exact h.shift_node_decrement L hL k hk hm i

/-- The exact half-absorption needed by the graph estimate. -/
theorem shift_increment_absorb (s : Orientation) (m : ℕ) (hm : 0 < m)
    (L : ℝ) (hL : 1 ≤ L)
    (hlarge : 2*(2*(2*m:ℕ)*2^(2*m-1)*β) ≤ L^(2*m))
    (hmesh : β*g.dt*w.max^2 ≤ 1/2) (i : g.Index) :
    (L*w.nodes g ((s.neighbor g).symm i))^(2*m) - (L*w.nodes g i)^(2*m) ≤
      g.dt/2 * ((L*w.nodes g i)^(2*m))^2 := by
  have hk : 1 ≤ 2*m := by omega
  have hi := (le_abs_self _).trans (h.shift_oriented_increment s L (by linarith) (2*m) hk hmesh i)
  have hq := pow_le_pow_right₀ (w.lower (g.nodeTime i)) (show 2*m+1 ≤ (2*m)*2 by omega)
  change (w.nodes g i)^(2*m+1) ≤ (w.nodes g i)^((2*m)*2) at hq
  have hC : 0 ≤ 2*(2*m:ℕ)*2^(2*m-1)*β := by positivity [h.beta_pos]
  calc
    _ ≤ (2*(2*m:ℕ)*2^(2*m-1)*β) * L^(2*m) * g.dt * (w.nodes g i)^((2*m)*2) :=
      hi.trans (mul_le_mul_of_nonneg_left hq (by positivity [g.dt_pos]))
    _ ≤ (L^(2*m)/2) * L^(2*m) * g.dt * (w.nodes g i)^((2*m)*2) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (w.nonneg _) _)
      apply mul_le_mul_of_nonneg_right _ g.dt_pos.le
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith : 0 ≤ L) _)
      linarith
    _ = _ := by rw [mul_pow, mul_pow, pow_mul]; ring

end TimeWeightRegularity

/-- Explicit L threshold depends only on order and beta. -/
def eulerShiftThreshold (m : ℕ) (β : ℝ) : ℝ := max 1 (2*(2*(2*m:ℕ)*2^(2*m-1)*β))

theorem eulerShiftThreshold_large {m : ℕ} (hm : 0 < m) {β L : ℝ}
    (hL : eulerShiftThreshold m β ≤ L) :
    1 ≤ L ∧ 2*(2*(2*m:ℕ)*2^(2*m-1)*β) ≤ L^(2*m) := by
  have h1 : 1 ≤ L := (le_max_left _ _).trans hL
  refine ⟨h1, ((le_max_right _ _).trans hL).trans ?_⟩
  simpa using pow_le_pow_right₀ h1 (show 1 ≤ 2*m by omega)

namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : CoerciveForm H V)

/-- T-uniform graph estimate for the actual nodal mu, all domain-valued
states, both orientations. Spatial interpolation/weighted conjugation remain. -/
theorem euler_unweighted_graph {m : ℕ} (hm : 0 < m) {β L : ℝ}
    (hL : eulerShiftThreshold m β ≤ L) (g : TimeGrid) (w : TimeWeight)
    (hw : TimeWeightRegularity w g β) (hmesh : g.dt*w.max^2 ≤ cellThreshold β 0 0)
    (s : Orientation) (u : g.Sequence b.domain) :
    g.l2Norm (s.difference g (fun k => (u k : H))) +
      g.l2Norm (fun i => b.operator (u i)) +
      g.l2Norm (fun i => (L*w.nodes g i)^(2*m) • (u i : H)) ≤
      3 * g.l2Norm (b.eulerResidual g s (fun i => (L*w.nodes g i)^(2*m)) u) := by
  obtain ⟨hL1, hlarge⟩ := eulerShiftThreshold_large hm hL
  exact b.euler_graph_norm g s _ (fun i => pow_nonneg (mul_nonneg (zero_le_one.trans hL1) (w.nonneg (g.nodeTime i))) _)
    (hw.shift_increment_absorb s m hm L hL1 hlarge (hw.mesh_bounds 0 0 le_rfl le_rfl hmesh).1) u

/-- Actual unique solution and the bound in terms of the prescribed load,
with all thresholds before T/grid/weight/orientation/load. -/
theorem periodicEuler_wellposed [CompleteSpace V] {m : ℕ} (hm : 0 < m) {β L : ℝ}
    (hL : eulerShiftThreshold m β ≤ L) (g : TimeGrid) (w : TimeWeight)
    (hw : TimeWeightRegularity w g β) (hmesh : g.dt*w.max^2 ≤ cellThreshold β 0 0)
    (s : Orientation) (f : g.Sequence H) :
    ∃! u : g.Sequence b.domain,
      (∀ i, b.eulerResidual g s (fun i => (L*w.nodes g i)^(2*m)) u i = f i) ∧
      g.l2Norm (s.difference g (fun k => (u k : H))) +
        g.l2Norm (fun i => b.operator (u i)) +
        g.l2Norm (fun i => (L*w.nodes g i)^(2*m) • (u i : H)) ≤ 3*g.l2Norm f := by
  have hL1 := (eulerShiftThreshold_large hm hL).1
  let μ : g.Sequence ℝ := fun i => (L*w.nodes g i)^(2*m)
  have hμ : ∀ i, 0 ≤ μ i := fun i =>
    pow_nonneg (mul_nonneg (zero_le_one.trans hL1) (w.nonneg (g.nodeTime i))) _
  let u := b.eulerSolution g s μ hμ f
  have he : b.eulerResidual g s μ u = f := funext (b.eulerSolution_equation g s μ hμ f)
  refine ⟨u, ⟨fun i => congrFun he i, ?_⟩, fun v hv => ?_⟩
  · have hb := b.euler_unweighted_graph hm hL g w hw hmesh s u
    change _ ≤ 3*g.l2Norm (b.eulerResidual g s μ u) at hb
    rwa [he] at hb
  · exact b.eulerSolution_unique g s μ hμ f v hv.1

end CoerciveForm
end Carleman
