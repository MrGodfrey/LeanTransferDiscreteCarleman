module

public import Carleman.Periodic.EulerSolution
public import Carleman.Periodic.BilinearEnergy
public import Carleman.Periodic.WeightedNorm

/-! Exact cyclic energy identity and an estimate in the actual discrete L²
norm. The defect is the true oriented increment of the nodal shift. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
namespace TimeGrid
variable (g : TimeGrid) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def l2Sq (u : g.Sequence H) : ℝ := g.weightedSq (fun _ => normSeminorm ℝ H) u

def l2Norm (u : g.Sequence H) : ℝ := g.weightedNorm (fun _ => normSeminorm ℝ H) u

theorem l2Sq_eq (u : g.Sequence H) : g.l2Sq u = g.dt * ∑ i, ‖u i‖^2 := rfl

theorem l2Sq_nonneg (u : g.Sequence H) : 0 ≤ g.l2Sq u := g.weightedSq_nonneg _ u

theorem l2Norm_sq (u : g.Sequence H) : g.l2Norm u ^ 2 = g.l2Sq u := g.weightedNorm_sq _ u

theorem l2Norm_nonneg (u : g.Sequence H) : 0 ≤ g.l2Norm u := Real.sqrt_nonneg _

end TimeGrid
namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : CoerciveForm H V) (g : TimeGrid) (s : Orientation)

def eulerResidual (μ : g.Sequence ℝ) (u : g.Sequence b.domain) : g.Sequence H :=
  fun i => s.difference g (fun k => (u k : H)) i + b.operator (u i) + μ i • (u i : H)

/-- The form term is the squared A^(1/2) energy, expressed without choosing
an unbounded square-root operator. No spatial regularity assumption is added. -/
theorem euler_energy_identity (μ : g.Sequence ℝ) (u : g.Sequence b.domain) :
    g.l2Sq (b.eulerResidual g s μ u) =
      g.l2Sq (s.difference g (fun k => (u k : H))) +
      g.l2Sq (fun i => b.operator (u i) + μ i • (u i : H)) +
      (∑ i, b.form (b.energy (u i) - b.energy (u (s.neighbor g i)))
        (b.energy (u i) - b.energy (u (s.neighbor g i)))) +
      (∑ i, μ i * ‖(u i : H) - (u (s.neighbor g i) : H)‖^2) -
      ∑ i, (μ ((s.neighbor g).symm i) - μ i) * ‖(u i : H)‖^2 := by
  have ha := sum_bilinear_increment b.form.toLinearMap₁₂ b.symmetric (s.neighbor g)
    (fun i => b.energy (u i))
  change 2 * (∑ i, b.form (b.energy (u i) - b.energy (u (s.neighbor g i)))
    (b.energy (u i))) = ∑ i, b.form (b.energy (u i) - b.energy (u (s.neighbor g i)))
      (b.energy (u i) - b.energy (u (s.neighbor g i))) at ha
  have hm := sum_weighted_increment (s.neighbor g) μ (fun i => (u i : H))
  have hp : ∀ i, inner ℝ ((u i : H) - (u (s.neighbor g i) : H)) (b.operator (u i)) =
      b.form (b.energy (u i) - b.energy (u (s.neighbor g i))) (b.energy (u i)) := by
    intro i
    rw [real_inner_comm, ← b.embed_energy (u i), ← b.embed_energy (u (s.neighbor g i)),
      ← map_sub, b.operator_test, b.symmetric]
  have hn : ∀ i, ‖b.eulerResidual g s μ u i‖^2 =
      ‖s.difference g (fun k => (u k : H)) i‖^2 +
      ‖b.operator (u i) + μ i • (u i : H)‖^2 +
      2*g.dt⁻¹*(b.form (b.energy (u i) - b.energy (u (s.neighbor g i))) (b.energy (u i)) +
        μ i * inner ℝ ((u i : H) - (u (s.neighbor g i) : H)) (u i : H)) := by
    intro i
    rw [eulerResidual, add_assoc, norm_add_sq_real, inner_add_right,
      Orientation.difference_neighbor, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, hp]
    ring
  simp only [TimeGrid.l2Sq_eq, hn, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hd : g.dt * g.dt⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt g.dt_pos)
  have hc (x : ℝ) : g.dt * (2*g.dt⁻¹*x) = 2*x := by
    calc
      _ = (g.dt*g.dt⁻¹)*(2*x) := by ring
      _ = _ := by rw [hd, one_mul]
  rw [mul_add, mul_add, hc]
  linarith only [ha, hm]

/-- The uniform unweighted operator graph bound. The increment hypothesis is
subsequently derived for the manuscript's mu=(Lq)^(2m), in both directions. -/
theorem euler_graph_sq (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hinc : ∀ i, μ ((s.neighbor g).symm i) - μ i ≤ g.dt / 2 * (μ i)^2)
    (u : g.Sequence b.domain) :
    g.l2Sq (s.difference g (fun k => (u k : H))) +
      g.l2Sq (fun i => b.operator (u i)) +
      (1/2) * g.l2Sq (fun i => μ i • (u i : H)) ≤ g.l2Sq (b.eulerResidual g s μ u) := by
  have he := b.euler_energy_identity g s μ u
  have hf : 0 ≤ ∑ i, b.form (b.energy (u i) - b.energy (u (s.neighbor g i)))
      (b.energy (u i) - b.energy (u (s.neighbor g i))) :=
    Finset.sum_nonneg fun i _ => b.form_nonneg _
  have hm : 0 ≤ ∑ i, μ i * ‖(u i : H) - (u (s.neighbor g i) : H)‖^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)
  have hs : g.l2Sq (fun i => b.operator (u i)) + g.l2Sq (fun i => μ i • (u i : H)) ≤
      g.l2Sq (fun i => b.operator (u i) + μ i • (u i : H)) := by
    simp only [TimeGrid.l2Sq_eq, ← mul_add, ← Finset.sum_add_distrib]
    apply mul_le_mul_of_nonneg_left _ g.dt_pos.le
    apply Finset.sum_le_sum
    intro i _
    rw [norm_add_sq_real, real_inner_smul_right]
    have := mul_nonneg (hμ i) (b.operator_nonneg (u i))
    linarith
  have hi : (∑ i, (μ ((s.neighbor g).symm i) - μ i) * ‖(u i : H)‖^2) ≤
      (1/2) * g.l2Sq (fun i => μ i • (u i : H)) := by
    calc
      _ ≤ ∑ i, (g.dt / 2 * (μ i)^2) * ‖(u i : H)‖^2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hinc i) (sq_nonneg _)
      _ = _ := by
        simp only [TimeGrid.l2Sq_eq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
          mul_assoc, ← Finset.mul_sum]
        ring
  linarith

/-- A numerical constant independent of T, mesh, node count, shift and state. -/
theorem euler_graph_norm (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hinc : ∀ i, μ ((s.neighbor g).symm i) - μ i ≤ g.dt / 2 * (μ i)^2)
    (u : g.Sequence b.domain) :
    g.l2Norm (s.difference g (fun k => (u k : H))) +
      g.l2Norm (fun i => b.operator (u i)) +
      g.l2Norm (fun i => μ i • (u i : H)) ≤ 3 * g.l2Norm (b.eulerResidual g s μ u) := by
  have h := b.euler_graph_sq g s μ hμ hinc u
  have hx := g.l2Sq_nonneg (s.difference g (fun k => (u k : H)))
  have hy := g.l2Sq_nonneg (fun i => b.operator (u i))
  have hz := g.l2Sq_nonneg (fun i => μ i • (u i : H))
  have hr := g.l2Norm_nonneg (b.eulerResidual g s μ u)
  have hs (a c d : ℝ) : (a+c+d)^2 ≤ 6*(a^2+c^2+d^2/2) := by
    nlinarith [sq_nonneg (a-c), sq_nonneg (a-d/2), sq_nonneg (c-d/2)]
  have hh := hs (g.l2Norm (s.difference g (fun k => (u k : H))))
    (g.l2Norm (fun i => b.operator (u i))) (g.l2Norm (fun i => μ i • (u i : H)))
  simp only [g.l2Norm_sq] at hh
  have hrr := g.l2Norm_sq (b.eulerResidual g s μ u)
  nlinarith [sq_nonneg (g.l2Norm (b.eulerResidual g s μ u))]

end CoerciveForm
end Carleman

@[expose] public noncomputable section
namespace Carleman.TimeGrid
variable (g : Carleman.TimeGrid) {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem l2Norm_le_of_bound (u : g.Sequence H) (v : g.Sequence K) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, ‖u i‖ ≤ C*‖v i‖) : g.l2Norm u ≤ C*g.l2Norm v := by
  have hs : g.l2Sq u ≤ C^2*g.l2Sq v := by
    apply g.weightedSq_le
    intro i
    change ‖u i‖^2 ≤ C^2*‖v i‖^2
    nlinarith [sq_nonneg (C*‖v i‖-‖u i‖), h i, norm_nonneg (u i), norm_nonneg (v i)]
  have hu := g.l2Norm_sq u
  have hv := g.l2Norm_sq v
  have hvn := g.l2Norm_nonneg v
  nlinarith [g.l2Norm_nonneg u, mul_nonneg hC hvn]

end Carleman.TimeGrid
