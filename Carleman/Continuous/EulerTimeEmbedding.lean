module

public import Carleman.Continuous.SobolevError
public import Carleman.Continuous.FormTimeGraph
public import Carleman.Periodic.EulerShift

/-! Actual Euler solutions embedded into Bochner time spaces. The extended
difference is explicitly a discrete difference, not a claimed weak derivative
of the piecewise constant state. Its uniform estimates are proved from T007. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
namespace Orientation
variable (s : Orientation) (g : TimeGrid)
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def extensionLp (u : g.Sequence H) : Lp H 2 g.timeMeasure :=
  (s.memLp_extension g u).toLp (s.extension g u)

omit [InnerProductSpace ℝ H] in
theorem extensionLp_ae (u : g.Sequence H) :
    s.extensionLp g u =ᵐ[g.timeMeasure] s.extension g u := (s.memLp_extension g u).coeFn_toLp

theorem extensionLp_norm_sq (u : g.Sequence H) : ‖s.extensionLp g u‖^2 = g.l2Sq u := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ t, s.extension g (fun i => ‖u i‖^2) t ∂g.timeMeasure := by
      apply integral_congr_ae
      filter_upwards [s.extensionLp_ae g u] with t ht
      rw [ht, real_inner_self_eq_norm_sq]
      cases s <;> rfl
    _ = g.l2Sq u := s.integral_extension g _

theorem extensionLp_norm (u : g.Sequence H) : ‖s.extensionLp g u‖ = g.l2Norm u := by
  have he := s.extensionLp_norm_sq g u
  have hn := g.l2Norm_sq u
  nlinarith [norm_nonneg (s.extensionLp g u), g.l2Norm_nonneg u]
end Orientation

namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (s : Orientation)

/-- Every actual piecewise constant Euler state and operator belong to the
closed L² operator graph. No time differentiability is asserted here. -/
theorem eulerExtension_graph (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i) (f : g.Sequence H) :
    (s.extensionLp g (fun i => (b.eulerSolution g s μ hμ f i : H)),
      s.extensionLp g (fun i => b.operator (b.eulerSolution g s μ hμ f i))) ∈
      b.timeOperatorGraph g.timeMeasure := by
  apply (b.timeOperatorGraph_ae g.timeMeasure _ _).mpr
  filter_upwards [s.extensionLp_ae g (fun i => (b.eulerSolution g s μ hμ f i : H)),
    s.extensionLp_ae g (fun i => b.operator (b.eulerSolution g s μ hμ f i))] with t hv ha
  rw [hv, ha]
  apply (b.operatorGraph_mem _ _).mpr
  refine ⟨s.extension g (b.eulerSolution g s μ hμ f) t, ?_, ?_⟩ <;> cases s <;> rfl

/-- The genuine continuous-time L² norms of the Euler extensions satisfy the
same uniform estimate. This is a constructed approximant estimate, not B1. -/
theorem eulerExtension_graph_bound {m : ℕ} (hm : 0 < m) {β L : ℝ}
    (hL : eulerShiftThreshold m β ≤ L) (w : TimeWeight)
    (hw : TimeWeightRegularity w g β) (hmesh : g.dt*w.max^2 ≤ cellThreshold β 0 0)
    (f : g.Sequence H) :
    let μ := fun i => (L*w.nodes g i)^(2*m)
    let hμ : ∀ i, 0 ≤ μ i := fun _ => (even_two_mul m).pow_nonneg _
    let u := b.eulerSolution g s μ hμ f
    ‖s.extensionLp g (s.difference g (fun i => (u i : H)))‖ +
      ‖s.extensionLp g (fun i => b.operator (u i))‖ +
      ‖s.extensionLp g (fun i => μ i • (u i : H))‖ ≤ 3 * ‖s.extensionLp g f‖ := by
  intro μ hμ u
  simp only [s.extensionLp_norm]
  have he := b.euler_unweighted_graph hm hL g w hw hmesh s u
  have hr : (fun i => s.difference g (fun k => (u k : H)) i + b.operator (u i) +
      (L*w.nodes g i)^(2*m) • (u i : H)) = f :=
    funext (b.eulerSolution_equation g s μ hμ f)
  change _ ≤ 3 * g.l2Norm (fun i => s.difference g (fun k => (u k : H)) i +
    b.operator (u i) + (L*w.nodes g i)^(2*m) • (u i : H)) at he
  rw [hr] at he
  exact he
end CoerciveForm
end Carleman
