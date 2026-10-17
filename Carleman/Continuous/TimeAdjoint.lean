module

public import Carleman.Continuous.WeakTimePairing
public import Carleman.Continuous.AffineTimeClass
public import Carleman.Continuous.VariablePeriodicExistence

/-! Adjoint identities on the actual periodic H¹ and closed operator graphs.
Both temporal signs use the same frozen coefficient and full spatial domain. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
namespace Orientation

def opposite : Orientation → Orientation | .plus => .minus | .minus => .plus

theorem opposite_sign (s : Orientation) : s.opposite.sign = -s.sign := by
  cases s <;> norm_num [opposite, sign]
end Orientation

namespace TimeGrid
variable (g : TimeGrid) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

theorem weak_pairing_L2 (p q : g.TracePath (H := H)) (dp dq : Lp H 2 g.timeMeasure)
    (hp : IsWeakTimeClass g (g.pathL2 p) dp) (hq : IsWeakTimeClass g (g.pathL2 q) dq)
    (hpp : p ⟨0, by simp [g.period_pos.le]⟩ = p ⟨g.period, by simp [g.period_pos.le]⟩)
    (hqp : q ⟨0, by simp [g.period_pos.le]⟩ = q ⟨g.period, by simp [g.period_pos.le]⟩) :
    inner ℝ dp (g.pathL2 q) + inner ℝ (g.pathL2 p) dq = 0 := by
  have hw1 := (IsWeakTimeClass.iff_weakDerivative.mp hp).congr (g.pathL2_ae p)
  have hw2 := (IsWeakTimeClass.iff_weakDerivative.mp hq).congr (g.pathL2_ae q)
  have trace (r : g.TracePath (H := H))
      (hr : r ⟨0, by simp [g.period_pos.le]⟩ = r ⟨g.period, by simp [g.period_pos.le]⟩) :
      g.clampPath r 0 = g.clampPath r g.period := by
    rw [g.clampPath_on _ _ (by simp [g.period_pos.le]),
      g.clampPath_on _ _ (by simp [g.period_pos.le])]
    exact hr
  have he := hw1.periodic_pairing hw2 (g.clampPath p).continuous.continuousOn
    (g.clampPath q).continuous.continuousOn (Lp.memLp dp) (Lp.memLp dq) (trace p hpp) (trace q hqp)
  have h1 : inner ℝ dp (g.pathL2 q) = ∫ t, inner ℝ (dp t) (g.clampPath q t) ∂g.timeMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [g.pathL2_ae q] with t ht
    rw [ht]
  have h2 : inner ℝ (g.pathL2 p) dq = ∫ t, inner ℝ (g.clampPath p t) (dq t) ∂g.timeMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [g.pathL2_ae p] with t ht
    rw [ht]
  rwa [h1,h2]

theorem affine_weakTimeClass (s : Orientation) (u : g.Sequence H) :
    IsWeakTimeClass g (g.affineLp u) (s.sign • s.extensionLp g (s.difference g u)) := by
  apply IsWeakTimeClass.iff_weakDerivative.mpr
  apply (g.affineReconstruction_weakDerivative u).congr (g.affineLp_ae u).symm |>.congr_derivative
  filter_upwards [s.signed_difference_ae g u,
    Lp.coeFn_smul s.sign (s.extensionLp g (s.difference g u)),
    s.extensionLp_ae g (s.difference g u)] with t ht hs hd
  simp only [Pi.smul_apply] at hs
  rw [hs,hd]
  exact ht.symm
end TimeGrid

namespace BoundedMultiplier
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {μ : Measure ℝ}

theorem map_inner (w : BoundedMultiplier μ) (u v : Lp H 2 μ) :
    inner ℝ (w.map u) v = inner ℝ u (w.map v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [w.map_ae u, w.map_ae v] with t hu hv
  rw [hu,hv,real_inner_smul_left,real_inner_smul_right]
end BoundedMultiplier

namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

theorem timeOperatorGraph_symmetric {μ : Measure ℝ} {u a v c : Lp H 2 μ}
    (hu : (u,a) ∈ b.timeOperatorGraph μ) (hv : (v,c) ∈ b.timeOperatorGraph μ) :
    inner ℝ a v = inner ℝ u c := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(b.timeOperatorGraph_ae μ u a).mp hu, (b.timeOperatorGraph_ae μ v c).mp hv]
    with t ht hk
  obtain ⟨x,hx,ha⟩ := (b.operatorGraph_mem _ _).mp ht
  obtain ⟨y,hy,hc⟩ := (b.operatorGraph_mem _ _).mp hk
  rw [←hx,←ha,←hy,←hc]
  exact b.operator_symmetric x y

variable [CompleteSpace H] (g : TimeGrid)

theorem evolution_adjoint (s : Orientation) (μ : BoundedMultiplier g.timeMeasure)
    (p q : b.PeriodicGraph g) :
    inner ℝ (b.evolution g s μ p) (g.pathL2 q.val.1) =
      inner ℝ (g.pathL2 p.val.1) (b.evolution g s.opposite μ q) := by
  have hp := (b.periodicGraph_mem g p.val).mp p.property
  have hq := (b.periodicGraph_mem g q.val).mp q.property
  have ht := g.weak_pairing_L2 p.val.1 q.val.1 p.val.2.1 q.val.2.1 hp.1 hq.1 hp.2.2 hq.2.2
  have ha := b.timeOperatorGraph_symmetric hp.2.1 hq.2.1
  change inner ℝ (s.sign • p.val.2.1 + p.val.2.2 + μ.map (g.pathL2 p.val.1)) (g.pathL2 q.val.1) =
    inner ℝ (g.pathL2 p.val.1) (s.opposite.sign • q.val.2.1 + q.val.2.2 + μ.map (g.pathL2 q.val.1))
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    s.opposite_sign,ha,μ.map_inner]
  have hmul := congrArg (fun a : ℝ => s.sign*a) ht
  simp only [mul_add,mul_zero] at hmul
  linarith
end CoerciveForm
end Carleman
