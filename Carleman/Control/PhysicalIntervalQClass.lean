module

public import Carleman.Control.PhysicalQClass
public import Carleman.Weights.IntervalQClass
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The actual physical weight satisfies the original interval class, including both derivative traces. -/
@[expose] public noncomputable section
open Set
namespace Carleman

theorem smooth_interval_derivatives {q : ℝ → ℝ} (hq : ContDiff ℝ ⊤ q)
    {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc 0 T, derivWithin q (Icc 0 T) t=deriv q t ∧
      derivWithin (derivWithin q (Icc 0 T)) (Icc 0 T) t=deriv (deriv q) t := by
  have hd : EqOn (derivWithin q (Icc 0 T)) (deriv q) (Icc 0 T) := by
    intro t ht
    exact ((hq.differentiable (by norm_num) t).hasDerivAt.hasDerivWithinAt).derivWithin
      (uniqueDiffOn_Icc hT t ht)
  have hdq : ContDiff ℝ ⊤ (deriv q) := hq.deriv'
  intro t ht
  refine ⟨hd ht,?_⟩
  rw [derivWithin_congr hd (hd ht)]
  exact ((hdq.differentiable (by norm_num) t).hasDerivAt.hasDerivWithinAt).derivWithin
    (uniqueDiffOn_Icc hT t ht)

namespace Physical

theorem PhysicalQClass.toInterval {w : TimeWeight} {g : TimeGrid} {β qc : ℝ}
    (h : PhysicalQClass w g.period β qc) : IntervalQClass w.q g.period β qc := by
  have hd := smooth_interval_derivatives h.smooth g.period_pos
  have h0 : (0:ℝ) ∈ Icc 0 g.period := ⟨le_rfl,g.period_pos.le⟩
  have hT : g.period ∈ Icc 0 g.period := ⟨g.period_pos.le,le_rfl⟩
  refine ⟨h.beta_pos,h.qc_ge_one,(h.smooth.of_le (by norm_num)).contDiffOn,
    fun t _ => h.lower t,?_,?_,h.endpoint,?_,?_⟩
  · intro t ht
    rw [(hd t ht).1]
    exact h.first_bound t
  · intro t ht
    rw [(hd t ht).2]
    exact h.second_bound t
  · rw [(hd 0 h0).1,(hd g.period hT).1]
    exact h.first_endpoint
  · rw [(hd 0 h0).2,(hd g.period hT).2]
    exact h.second_endpoint

end Physical
end Carleman
