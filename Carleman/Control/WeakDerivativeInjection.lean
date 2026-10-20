module

public import Carleman.Control.TensorAdjointPairing

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Carleman

theorem HasWeakTimeDerivative.of_injective_map_integral
    {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g : TimeGrid} {u du : ℝ → H}
    (hu : MemLp u 2 g.timeMeasure) (hdu : MemLp du 2 g.timeMeasure)
    (L : H →L[ℝ] F) (hL : Function.Injective L)
    (hw : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 g.period →
      (∫ t, deriv φ t • L (u t) ∂g.timeMeasure)=-(∫ t, φ t • L (du t) ∂g.timeMeasure)) :
    HasWeakTimeDerivative g u du := by
  intro φ hφ hc hs
  have hiu : Integrable (fun t => deriv φ t • u t) g.timeMeasure :=
    memLp_one_iff_integrable.mp ((g.memLp_of_continuousOn (hφ.continuous_deriv (by simp)).continuousOn).smul hu)
  have hid : Integrable (fun t => φ t • du t) g.timeMeasure :=
    memLp_one_iff_integrable.mp ((g.memLp_of_continuousOn hφ.continuous.continuousOn).smul hdu)
  apply hL
  rw [_root_.map_neg,← L.integral_comp_comm hiu,← L.integral_comp_comm hid]
  simpa only [_root_.map_smul] using hw φ hφ hc hs

end Carleman
