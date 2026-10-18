module

public import Carleman.Spatial.WeakDerivative

/-! Zero extension as an actual isometry of L² classes. No claim is made
that zero extension preserves a Sobolev derivative across the boundary. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} {S : Set X} (hS : MeasurableSet S)

def zeroExtendLp (u : Lp E 2 (μ.restrict S)) : Lp E 2 μ :=
  ((memLp_indicator_iff_restrict hS.nullMeasurableSet).mpr (Lp.memLp u)).toLp (S.indicator u)

theorem zeroExtendLp_ae (u : Lp E 2 (μ.restrict S)) :
    zeroExtendLp hS u =ᵐ[μ] S.indicator u :=
  MemLp.coeFn_toLp _

theorem zeroExtendLp_ae_restrict (u : Lp E 2 (μ.restrict S)) :
    zeroExtendLp hS u =ᵐ[μ.restrict S] u := by
  filter_upwards [(zeroExtendLp_ae hS u).filter_mono ae_restrict_le,
    ae_restrict_mem hS] with x hx hxS
  rw [hx,indicator_of_mem hxS]

theorem zeroExtendLp_norm (u : Lp E 2 (μ.restrict S)) : ‖zeroExtendLp hS u‖ = ‖u‖ := by
  rw [Lp.norm_def,Lp.norm_def,eLpNorm_congr_ae (zeroExtendLp_ae hS u),
    eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet]

theorem integral_mul_zeroExtendLp (u : Lp ℝ 2 (μ.restrict S)) (g : X → ℝ) :
    (∫ x, g x*zeroExtendLp hS u x ∂μ) = ∫ x, g x*u x ∂μ.restrict S := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [zeroExtendLp_ae hS u] with x hx
  rw [hx]
  by_cases hxS : x ∈ S
  · simp only [indicator_of_mem hxS]
  · simp only [indicator_of_notMem hxS,mul_zero]
end Carleman
