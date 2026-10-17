module

public import Carleman.Weights.TimeL2Multiplier
public import Carleman.Continuous.FrozenErrorResidual
public import Carleman.Continuous.NormDomination

/-! Identify the actual weak-trajectory and Euler error function with its
Bochner L² class. The continuous representative keeps the original H traces. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ν : Measure Ω} (ρ : SpatialProfile ν) (g : TimeGrid) (w : TimeWeight) (τ : ℝ)
  (hq : AEStronglyMeasurable w.q g.timeMeasure)

theorem timeMap_bochnerNorm (f : Lp (Lp E 2 ν) 2 g.timeMeasure) :
    bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map (f t)) =
      ‖ρ.timeMap g w τ hq f‖ :=
  (bochnerL2Norm_congr_ae (ρ.timeMap_ae g w τ hq f).symm).trans (bochnerL2Norm_coe _)

theorem timeMap_extension_bochnerNorm (s : Orientation) (u : g.Sequence (Lp E 2 ν)) :
    bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map (s.extension g u t)) =
      ‖ρ.timeMap g w τ hq (s.extensionLp g u)‖ := by
  apply (bochnerL2Norm_congr_ae ?_).trans (ρ.timeMap_bochnerNorm g w τ hq (s.extensionLp g u))
  exact (s.extensionLp_ae g u).symm.mono fun t ht => congrArg _ ht
end Carleman.SpatialProfile

namespace Carleman.CoerciveForm.PeriodicGraph
variable {H W : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  {b : CoerciveForm H W} {g : TimeGrid} (p : b.PeriodicGraph g)

def frozenEulerPair (s : Orientation) (μ : g.Sequence ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (f : g.Sequence H) (hp : b.evolution g s (s.frozenMultiplier g μ) p = s.extensionLp g f) :
    FrozenEulerPair g s μ b.operator f where
  nodes := b.eulerSolution g s μ hμ f
  trajectory := p.toTrajectory
  discrete_equation := b.eulerSolution_equation g s μ hμ f
  continuous_equation := by
    filter_upwards [(b.evolution_eq_iff g s (s.frozenMultiplier g μ) p (s.extensionLp g f)).mp hp,
      s.extensionLp_ae g f] with t ht hf
    exact ht.trans hf
end Carleman.CoerciveForm.PeriodicGraph

namespace Carleman.CoerciveForm.PeriodicGraph
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  {b : CoerciveForm (Lp ℝ 2 ν) W} {g : TimeGrid} (p : b.PeriodicGraph g)
  (ρ : SpatialProfile ν) (w : TimeWeight) (τ : ℝ)
  (hq : AEStronglyMeasurable w.q g.timeMeasure)

theorem weighted_derivative_bochnerNorm :
    bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map (p.toTrajectory.derivative t)) =
      ‖ρ.timeMap g w τ hq p.val.2.1‖ := ρ.timeMap_bochnerNorm g w τ hq p.val.2.1

theorem weighted_error_bochnerNorm (s : Orientation) (u : g.Sequence (Lp ℝ 2 ν)) :
    bochnerL2Norm g.timeMeasure (fun t => (ρ.multiplier w τ t).map
      (p.toTrajectory.value t - s.extension g u t)) =
      ‖ρ.timeMap g w τ hq (g.pathL2 p.val.1 - s.extensionLp g u)‖ := by
  apply (bochnerL2Norm_congr_ae ?_).trans
    (ρ.timeMap_bochnerNorm g w τ hq (g.pathL2 p.val.1 - s.extensionLp g u))
  filter_upwards [g.pathL2_ae p.val.1,s.extensionLp_ae g u,
    Lp.coeFn_sub (g.pathL2 p.val.1) (s.extensionLp g u)] with t hv hu hs
  simp only [Pi.sub_apply] at hs
  rw [hs,hv,hu]
  rfl
end Carleman.CoerciveForm.PeriodicGraph
