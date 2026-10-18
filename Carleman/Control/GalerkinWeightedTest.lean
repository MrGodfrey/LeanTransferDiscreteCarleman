module

public import Carleman.Control.GalerkinNumericalData
public import Carleman.Weights.TemporalMultiplier
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The actual weighted Galerkin test is Pi_X(sigma² z), equivalently F*F
for F=sigma times the inclusion. This includes its true time derivative. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}
  (X : Submodule ℝ (Lp E 2 ν)) [CompleteSpace X]
  (ρ : SpatialProfile ν) (w : TimeWeight)

def weightedInclusion (τ t : ℝ) : X →L[ℝ] Lp E 2 ν :=
  (ρ.weightCLM w τ t).comp X.subtypeL

def galerkinWeightedTest (τ t : ℝ) : X →L[ℝ] X :=
  (weightedInclusion X ρ w τ t).adjoint.comp (weightedInclusion X ρ w τ t)

theorem galerkinWeightedTest_pairing (τ t : ℝ) (x z : X) :
    inner ℝ x (galerkinWeightedTest X ρ w τ t z) =
      inner ℝ ((ρ.multiplier w τ t).map (x : Lp E 2 ν))
        ((ρ.multiplier w τ t).map (z : Lp E 2 ν)) := by
  rw [galerkinWeightedTest,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]
  simp only [weightedInclusion,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,ρ.weightCLM_apply]

theorem galerkinWeightedTest_apply (τ t : ℝ) (z : X) :
    galerkinWeightedTest X ρ w τ t z =
      X.orthogonalProjectionOnto ((ρ.multiplier w τ t).map ((ρ.multiplier w τ t).map (z : Lp E 2 ν))) := by
  apply ext_inner_left ℝ
  intro x
  rw [galerkinWeightedTest_pairing,X.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact multiplier_clm_symmetric (ρ.multiplier w τ t) (x : Lp E 2 ν)
    ((ρ.multiplier w τ t).map (z : Lp E 2 ν))

theorem galerkinWeightedTest_symmetric (τ t : ℝ) (x z : X) :
    inner ℝ x (galerkinWeightedTest X ρ w τ t z) = inner ℝ z (galerkinWeightedTest X ρ w τ t x) := by
  rw [galerkinWeightedTest_pairing,galerkinWeightedTest_pairing]
  exact real_inner_comm _ _

theorem galerkinWeightedTest_energy (τ t : ℝ) (z : X) :
    inner ℝ z (galerkinWeightedTest X ρ w τ t z) =
      ((ρ.multiplier w τ t).seminorm (z : Lp E 2 ν))^2 := by
  rw [galerkinWeightedTest_pairing,real_inner_self_eq_norm_sq]
  rfl

theorem galerkinWeightedTest_nonneg (τ t : ℝ) (z : X) :
    0 ≤ inner ℝ z (galerkinWeightedTest X ρ w τ t z) := by
  rw [galerkinWeightedTest_energy]
  positivity

variable {g : TimeGrid} {β : ℝ} (h : TimeWeightRegularity w g β)

def weightedInclusionDerivative (τ t : ℝ) : X →L[ℝ] Lp E 2 ν :=
  (ρ.weightDerivativeCLM h τ t).comp X.subtypeL

def galerkinWeightedTestDerivative (τ t : ℝ) : X →L[ℝ] X :=
  (weightedInclusionDerivative X ρ w h τ t).adjoint.comp (weightedInclusion X ρ w τ t)+
    (weightedInclusion X ρ w τ t).adjoint.comp (weightedInclusionDerivative X ρ w h τ t)

theorem galerkinWeightedTestDerivative_pairing (τ t : ℝ) (x z : X) :
    inner ℝ x (galerkinWeightedTestDerivative X ρ w h τ t z) =
      inner ℝ (weightedInclusionDerivative X ρ w h τ t x) (weightedInclusion X ρ w τ t z)+
        inner ℝ (weightedInclusion X ρ w τ t x) (weightedInclusionDerivative X ρ w h τ t z) := by
  simp only [galerkinWeightedTestDerivative,add_apply,inner_add_right,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right]

include h in
theorem galerkinWeightedTest_endpoint (τ : ℝ) :
    galerkinWeightedTest X ρ w τ 0 = galerkinWeightedTest X ρ w τ g.period := by
  simp only [galerkinWeightedTest,weightedInclusion,ρ.weightCLM_periodic_trace h τ]

theorem galerkinWeightedTest_hasDeriv (τ : ℝ) (z : X) {t : ℝ} (ht : t ∈ Icc 0 g.period) :
    HasDerivWithinAt (fun s => inner ℝ z (galerkinWeightedTest X ρ w τ s z))
      (inner ℝ z (galerkinWeightedTestDerivative X ρ w h τ t z)) (Icc 0 g.period) t := by
  have hd := (ρ.hasDerivWithinAt_weightCLM (E := E) h τ ht).clm_apply
    (hasDerivWithinAt_const t (Icc 0 g.period) (z : Lp E 2 ν))
  simp only [map_zero,add_zero] at hd
  have hh := hd.inner ℝ hd
  simpa only [galerkinWeightedTest_pairing,galerkinWeightedTestDerivative_pairing,
    weightedInclusion,weightedInclusionDerivative,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,ρ.weightCLM_apply,add_comm] using hh

end Carleman.Physical
