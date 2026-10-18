module

public import Carleman.Control.ObservedRegionLp

/-! The original L2(omega) control operator, rather than a named linear observation. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}
  (X : Submodule ℝ (Lp E 2 ν)) [CompleteSpace X] (ω : Set Ω) (hω : MeasurableSet ω)

def conformingRegionControl : Lp E 2 (ν.restrict ω) →L[ℝ] X :=
  X.orthogonalProjectionOnto.comp (restrictRegionCLM ω).adjoint

theorem conformingRegionControl_apply (u : Lp E 2 (ν.restrict ω)) :
    conformingRegionControl X ω u = X.orthogonalProjectionOnto (zeroExtendLp hω u) := by
  rw [conformingRegionControl,ContinuousLinearMap.comp_apply,restrictRegion_adjoint ω hω]

theorem conformingRegionControl_adjoint :
    (conformingRegionControl X ω).adjoint = (restrictRegionCLM ω).comp X.subtypeL := by
  rw [conformingRegionControl,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,X.adjoint_orthogonalProjectionOnto]

theorem conformingRegionControl_adjoint_apply (x : X) :
    (conformingRegionControl X ω).adjoint x = restrictRegionLp ω (x : Lp E 2 ν) := by
  rw [conformingRegionControl_adjoint]
  rfl

include hω in
theorem conformingRegionControl_norm : ‖conformingRegionControl X ω‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [conformingRegionControl_apply X ω hω]
  have hh := X.norm_orthogonalProjectionOnto_apply_le (zeroExtendLp hω u)
  simpa only [zeroExtendLp_norm,one_mul] using hh

theorem conforming_region_observation_norm (x : X) :
    ‖(conformingRegionControl X ω).adjoint x‖ = ‖(conformingAmbientControl X ω hω).adjoint x‖ := by
  rw [conformingRegionControl_adjoint_apply,conformingAmbientControl_adjoint,
    ContinuousLinearMap.comp_apply,BoundedMultiplier.continuousLinearMap_apply,Submodule.subtypeL_apply]
  exact restrictRegion_norm_eq_cutoff ω hω (x : Lp E 2 ν)

include hω in
theorem conformingRegionControl_pairing (u : Lp E 2 (ν.restrict ω)) (x : X) :
    inner ℝ (conformingRegionControl X ω u) x =
      ∫ t in ω, inner ℝ (u t) ((x : Lp E 2 ν) t) ∂ν := by
  rw [conformingRegionControl_apply X ω hω,X.inner_orthogonalProjectionOnto_eq_of_mem_right,
    L2.inner_def,integral_inner_zeroExtend]

end Carleman.Physical
