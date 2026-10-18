module

public import Carleman.Control.PhysicalObservationUniform
public import Carleman.Spatial.MultiplierContinuity
public import Carleman.Spatial.Observation
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Actual L2 conforming subspace operators: orthogonal loads, multiplication
potentials and observed-region controls. No concrete mesh is asserted here. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.Physical
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω}

theorem multiplier_clm_norm (b : BoundedMultiplier ν) :
    ‖b.continuousLinearMap (E := E)‖ ≤ b.bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ b.bound_nonneg
  intro u
  change ‖b.map u‖ ≤ b.bound*‖u‖
  exact b.seminorm_le u

theorem multiplier_clm_symmetric (b : BoundedMultiplier ν) :
    (b.continuousLinearMap (E := E)).IsSymmetric := by
  intro u v
  change inner ℝ (b.map u) v = inner ℝ u (b.map v)
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [b.map_ae u,b.map_ae v] with x hu hv
  rw [hu,hv,real_inner_smul_left,real_inner_smul_right]

variable (X : Submodule ℝ (Lp E 2 ν)) [CompleteSpace X]

def conformingPotential (b : BoundedMultiplier ν) : X →L[ℝ] X :=
  X.orthogonalProjectionOnto.comp (b.continuousLinearMap.comp X.subtypeL)

theorem conformingPotential_apply (b : BoundedMultiplier ν) (x : X) :
    conformingPotential X b x = X.orthogonalProjectionOnto (b.map (x : Lp E 2 ν)) := rfl

theorem conformingPotential_symmetric (b : BoundedMultiplier ν) :
    (conformingPotential X b).IsSymmetric := by
  intro x y
  change inner ℝ (X.orthogonalProjectionOnto (b.map (x : Lp E 2 ν))) y =
    inner ℝ x (X.orthogonalProjectionOnto (b.map (y : Lp E 2 ν)))
  rw [X.inner_orthogonalProjectionOnto_eq_of_mem_left,
    X.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact multiplier_clm_symmetric b (x : Lp E 2 ν) (y : Lp E 2 ν)

theorem conformingPotential_norm (b : BoundedMultiplier ν) :
    ‖conformingPotential X b‖ ≤ b.bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ b.bound_nonneg
  intro x
  change ‖X.orthogonalProjectionOnto (b.map (x : Lp E 2 ν))‖ ≤ b.bound*‖x‖
  exact (X.norm_orthogonalProjectionOnto_apply_le (b.map (x : Lp E 2 ν))).trans
    (b.seminorm_le (x : Lp E 2 ν))

theorem conformingPotential_form (b : BoundedMultiplier ν) (x y : X) :
    inner ℝ (conformingPotential X b x) y =
      ∫ t, b.value t*inner ℝ ((x : Lp E 2 ν) t) ((y : Lp E 2 ν) t) ∂ν := by
  rw [conformingPotential_apply,X.inner_orthogonalProjectionOnto_eq_of_mem_right,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [b.map_ae (x : Lp E 2 ν)] with t ht
  rw [ht,real_inner_smul_left]

theorem conforming_load_right_inverse (x : X) :
    X.orthogonalProjectionOnto (X.subtypeL x) = x := by simp

omit [CompleteSpace X] in
theorem conforming_mass_norm (x : X) : ‖X.subtypeL x‖ = ‖x‖ := rfl

def conformingAmbientControl (ω : Set Ω) (hω : MeasurableSet ω) : Lp E 2 ν →L[ℝ] X :=
  X.orthogonalProjectionOnto.comp (BoundedMultiplier.cutoff ω hω).continuousLinearMap

theorem conformingAmbientControl_norm (ω : Set Ω) (hω : MeasurableSet ω) :
    ‖conformingAmbientControl X ω hω‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  have hh := (X.norm_orthogonalProjectionOnto_apply_le
    ((BoundedMultiplier.cutoff ω hω).map u)).trans ((BoundedMultiplier.cutoff ω hω).seminorm_le u)
  exact hh

theorem conformingAmbientControl_adjoint [CompleteSpace E] (ω : Set Ω) (hω : MeasurableSet ω) :
    (conformingAmbientControl X ω hω).adjoint =
      (BoundedMultiplier.cutoff ω hω).continuousLinearMap.comp X.subtypeL := by
  rw [conformingAmbientControl,ContinuousLinearMap.adjoint_comp,
    (multiplier_clm_symmetric (E := E) (BoundedMultiplier.cutoff ω hω)).clm_adjoint_eq,
    X.adjoint_orthogonalProjectionOnto]

theorem conforming_observation_integral [CompleteSpace E] (ω : Set Ω) (hω : MeasurableSet ω) (x : X) :
    ‖(conformingAmbientControl X ω hω).adjoint x‖^2 = ∫ y in ω, ‖(x : Lp E 2 ν) y‖^2 ∂ν := by
  rw [conformingAmbientControl_adjoint,ContinuousLinearMap.comp_apply,
    BoundedMultiplier.continuousLinearMap_apply,Submodule.subtypeL_apply]
  have hh := (BoundedMultiplier.one (ν := ν)).observation_sq_integral ω hω (x : Lp E 2 ν)
  change (BoundedMultiplier.one (ν := ν)).seminorm ((BoundedMultiplier.cutoff ω hω).map
    (x : Lp E 2 ν)) ^ 2 = _ at hh
  rw [BoundedMultiplier.one_seminorm] at hh
  simpa only [BoundedMultiplier.one,abs_one,one_pow,one_mul] using hh

end Carleman.Physical
