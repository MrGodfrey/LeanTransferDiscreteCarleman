module

public import Carleman.Spatial.ComponentNorms

/-! Finite coordinate assembly in every original Euclidean derivative
fiber, retaining the manuscript's unordered multi-index convention. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Carleman
variable {d k : ℕ} {ν : Measure (SpatialCoordinates d)}

def derivativeFiberInjection (α : Sym (Fin d) k) : ℝ →L[ℝ] DerivativeFiber d k :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Sym (Fin d) k => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun β => if β=α then ContinuousLinearMap.id ℝ ℝ else 0))

theorem derivativeFiberInjection_component (α β : Sym (Fin d) k) (u : Lp ℝ 2 ν) :
    derivativeComponent α ((OperatorMultiplier.const (derivativeFiberInjection β)).map u) =
      if α=β then u else 0 := by
  classical
  apply Lp.ext
  filter_upwards [derivativeComponent_ae α ((OperatorMultiplier.const (derivativeFiberInjection β)).map u),
    OperatorMultiplier.const_map_ae (derivativeFiberInjection β) u,Lp.coeFn_zero ℝ 2 ν] with x hc hi hz
  rw [hc,hi]
  change (if α=β then ContinuousLinearMap.id ℝ ℝ else 0) (u x) = _
  by_cases h : α=β
  · rw [ite_eq_left h,ite_eq_left h]
    rfl
  · rw [ite_eq_right h,ite_eq_right h]
    exact hz.symm

def derivativeFieldAssembly : (Sym (Fin d) k → Lp ℝ 2 ν) →L[ℝ] Lp (DerivativeFiber d k) 2 ν :=
  ∑ α : Sym (Fin d) k, (OperatorMultiplier.const (derivativeFiberInjection α)).continuousLinearMap.comp
    (ContinuousLinearMap.proj α)

theorem derivativeFieldAssembly_component (v : Sym (Fin d) k → Lp ℝ 2 ν) (α : Sym (Fin d) k) :
    derivativeComponent α (derivativeFieldAssembly v) = v α := by
  classical
  simp only [derivativeFieldAssembly,sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,OperatorMultiplier.continuousLinearMap,OperatorMultiplier.linearMap,
    LinearMap.mkContinuous_apply,LinearMap.coe_mk,AddHom.coe_mk,map_sum,derivativeFiberInjection_component]
  simp

theorem derivativeFieldAssembly_norm_sq (v : Sym (Fin d) k → Lp ℝ 2 ν) :
    ‖derivativeFieldAssembly v‖^2 = ∑ α, ‖v α‖^2 := by
  rw [derivativeField_norm_sq]
  simp only [derivativeFieldAssembly_component]

end Carleman
