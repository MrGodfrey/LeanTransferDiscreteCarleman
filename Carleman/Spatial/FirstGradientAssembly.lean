module

public import Carleman.Spatial.ComponentNorms
public import Carleman.Spatial.FirstOrderSobolevJet

/-! Finite coordinate assembly in the actual first Euclidean derivative
fiber, as a bounded linear map on L² coordinate fields. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}

def firstDerivativeInjection (i : Fin d) : ℝ →L[ℝ] DerivativeFiber d 1 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Sym (Fin d) 1 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun α => if α=Sym.oneEquiv i then ContinuousLinearMap.id ℝ ℝ else 0))

theorem firstDerivativeInjection_component (i j : Fin d) (u : Lp ℝ 2 ν) :
    derivativeComponent (Sym.cons i Sym.nil) ((OperatorMultiplier.const (firstDerivativeInjection j)).map u) =
      if i=j then u else 0 := by
  classical
  apply Lp.ext
  filter_upwards [derivativeComponent_ae (Sym.cons i Sym.nil)
    ((OperatorMultiplier.const (firstDerivativeInjection j)).map u),
    OperatorMultiplier.const_map_ae (firstDerivativeInjection j) u,
    (Lp.coeFn_zero ℝ 2 ν)] with x hc hi hz
  rw [hc,hi]
  change (if Sym.oneEquiv i=Sym.oneEquiv j then ContinuousLinearMap.id ℝ ℝ else 0) (u x) = _
  by_cases h : i=j
  · subst j
    rw [ite_eq_left rfl,ite_eq_left rfl]
    rfl
  · have hn : Sym.oneEquiv i ≠ Sym.oneEquiv j := fun hh => h (Sym.oneEquiv.injective hh)
    rw [ite_eq_right hn,ite_eq_right h]
    exact hz.symm

def firstGradientAssembly : (Fin d → Lp ℝ 2 ν) →L[ℝ] Lp (DerivativeFiber d 1) 2 ν :=
  ∑ i : Fin d, (OperatorMultiplier.const (firstDerivativeInjection i)).continuousLinearMap.comp
    (ContinuousLinearMap.proj i)

theorem firstGradientAssembly_component (v : Fin d → Lp ℝ 2 ν) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (firstGradientAssembly v) = v i := by
  classical
  simp only [firstGradientAssembly,sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,OperatorMultiplier.continuousLinearMap,OperatorMultiplier.linearMap,
    LinearMap.mkContinuous_apply,LinearMap.coe_mk,AddHom.coe_mk,map_sum,firstDerivativeInjection_component]
  simp

end Carleman
