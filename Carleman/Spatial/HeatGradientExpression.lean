module

public import Carleman.Transfer.SobolevGeometry
public import Carleman.Transfer.ScaleExponents
public import Carleman.Spatial.DirichletCommutatorIdentity

/-! The actual heat gradient as the order-one bounded-coefficient expression used by transfer. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}

/-- Zero zeroth-order coefficient and identity first-order coefficient. -/
def heatGradientExpression : DifferentialExpression ν
    (fun k : Fin 2 => DerivativeFiber d k.val) (DerivativeFiber d 1) 1 where
  coefficient := fun k => Fin.cases (OperatorMultiplier.const 0)
    (fun i => by
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact OperatorMultiplier.const (ContinuousLinearMap.id ℝ _)) k

theorem heatGradientExpression_apply (u : ∀ k : Fin 2, Lp (DerivativeFiber d k.val) 2 ν) :
    heatGradientExpression.apply u = u 1 := by
  apply Lp.ext
  filter_upwards [heatGradientExpression.apply_ae u] with x hx
  rw [hx]
  have ho : (heatGradientExpression (ν := ν)).orders = Finset.univ := by
    ext k
    simp only [DifferentialExpression.orders, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    have hk := k.isLt
    omega
  rw [ho, Fin.sum_univ_two]
  change 0 + (u 1) x = (u 1) x
  exact zero_add _

/-- The one-member differential family for the heat exponents. -/
def heatDifferentialFamily (j : Fin 1) :
    DifferentialExpression ν
      (fun k : Fin (CarlemanExponents.heat.m+1) => DerivativeFiber d k.val)
      (DerivativeFiber d 1) (j.val+1) := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact heatGradientExpression

variable [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S : Set (SpatialCoordinates d)} (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
  {V : Submodule ℝ (Lp ℝ 2 ν)} (hV : V ≤ sobolevSubspace d 1 ν S)

theorem conforming_heat_expression (j : Fin 1) (v : V) :
    conformingExpression (a := CarlemanExponents.heat) hS hν hV j (heatDifferentialFamily j) v =
      conformingDerivative (a := CarlemanExponents.heat) hS hν hV 1 v := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact heatGradientExpression_apply _

omit [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν] hν hV in
theorem dirichlet_conforming_gradient (hd : 0 < d) (hb : Bornology.IsBounded S)
    (z : (boundedDirichletOriginalForm hS hd hb).model.domain) :
    conformingDerivative (a := CarlemanExponents.heat) hS (ae_restrict_mem hS.measurableSet)
      (boundedDirichletOriginalForm hS hd hb).sobolev 1
      ((boundedDirichletOriginalForm hS hd hb).model.domain.inclusion
        (boundedDirichletOriginalForm hS hd hb).domain_le z) =
      WeakSobolevJet.field 1 (dirichletDomainJet hS hd hb z) := rfl

end Carleman
