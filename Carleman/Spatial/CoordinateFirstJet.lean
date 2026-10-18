module

public import Carleman.Spatial.FirstGradientAssembly

/-! Assemble the genuine H¹ jet of a scalar L² state from its proved weak
coordinate derivatives; the full gradient norm is exactly their square sum. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

def coordinateFirstFields (u : Lp ℝ 2 ν) (v : Fin d → Lp ℝ 2 ν) : JetFields d 1 ν :=
  Fin.cases ((OperatorMultiplier.const scalarZeroFiber).map u) (fun j => by
    have hj : j=0 := Fin.eq_zero j
    subst j
    exact firstGradientAssembly v)

def coordinateFirstJet (u : Lp ℝ 2 ν) (v : Fin d → Lp ℝ 2 ν)
    (h : ∀ i, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i)) :
    WeakSobolevJet d 1 ν S := by
  refine ⟨coordinateFirstFields u v,?_⟩
  intro k α i
  have hk : k=0 := Fin.eq_zero k
  subst k
  have ha : α=Sym.nil := Sym.eq_nil_of_card_zero α
  subst α
  change IsWeakSpatialDerivative ν S _
    (derivativeComponent Sym.nil ((OperatorMultiplier.const scalarZeroFiber).map u))
    (derivativeComponent (Sym.cons i Sym.nil) (firstGradientAssembly v))
  rw [scalarZeroFiber_component,firstGradientAssembly_component]
  exact h i

theorem coordinateFirstJet_value [IsLocallyFiniteMeasure ν]
    (u : Lp ℝ 2 ν) (v : Fin d → Lp ℝ 2 ν)
    (h : ∀ i, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i)) :
    WeakSobolevJet.value (coordinateFirstJet u v h)=u := scalarZeroFiber_component u Sym.nil

theorem coordinateFirstJet_gradient_norm_sq
    (u : Lp ℝ 2 ν) (v : Fin d → Lp ℝ 2 ν)
    (h : ∀ i, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i)) :
    ‖WeakSobolevJet.field 1 (coordinateFirstJet u v h)‖^2=∑ i : Fin d, ‖v i‖^2 := by
  change ‖firstGradientAssembly v‖^2= _
  rw [derivativeField_norm_sq,← Equiv.sum_comp Sym.oneEquiv
    (fun α => ‖derivativeComponent α (firstGradientAssembly v)‖^2)]
  simp only [show ∀ i : Fin d, Sym.oneEquiv i=Sym.cons i Sym.nil from fun _ => rfl,
    firstGradientAssembly_component]

end Carleman
