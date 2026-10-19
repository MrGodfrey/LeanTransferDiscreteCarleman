module

public import Carleman.Spatial.FirstGradientAssembly

/-! Assemble a genuine H1 jet from all actual scalar weak gradient components. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

def firstComponentFields (u : Lp ℝ 2 ν) (g : Fin d → Lp ℝ 2 ν) : JetFields d 1 ν :=
  Fin.cases ((OperatorMultiplier.const scalarZeroFiber).map u) (fun j => by
    have hj : j=0 := Fin.eq_zero j
    subst j
    exact firstGradientAssembly g)

def firstComponentJet (u : Lp ℝ 2 ν) (g : Fin d → Lp ℝ 2 ν)
    (hg : ∀ i, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i) u (g i)) :
    WeakSobolevJet d 1 ν S := by
  refine ⟨firstComponentFields u g,?_⟩
  intro k α i
  have hk : k=0 := Fin.eq_zero k
  subst k
  have hα : α=Sym.nil := Sym.eq_nil_of_card_zero α
  subst α
  change IsWeakSpatialDerivative ν S _
    (derivativeComponent Sym.nil ((OperatorMultiplier.const scalarZeroFiber).map u))
    (derivativeComponent (Sym.cons i Sym.nil) (firstGradientAssembly g))
  rw [scalarZeroFiber_component,firstGradientAssembly_component]
  exact hg i

theorem firstComponentJet_value (u : Lp ℝ 2 ν) (g : Fin d → Lp ℝ 2 ν)
    (hg : ∀ i, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i) u (g i)) :
    WeakSobolevJet.value (firstComponentJet u g hg)=u := scalarZeroFiber_component u Sym.nil

theorem firstComponentJet_gradient (u : Lp ℝ 2 ν) (g : Fin d → Lp ℝ 2 ν)
    (hg : ∀ i, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i) u (g i)) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 (firstComponentJet u g hg))=g i :=
  firstGradientAssembly_component g i

omit [IsFiniteMeasureOnCompacts ν] in
theorem firstGradientAssembly_norm_sq (g : Fin d → Lp ℝ 2 ν) :
    ‖firstGradientAssembly g‖^2=∑ i, ‖g i‖^2 := by
  rw [derivativeField_norm_sq,← (Sym.oneEquiv : Fin d ≃ Sym (Fin d) 1).sum_comp]
  change (∑ i, ‖derivativeComponent (Sym.cons i Sym.nil) (firstGradientAssembly g)‖^2)=_
  simp only [firstGradientAssembly_component]

end Carleman
