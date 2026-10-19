module

public import Carleman.Spatial.DerivativeFieldAssembly
public import Carleman.Spatial.SobolevTruncation

/-! A genuine H¹ jet and proved second coordinate derivative identities
assemble the original symmetric H² jet, preserving its original first jet. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

def secondOrderFields (u : WeakSobolevJet d 1 ν S) (A : Lp (DerivativeFiber d 2) 2 ν) :
    JetFields d 2 ν :=
  Fin.cases (WeakSobolevJet.field (m := 1) 0 u) (Fin.cases (WeakSobolevJet.field (m := 1) 1 u) (fun j => by
    have hj : j=0 := Fin.eq_zero j
    subst j
    exact A))

def secondOrderJet (u : WeakSobolevJet d 1 ν S) (A : Lp (DerivativeFiber d 2) 2 ν)
    (hA : ∀ i j : Fin d, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ j)
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field (m := 1) 1 u))
      (derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) A)) : WeakSobolevJet d 2 ν S := by
  refine ⟨secondOrderFields u A,?_⟩
  intro k α j
  fin_cases k
  · exact u.property 0 α j
  · obtain ⟨i,β,hβ⟩ := Sym.exists_eq_cons_of_succ α
    have he := Sym.eq_nil_of_card_zero β
    subst β
    subst α
    exact hA i j

theorem secondOrderJet_truncate (u : WeakSobolevJet d 1 ν S) (A : Lp (DerivativeFiber d 2) 2 ν)
    (hA : ∀ i j : Fin d, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ j)
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field (m := 1) 1 u))
      (derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) A)) :
    WeakSobolevJet.truncate (by omega : 1 ≤ 2) (secondOrderJet u A hA) = u := by
  apply Subtype.ext
  funext k
  fin_cases k <;> rfl

theorem secondOrderJet_hessian (u : WeakSobolevJet d 1 ν S) (A : Lp (DerivativeFiber d 2) 2 ν)
    (hA : ∀ i j : Fin d, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ j)
      (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field (m := 1) 1 u))
      (derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) A)) :
    WeakSobolevJet.field 2 (secondOrderJet u A hA) = A := rfl

end Carleman
