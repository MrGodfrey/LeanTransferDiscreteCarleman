module

public import Carleman.Spatial.SobolevRealization

/-! Assemble a genuine first-order weak Sobolev jet from an L² scalar and
an L² continuous-linear derivative field with proved coordinate identities. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)}

def scalarZeroFiber : ℝ →L[ℝ] DerivativeFiber d 0 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Sym (Fin d) 0 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℝ))

def derivativeOneFiber : (SpatialCoordinates d →L[ℝ] ℝ) →L[ℝ] DerivativeFiber d 1 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Sym (Fin d) 1 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun α => ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.basisFun (Fin d) ℝ (Sym.oneEquiv.symm α))))

theorem scalarZeroFiber_component (u : Lp ℝ 2 ν) (α : Sym (Fin d) 0) :
    derivativeComponent α ((OperatorMultiplier.const (scalarZeroFiber (d := d))).map u) = u := by
  apply Lp.ext
  filter_upwards [derivativeComponent_ae α ((OperatorMultiplier.const scalarZeroFiber).map u),
    OperatorMultiplier.const_map_ae scalarZeroFiber u] with x h1 h2
  rw [h1,h2]
  rfl

theorem derivativeOneFiber_component (A : Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 ν) (i : Fin d) :
    derivativeComponent (Sym.cons i Sym.nil) ((OperatorMultiplier.const derivativeOneFiber).map A) =
      (OperatorMultiplier.const (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i))).map A := by
  apply Lp.ext
  filter_upwards [derivativeComponent_ae (Sym.cons i Sym.nil) ((OperatorMultiplier.const derivativeOneFiber).map A),
    OperatorMultiplier.const_map_ae derivativeOneFiber A,
    OperatorMultiplier.const_map_ae (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)) A]
    with x h1 h2 h3
  rw [h1,h2,h3]
  change A x (EuclideanSpace.basisFun (Fin d) ℝ (Sym.oneEquiv.symm (Sym.cons i Sym.nil))) = _
  have he : Sym.cons i Sym.nil = Sym.oneEquiv i := rfl
  rw [he,Equiv.symm_apply_apply]
  rfl

def firstOrderFields (u : Lp ℝ 2 ν) (A : Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 ν) :
    JetFields d 1 ν :=
  Fin.cases ((OperatorMultiplier.const scalarZeroFiber).map u) (fun j => by
    have hj : j = 0 := Fin.eq_zero j
    subst j
    exact (OperatorMultiplier.const derivativeOneFiber).map A)

variable [IsFiniteMeasureOnCompacts ν]

def firstOrderJet {S : Set (SpatialCoordinates d)}
    (u : Lp ℝ 2 ν) (A : Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 ν)
    (h : ∀ i : Fin d, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i) u
      ((OperatorMultiplier.const (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i))).map A)) :
    WeakSobolevJet d 1 ν S := by
  refine ⟨firstOrderFields u A,?_⟩
  intro k α i
  have hk : k = 0 := Fin.eq_zero k
  subst k
  have ha : α = Sym.nil := Sym.eq_nil_of_card_zero α
  subst α
  change IsWeakSpatialDerivative ν S _
    (derivativeComponent Sym.nil ((OperatorMultiplier.const scalarZeroFiber).map u))
    (derivativeComponent (Sym.cons i Sym.nil) ((OperatorMultiplier.const derivativeOneFiber).map A))
  rw [scalarZeroFiber_component,derivativeOneFiber_component]
  exact h i

theorem firstOrderJet_value {S : Set (SpatialCoordinates d)}
    (u : Lp ℝ 2 ν) (A : Lp (SpatialCoordinates d →L[ℝ] ℝ) 2 ν)
    (h : ∀ i : Fin d, IsWeakSpatialDerivative ν S (EuclideanSpace.basisFun (Fin d) ℝ i) u
      ((OperatorMultiplier.const (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i))).map A)) :
    WeakSobolevJet.value (firstOrderJet u A h) = u :=
  scalarZeroFiber_component u Sym.nil

end Carleman
