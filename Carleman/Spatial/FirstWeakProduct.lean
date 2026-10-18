module

public import Carleman.Spatial.FirstGradientAssembly
public import Carleman.Spatial.SobolevTopology

/-! A bounded smooth coefficient acts continuously on genuine H¹ jets,
with a proved weak product rule for every coordinate. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

def firstProductFields (w : BoundedMultiplier ν) (dw : Fin d → BoundedMultiplier ν)
    (u : WeakSobolevJet d 1 ν S) : JetFields d 1 ν :=
  Fin.cases ((OperatorMultiplier.const scalarZeroFiber).map (w.map (WeakSobolevJet.value u)))
    (fun j => by
      have hj : j=0 := Fin.eq_zero j
      subst j
      exact w.map (E := DerivativeFiber d 1) (WeakSobolevJet.field (1 : Fin 2) u)+firstGradientAssembly (fun i => (dw i).map (WeakSobolevJet.value u)))

def weakFirstProduct (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (w : BoundedMultiplier ν) (dw : Fin d → BoundedMultiplier ν)
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : ∀ i, (dw i).value =ᵐ[ν] (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u : WeakSobolevJet d 1 ν S) : WeakSobolevJet d 1 ν S := by
  refine ⟨firstProductFields w dw u,?_⟩
  intro k α i
  have hk : k=0 := Fin.eq_zero k
  subst k
  have ha : α=Sym.nil := Sym.eq_nil_of_card_zero α
  subst α
  change IsWeakSpatialDerivative ν S _
    (derivativeComponent Sym.nil ((OperatorMultiplier.const scalarZeroFiber).map (w.map (WeakSobolevJet.value u))))
    (derivativeComponent (Sym.cons i Sym.nil)
      (w.map (E := DerivativeFiber d 1) (WeakSobolevJet.field (1 : Fin 2) u)+firstGradientAssembly (fun j => (dw j).map (WeakSobolevJet.value u))))
  rw [scalarZeroFiber_component,map_add,derivativeComponent_multiplier,firstGradientAssembly_component]
  exact (WeakSobolevJet.field_weak_derivative u 0 Sym.nil i).mul hS hν w (dw i) hw (hdw i)

theorem weakFirstProduct_value (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (w : BoundedMultiplier ν) (dw : Fin d → BoundedMultiplier ν)
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : ∀ i, (dw i).value =ᵐ[ν] (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u : WeakSobolevJet d 1 ν S) :
    WeakSobolevJet.value (weakFirstProduct hS hν w dw hw hdw u)=w.map (WeakSobolevJet.value u) :=
  scalarZeroFiber_component _ Sym.nil

variable [IsLocallyFiniteMeasure ν]

def weakFirstProductCLM (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)
    (w : BoundedMultiplier ν) (dw : Fin d → BoundedMultiplier ν)
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : ∀ i, (dw i).value =ᵐ[ν] (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i))) :
    WeakSobolevJet d 1 ν S →L[ℝ] WeakSobolevJet d 1 ν S where
  toFun := weakFirstProduct hS hν w dw hw hdw
  map_add' u v := by
    apply WeakSobolevJet.value_injective hS hν
    simp only [weakFirstProduct_value,map_add,BoundedMultiplier.map_add]
  map_smul' a u := by
    apply WeakSobolevJet.value_injective hS hν
    simp only [weakFirstProduct_value,map_smul,BoundedMultiplier.map_smul,RingHom.id_apply]
  cont := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro k
    fin_cases k
    · exact (OperatorMultiplier.const scalarZeroFiber).continuousLinearMap.continuous.comp
        (w.continuousLinearMap.continuous.comp WeakSobolevJet.valueCLM.continuous)
    · change Continuous (fun u : WeakSobolevJet d 1 ν S =>
        w.map (E := DerivativeFiber d 1) (WeakSobolevJet.field (1 : Fin 2) u)+
          firstGradientAssembly (fun i => (dw i).map (WeakSobolevJet.value u)))
      exact (w.continuousLinearMap.continuous.comp (WeakSobolevJet.fieldCLM (1 : Fin 2)).continuous).add
        (firstGradientAssembly.continuous.comp (continuous_pi (fun i =>
          (dw i).continuousLinearMap.continuous.comp WeakSobolevJet.valueCLM.continuous)))

end Carleman
