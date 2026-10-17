module

public import Carleman.Spatial.SobolevTopology
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The actual weak Sobolev fields with the Hilbert norm given by the sum
of their L² squares. This is the energy topology, not the scalar H norm. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable (d m : ℕ) (ν : Measure (SpatialCoordinates d)) [IsFiniteMeasureOnCompacts ν]
  (S : Set (SpatialCoordinates d))

abbrev HilbertJetFields := PiLp 2 (fun k : Fin (m+1) => Lp (DerivativeFiber d k.val) 2 ν)

def hilbertJetSubmodule : Submodule ℝ (HilbertJetFields d m ν) :=
  (weakJetSubmodule d m ν S).comap (WithLp.linearEquiv 2 ℝ (JetFields d m ν)).toLinearMap

abbrev SobolevHilbert := hilbertJetSubmodule d m ν S

theorem hilbertJetSubmodule_isClosed :
    IsClosed (hilbertJetSubmodule d m ν S : Set (HilbertJetFields d m ν)) :=
  (weakJetSubmodule_isClosed d m ν S).preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun k : Fin (m+1) => Lp (DerivativeFiber d k.val) 2 ν)).continuous

instance sobolevHilbert_completeSpace : CompleteSpace (SobolevHilbert d m ν S) := by
  let : IsClosed (hilbertJetSubmodule d m ν S : Set (HilbertJetFields d m ν)) :=
    hilbertJetSubmodule_isClosed d m ν S
  exact IsClosed.completeSpace_coe

variable {d m ν S}

def SobolevHilbert.toJet : SobolevHilbert d m ν S →L[ℝ] WeakSobolevJet d m ν S :=
  (((PiLp.continuousLinearEquiv 2 ℝ
    (fun k : Fin (m+1) => Lp (DerivativeFiber d k.val) 2 ν)).toContinuousLinearMap).comp
      (hilbertJetSubmodule d m ν S).subtypeL).codRestrict (weakJetSubmodule d m ν S)
        (fun u => u.property)

def SobolevHilbert.ofJet : WeakSobolevJet d m ν S →L[ℝ] SobolevHilbert d m ν S :=
  (((PiLp.continuousLinearEquiv 2 ℝ
    (fun k : Fin (m+1) => Lp (DerivativeFiber d k.val) 2 ν)).symm.toContinuousLinearMap).comp
      (weakJetSubmodule d m ν S).subtypeL).codRestrict (hilbertJetSubmodule d m ν S)
        (fun u => u.property)

def SobolevHilbert.jetEquiv : SobolevHilbert d m ν S ≃L[ℝ] WeakSobolevJet d m ν S where
  toLinearEquiv :=
    { toLinearMap := SobolevHilbert.toJet.toLinearMap
      invFun := SobolevHilbert.ofJet
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := SobolevHilbert.toJet.continuous
  continuous_invFun := SobolevHilbert.ofJet.continuous

theorem SobolevHilbert.norm_sq (u : SobolevHilbert d m ν S) :
    ‖u‖^2 = ∑ k : Fin (m+1), ‖WeakSobolevJet.field k (SobolevHilbert.toJet u)‖^2 :=
  PiLp.norm_sq_eq_of_L2 _ u.val

def SobolevHilbert.value : SobolevHilbert d m ν S →L[ℝ] Lp ℝ 2 ν :=
  WeakSobolevJet.valueCLM.comp SobolevHilbert.toJet

variable [IsLocallyFiniteMeasure ν] (hS : IsOpen S) (hν : ∀ᵐ x ∂ν, x ∈ S)

include hS hν in
theorem SobolevHilbert.value_injective : Function.Injective (SobolevHilbert.value (d := d) (m := m) (ν := ν) (S := S)) :=
  (WeakSobolevJet.value_injective hS hν).comp SobolevHilbert.jetEquiv.injective

end Carleman
