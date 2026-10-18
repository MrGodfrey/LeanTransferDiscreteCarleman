module

public import Carleman.Spatial.DirichletForm

/-! The L² gradient pairing is the sum of the genuine coordinate
derivative pairings, with each first-order component counted once. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d k : ℕ} {ν : Measure (SpatialCoordinates d)}

theorem derivativeField_inner (u v : Lp (DerivativeFiber d k) 2 ν) :
    inner ℝ u v = ∑ α : Sym (Fin d) k,
      inner ℝ (derivativeComponent α u) (derivativeComponent α v) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, ∑ α : Sym (Fin d) k,
        inner ℝ (derivativeComponent α u x) (derivativeComponent α v x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr (fun α => derivativeComponent_ae α u),
        ae_all_iff.mpr (fun α => derivativeComponent_ae α v)] with x hu hv
      simp only [PiLp.inner_apply,hu,hv]
    _ = ∑ α : Sym (Fin d) k, ∫ x,
        inner ℝ (derivativeComponent α u x) (derivativeComponent α v x) ∂ν :=
      integral_finsetSum _ (fun α _ => L2.integrable_inner _ _)
    _ = _ := by simp only [L2.inner_def]

theorem firstDerivativeField_inner (u v : Lp (DerivativeFiber d 1) 2 ν) :
    inner ℝ u v = ∑ i : Fin d, inner ℝ
      (derivativeComponent (Sym.cons i Sym.nil) u)
      (derivativeComponent (Sym.cons i Sym.nil) v) := by
  rw [derivativeField_inner]
  exact (Equiv.sum_comp Sym.oneEquiv
    (fun α => inner ℝ (derivativeComponent α u) (derivativeComponent α v))).symm

variable [IsFiniteMeasureOnCompacts ν] {S : Set (SpatialCoordinates d)}

def weakGradientPairing : WeakSobolevJet d 1 ν S →L[ℝ] WeakSobolevJet d 1 ν S →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (WeakSobolevJet.fieldCLM 1) (WeakSobolevJet.fieldCLM 1)

theorem weakGradientPairing_apply (u v : WeakSobolevJet d 1 ν S) :
    weakGradientPairing u v = inner ℝ (WeakSobolevJet.field 1 u) (WeakSobolevJet.field 1 v) := rfl

end Carleman
