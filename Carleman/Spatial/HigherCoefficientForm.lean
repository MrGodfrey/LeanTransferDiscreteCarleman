module

public import Carleman.Spatial.CoefficientJetForm
public import Carleman.Spatial.HigherDirichletSpace
public import Carleman.Section3.OriginalForm

/-! The manuscript coefficient form on the actual H₀ᵐ Hilbert space.
Coercivity is exactly the original assumption, not an inferred property. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace Carleman
variable {d m : ℕ} {S : Set (SpatialCoordinates d)}

abbrev HigherDirichletEnergy (S : Set (SpatialCoordinates d)) (m : ℕ) :=
  conformingHilbert (m := m) (S := S) (higherDirichletSubspace S m)

def higherDirichletToJet (S : Set (SpatialCoordinates d)) (m : ℕ) :
    HigherDirichletEnergy S m →L[ℝ] WeakSobolevJet d m (volume.restrict S) S :=
  SobolevHilbert.toJet.comp (conformingHilbert (m := m) (S := S) (higherDirichletSubspace S m)).subtypeL

theorem higherDirichletEnergy_norm_sq (u : HigherDirichletEnergy S m) :
    ‖u‖^2=∑ α : MultiDerivativeIndex d m, ‖jetScalarComponent α (higherDirichletToJet S m u)‖^2 := by
  change ‖u.val‖^2=_
  rw [SobolevHilbert.norm_sq, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  exact derivativeField_norm_sq _

def higherCoefficientForm (S : Set (SpatialCoordinates d)) (m : ℕ)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S)) :
    HigherDirichletEnergy S m →L[ℝ] HigherDirichletEnergy S m →L[ℝ] ℝ :=
  (coefficientJetForm a).bilinearComp (higherDirichletToJet S m) (higherDirichletToJet S m)

theorem higherCoefficientForm_apply
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S))
    (u v : HigherDirichletEnergy S m) :
    higherCoefficientForm S m a u v=coefficientJetForm a (higherDirichletToJet S m u) (higherDirichletToJet S m v) := rfl

theorem higherCoefficientForm_symmetric
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S))
    (hsym : ∀ α β, (a α β).value =ᵐ[volume.restrict S] (a β α).value)
    (u v : HigherDirichletEnergy S m) : higherCoefficientForm S m a u v=higherCoefficientForm S m a v u :=
  coefficientJetForm_symmetric a hsym _ _

theorem higherCoefficientForm_integral
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S))
    (u v : HigherDirichletEnergy S m) :
    higherCoefficientForm S m a u v=∑ α, ∑ β, ∫ x,
      (a α β).value x*(jetScalarComponent β (higherDirichletToJet S m u) x)*
      (jetScalarComponent α (higherDirichletToJet S m v) x) ∂(volume.restrict S) :=
  coefficientJetForm_integral a _ _

theorem higherCoefficientForm_weighted_upper
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S))
    (w ξ : BoundedMultiplier (volume.restrict S))
    (hinv : ∀ᵐ x ∂(volume.restrict S), w.value x*ξ.value x=1)
    {q : ℝ} (hq : 1 ≤ q) (u v : HigherDirichletEnergy S m) :
    |higherCoefficientForm S m a u v| ≤ (∑ α, ∑ β, (a α β).bound)*
      WeakSobolevJet.weightedNorm q w (higherDirichletToJet S m u)*
      WeakSobolevJet.weightedNorm q ξ (higherDirichletToJet S m v) :=
  coefficientJetForm_weighted_upper a w ξ hinv hq _ _

def higherCoefficientOriginalForm (hS : IsOpen S)
    (a : MultiDerivativeIndex d m → MultiDerivativeIndex d m → BoundedMultiplier (volume.restrict S))
    (hsym : ∀ α β, (a α β).value =ᵐ[volume.restrict S] (a β α).value)
    (hcoer : ∃ c > (0 : ℝ), ∀ u : HigherDirichletEnergy S m, c*‖u‖*‖u‖ ≤ higherCoefficientForm S m a u u) :
    OriginalForm (m := m) (ν := volume.restrict S) hS (ae_restrict_mem hS.measurableSet) where
  V := higherDirichletSubspace S m
  sobolev := higherDirichletSubspace_sobolev S m
  closed := higherDirichletSubspace_closed S m hS
  dense := higherDirichletSubspace_dense S m hS
  form := higherCoefficientForm S m a
  symmetric := higherCoefficientForm_symmetric a hsym
  coercive := hcoer

end Carleman
