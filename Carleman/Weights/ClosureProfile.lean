module

public import Carleman.Weights.IntrinsicSmoothClosure

/-! Realize the original bounded-domain profile on the exact restricted
Lebesgue measure, and verify uniqueness of its interior derivative traces. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman

theorem closureDerivative_extension_unique {d k : ℕ} {S : Set (SpatialCoordinates d)}
    {f : SpatialCoordinates d → ℝ}
    {F G : SpatialCoordinates d → (SpatialCoordinates d [×k]→L[ℝ] ℝ)}
    (hF : ContinuousOn F (closure S)) (hG : ContinuousOn G (closure S))
    (heF : EqOn F (iteratedFDeriv ℝ k f) S) (heG : EqOn G (iteratedFDeriv ℝ k f) S) :
    EqOn F G (closure S) :=
  (heF.trans heG.symm).of_subset_closure hF hG subset_closure (Subset.refl _)

def SpatialProfile.ofSmoothOnClosure {d : ℕ} {S : Set (SpatialCoordinates d)}
    {ρ : SpatialCoordinates d → ℝ} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
    (hρ : SmoothOnClosure ρ S) : SpatialProfile (volume.restrict S) :=
  SpatialProfile.ofContinuousOn ρ hρ.1 hbounded.isCompact_closure
    ((ae_restrict_mem hS.measurableSet).mono fun _ hx => subset_closure hx)

theorem SpatialProfile.ofSmoothOnClosure_value {d : ℕ} {S : Set (SpatialCoordinates d)}
    {ρ : SpatialCoordinates d → ℝ} (hS : IsOpen S) (hbounded : Bornology.IsBounded S)
    (hρ : SmoothOnClosure ρ S) : (SpatialProfile.ofSmoothOnClosure hS hbounded hρ).value = ρ := rfl

end Carleman
