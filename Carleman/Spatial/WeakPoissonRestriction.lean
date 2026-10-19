module

public import Carleman.Spatial.DirichletExtensionPairing
public import Carleman.Spatial.WeakLaplacianLimit

/-! Restricting an actual weak Poisson solution preserves the same load.
Only tests compactly supported in the smaller open set are transferred. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

theorem IsWeakNegativeLaplacian.restrictSubdomain (hS : IsOpen S) (hT : IsOpen T)
    (hTS : T ⊆ S) {u : WeakSobolevJet d 1 (volume.restrict S) S}
    {f : Lp ℝ 2 (volume.restrict S)} (h : IsWeakNegativeLaplacian u f) :
    IsWeakNegativeLaplacian (WeakSobolevJet.restrictSubdomain hTS u) (subdomainLp hTS f) := by
  intro φ
  have he := congrArg WeakSobolevJet.value (WeakSobolevJet.extendDirichlet_test hS hT hTS φ)
  rw [WeakSobolevJet.extendDirichlet_value,SpatialTest.sobolevJet_value,SpatialTest.sobolevJet_value] at he
  change subdomainZeroExtend S hT.measurableSet (φ.toLp (volume.restrict T)) =
    (φ.monoDomain hTS).toLp (volume.restrict S) at he
  calc
    _ = weakGradientPairing φ.sobolevJet (WeakSobolevJet.restrictSubdomain hTS u) := by
      simp only [weakGradientPairing_apply]
      exact real_inner_comm _ _
    _ = weakGradientPairing (WeakSobolevJet.extendDirichlet S hT φ.sobolevJet
        (test_mem_dirichletJetSpace T φ)) u :=
      (WeakSobolevJet.extendDirichlet_pairing hT hTS _ _ u).symm
    _ = weakGradientPairing (φ.monoDomain hTS).sobolevJet u := by
      rw [WeakSobolevJet.extendDirichlet_test hS hT hTS]
      rfl
    _ = weakGradientPairing u (φ.monoDomain hTS).sobolevJet := by
      simp only [weakGradientPairing_apply]
      exact real_inner_comm _ _
    _ = inner ℝ f ((φ.monoDomain hTS).toLp (volume.restrict S)) := h _
    _ = inner ℝ (subdomainLp hTS f) (φ.toLp (volume.restrict T)) := by
      rw [← he]
      calc
        _ = inner ℝ (subdomainZeroExtend S hT.measurableSet (φ.toLp (volume.restrict T))) f := real_inner_comm _ _
        _ = inner ℝ (φ.toLp (volume.restrict T)) (subdomainLp hTS f) := subdomainZeroExtend_inner hT.measurableSet hTS _ _
        _ = _ := real_inner_comm _ _

end Carleman
