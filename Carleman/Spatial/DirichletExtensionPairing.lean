module

public import Carleman.Spatial.DirichletSubdomainExtension
public import Carleman.Spatial.SubdomainZeroExtension
public import Carleman.Spatial.DirichletDistribution

/-! Restriction and zero extension preserve the exact test pairings needed
for inner-domain Dirichlet approximation. No boundary flux is discarded. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

theorem SpatialTest.restrictSubdomain_mono (hT : IsOpen T) (hTS : T ⊆ S)
    (φ : SpatialTest T) :
    WeakSobolevJet.restrictSubdomain hTS (φ.monoDomain hTS).sobolevJet = φ.sobolevJet := by
  apply WeakSobolevJet.value_injective hT (ae_restrict_mem hT.measurableSet)
  apply Lp.ext
  rw [φ.sobolevJet_value]
  exact (WeakSobolevJet.restrictSubdomain_test_value_ae hTS (φ.monoDomain hTS)).trans
    (φ.toLp_ae (volume.restrict T)).symm

namespace WeakSobolevJet

theorem extendDirichlet_field (hT : IsOpen T)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (hu : u ∈ dirichletJetSpace T) (k : Fin 2) :
    field k (extendDirichlet S hT u hu) = subdomainZeroExtend S hT.measurableSet (field k u) := rfl

theorem extendDirichlet_field_norm (hT : IsOpen T) (hTS : T ⊆ S)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (hu : u ∈ dirichletJetSpace T) (k : Fin 2) :
    ‖field k (extendDirichlet S hT u hu)‖ = ‖field k u‖ :=
  subdomainZeroExtend_norm hT.measurableSet hTS _

theorem extendDirichlet_pairing (hT : IsOpen T) (hTS : T ⊆ S)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (hu : u ∈ dirichletJetSpace T)
    (v : WeakSobolevJet d 1 (volume.restrict S) S) :
    weakGradientPairing (extendDirichlet S hT u hu) v =
      weakGradientPairing u (restrictSubdomain hTS v) :=
  subdomainZeroExtend_inner hT.measurableSet hTS _ _

theorem extendDirichlet_poisson_test (hS : IsOpen S) (hT : IsOpen T) (hTS : T ⊆ S)
    (u : WeakSobolevJet d 1 (volume.restrict T) T) (hu : u ∈ dirichletJetSpace T)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u (subdomainLp hTS f))
    (φ : SpatialTest T) :
    weakGradientPairing (extendDirichlet S hT u hu) (φ.monoDomain hTS).sobolevJet =
      inner ℝ f ((φ.monoDomain hTS).toLp (volume.restrict S)) := by
  rw [extendDirichlet_pairing hT hTS,φ.restrictSubdomain_mono hT hTS,hf φ]
  have he := congrArg value (extendDirichlet_test hS hT hTS φ)
  rw [extendDirichlet_value,SpatialTest.sobolevJet_value,SpatialTest.sobolevJet_value] at he
  change subdomainZeroExtend S hT.measurableSet (φ.toLp (volume.restrict T)) =
    (φ.monoDomain hTS).toLp (volume.restrict S) at he
  rw [← he]
  calc
    _ = inner ℝ (φ.toLp (volume.restrict T)) (subdomainLp hTS f) := real_inner_comm _ _
    _ = inner ℝ (subdomainZeroExtend S hT.measurableSet (φ.toLp (volume.restrict T))) f :=
      (subdomainZeroExtend_inner hT.measurableSet hTS _ _).symm
    _ = _ := real_inner_comm _ _

end WeakSobolevJet
end Carleman
