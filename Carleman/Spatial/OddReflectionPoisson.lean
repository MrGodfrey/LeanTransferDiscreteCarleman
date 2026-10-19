module

public import Carleman.Spatial.FullSpaceTestPairing

/-! Odd reflection of the original weak Dirichlet solution satisfies the
reflected equation wherever the actual odd tests vanish on the old boundary. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

def WeakSobolevJet.oddExtend (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (r : Fin d) (c : ℝ) : WeakSobolevJet d 1 volume univ :=
  zeroExtendDirichlet hS u hu-reflectCoordinate r c (zeroExtendDirichlet hS u hu)

def oddExtendLp (hS : MeasurableSet S) (f : Lp ℝ 2 (volume.restrict S))
    (r : Fin d) (c : ℝ) : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) :=
  zeroExtendLp hS f-coordinateReflectionLp r c (zeroExtendLp hS f)

theorem oddExtend_poisson_full_test (hS : IsOpen S) (hconv : Convex ℝ S)
    (hb : Bornology.IsBounded S) (hne : S.Nonempty)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d) (c : ℝ) (φ : SpatialTest T)
    (hzero : ∀ x ∈ frontier S, (φ.oddReflectionTest r c).value x=0) :
    weakGradientPairing (WeakSobolevJet.oddExtend hS u hu r c) φ.fullJet=
      inner ℝ (oddExtendLp hS.measurableSet f r c) (WeakSobolevJet.value φ.fullJet) := by
  have htest := (φ.oddReflectionTest r c).fullJet_boundary_mem hS hconv hb hne hzero
  have hp := (isWeakNegativeLaplacian_iff_dirichlet hS u f).mp hf _ htest
  have he : weakGradientPairing (WeakSobolevJet.oddExtend hS u hu r c) φ.fullJet=
      weakGradientPairing u (WeakSobolevJet.restrictDomain S (φ.oddReflectionTest r c).fullJet) := by
    rw [WeakSobolevJet.oddExtend,map_sub,sub_apply,
      WeakSobolevJet.reflectCoordinate_gradient_adjoint,← map_sub,
      ← φ.oddReflectionTest_fullJet,WeakSobolevJet.zeroExtendDirichlet_pairing]
  rw [he,hp,WeakSobolevJet.restrictDomain_value,← zeroExtendLp_inner hS.measurableSet,
    φ.oddReflectionTest_fullJet,map_sub,WeakSobolevJet.reflectCoordinate_value,
    inner_sub_right,oddExtendLp,inner_sub_left,coordinateReflectionLp_inner]

theorem oddExtend_isWeakNegativeLaplacian (hS : IsOpen S) (hT : IsOpen T)
    (hconv : Convex ℝ S) (hb : Bornology.IsBounded S) (hne : S.Nonempty)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d) (c : ℝ)
    (htest : ∀ φ : SpatialTest T, ∀ x ∈ frontier S, (φ.oddReflectionTest r c).value x=0) :
    IsWeakNegativeLaplacian (WeakSobolevJet.restrictDomain T (WeakSobolevJet.oddExtend hS u hu r c))
      (Physical.restrictRegionLp T (oddExtendLp hS.measurableSet f r c)) := by
  intro φ
  rw [← φ.fullJet_pairing hT,← φ.fullJet_inner hT]
  exact oddExtend_poisson_full_test hS hconv hb hne u hu f hf r c φ (htest φ)

end Carleman
