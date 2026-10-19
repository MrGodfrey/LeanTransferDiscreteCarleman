module

public import Carleman.Spatial.UpperBoxOddPoisson
public import Carleman.Spatial.OddReflectionBounds
public import Carleman.Spatial.SubdomainComposition

/-! Quantified original weak Dirichlet extensions, including exact recovery
and uniform bounds for the original value, gradient and right-hand side. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

def IsPoissonExtension (hST : S ⊆ T) (C : ℝ)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (f : Lp ℝ 2 (volume.restrict S))
    (v : WeakSobolevJet d 1 (volume.restrict T) T) (g : Lp ℝ 2 (volume.restrict T)) : Prop :=
  v ∈ dirichletJetSpace T ∧ IsWeakNegativeLaplacian v g ∧
  WeakSobolevJet.restrictSubdomain hST v=u ∧ ‖g‖ ≤ C*‖f‖ ∧
  ‖WeakSobolevJet.value v‖ ≤ C*‖WeakSobolevJet.value u‖ ∧
  ‖WeakSobolevJet.field 1 v‖ ≤ C*‖WeakSobolevJet.field 1 u‖

theorem exists_odd_dirichlet_extension (hS : IsOpen S) (hT : IsOpen T)
    (hconv : Convex ℝ S) (hb : Bornology.IsBounded S) (hne : S.Nonempty)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d) (c : ℝ) (hST : S ⊆ T) (hRT : (coordinateReflection r c) ⁻¹' S ⊆ T)
    (hdisj : ∀ x ∈ S, coordinateReflection r c x ∉ S)
    (htest : ∀ φ : SpatialTest T, ∀ x ∈ frontier S, (φ.oddReflectionTest r c).value x=0) :
    ∃ v g, IsPoissonExtension hST 2 u f v g := by
  let V := WeakSobolevJet.oddExtend hS u hu r c
  let F := oddExtendLp hS.measurableSet f r c
  refine ⟨WeakSobolevJet.restrictDomain T V,Physical.restrictRegionLp T F,
    WeakSobolevJet.oddExtend_mem hS hT u hu r c hST hRT,
    oddExtend_isWeakNegativeLaplacian hS hT hconv hb hne u hu f hf r c htest,?_,?_,?_,?_⟩
  · rw [WeakSobolevJet.restrictSubdomain_restrictDomain]
    exact oddExtend_restrict_original hS u hu r c hdisj
  · exact (Physical.restrictRegionLp_norm_le T F).trans (oddExtendLp_norm_le hS.measurableSet f r c)
  · rw [WeakSobolevJet.restrictDomain_value]
    exact (Physical.restrictRegionLp_norm_le T _).trans (WeakSobolevJet.oddExtend_value_norm_le hS u hu r c)
  · exact (Physical.restrictRegionLp_norm_le T _).trans (WeakSobolevJet.oddExtend_gradient_norm_le hS u hu r c)

theorem exists_lower_box_extension (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b))
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d) :
    ∃ v g, IsPoissonExtension (lowerReflectedBox_contains_original a b hpos r) 2 u f v g :=
  exists_odd_dirichlet_extension (openCoordinateBox_isOpen a b) (openCoordinateBox_isOpen _ _)
    (openCoordinateBox_convex a b) (openCoordinateBox_isBounded a b)
    (openCoordinateBox_nonempty a b hpos) u hu f hf r (a r)
    (lowerReflectedBox_contains_original a b hpos r) (lowerReflectedBox_contains_reflection a b r)
    (fun _ hx => lowerReflectedBox_no_original_overlap a b r hx) (lowerReflectedBox_test_boundary a b hpos r)

theorem exists_upper_box_extension (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b))
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d) :
    ∃ v g, IsPoissonExtension (upperReflectedBox_contains_original a b hpos r) 2 u f v g :=
  exists_odd_dirichlet_extension (openCoordinateBox_isOpen a b) (openCoordinateBox_isOpen _ _)
    (openCoordinateBox_convex a b) (openCoordinateBox_isBounded a b)
    (openCoordinateBox_nonempty a b hpos) u hu f hf r (b r)
    (upperReflectedBox_contains_original a b hpos r) (upperReflectedBox_contains_reflection a b r)
    (fun _ hx => upperReflectedBox_no_original_overlap a b r hx) (upperReflectedBox_test_boundary a b hpos r)

end Carleman
