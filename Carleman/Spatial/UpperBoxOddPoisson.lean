module

public import Carleman.Spatial.BoxOddPoisson
public import Carleman.Geometry.UpperReflectedBox

/-! The original weak Dirichlet Poisson solution really extends across a
box face, with the original equation and no assumed reflected test condition. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem upperReflectedBox_test_boundary (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (r : Fin d) (φ : SpatialTest (upperReflectedBox a b r))
    (x : SpatialCoordinates d) (hx : x ∈ frontier (openCoordinateBox a b)) :
    (φ.oddReflectionTest r (b r)).value x=0 := by
  rw [φ.oddReflectionTest_value]
  by_cases hr : x r=b r
  · rw [coordinateReflection_fixed_plane r (b r) hr,sub_self]
  · obtain ⟨h1,h2⟩ := upperReflectedBox_boundary_exclusion a b hpos r hx hr
    rw [image_eq_zero_of_notMem_tsupport (fun h => h1 (φ.support h)),
      image_eq_zero_of_notMem_tsupport (fun h => h2 (φ.support h)),sub_self]

theorem upper_box_odd_poisson (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b))
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d) :
    IsWeakNegativeLaplacian
      (WeakSobolevJet.restrictDomain (upperReflectedBox a b r)
        (WeakSobolevJet.oddExtend (openCoordinateBox_isOpen a b) u hu r (b r)))
      (Physical.restrictRegionLp (upperReflectedBox a b r)
        (oddExtendLp (openCoordinateBox_isOpen a b).measurableSet f r (b r))) :=
  oddExtend_isWeakNegativeLaplacian (openCoordinateBox_isOpen a b) (openCoordinateBox_isOpen _ _)
    (openCoordinateBox_convex a b) (openCoordinateBox_isBounded a b)
    (openCoordinateBox_nonempty a b hpos) u hu f hf r (b r) (upperReflectedBox_test_boundary a b hpos r)

theorem upper_box_odd_restrict (a b : Fin d → ℝ)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b)) (r : Fin d) :
    WeakSobolevJet.restrictDomain (openCoordinateBox a b)
      (WeakSobolevJet.oddExtend (openCoordinateBox_isOpen a b) u hu r (b r))=u :=
  oddExtend_restrict_original (openCoordinateBox_isOpen a b) u hu r (b r)
    (fun _ hx => upperReflectedBox_no_original_overlap a b r hx)

theorem upper_box_odd_dirichlet (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b)) (r : Fin d) :
    WeakSobolevJet.restrictDomain (upperReflectedBox a b r)
      (WeakSobolevJet.oddExtend (openCoordinateBox_isOpen a b) u hu r (b r)) ∈
        dirichletJetSpace (upperReflectedBox a b r) :=
  WeakSobolevJet.oddExtend_mem (openCoordinateBox_isOpen a b) (openCoordinateBox_isOpen _ _) u hu r (b r)
    (upperReflectedBox_contains_original a b hpos r) (upperReflectedBox_contains_reflection a b r)

end Carleman
