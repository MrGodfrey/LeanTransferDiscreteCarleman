module

public import Carleman.Spatial.OddPoissonExtensionValue

/-! Box reflection witnesses with exact global value formulas. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem exists_lower_box_extension_value (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b))
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d) :
    ∃ v g, IsPoissonExtension (lowerReflectedBox_contains_original a b hpos r) 2 u f v g ∧
      zeroExtendLp (openCoordinateBox_isOpen _ _).measurableSet (WeakSobolevJet.value v)=
        coordinateOddPart r (a r)
          (zeroExtendLp (openCoordinateBox_isOpen a b).measurableSet (WeakSobolevJet.value u)) :=
  exists_odd_dirichlet_extension_value (openCoordinateBox_isOpen a b) (openCoordinateBox_isOpen _ _)
    (openCoordinateBox_convex a b) (openCoordinateBox_isBounded a b)
    (openCoordinateBox_nonempty a b hpos) u hu f hf r (a r)
    (lowerReflectedBox_contains_original a b hpos r) (lowerReflectedBox_contains_reflection a b r)
    (fun _ hx => lowerReflectedBox_no_original_overlap a b r hx) (lowerReflectedBox_test_boundary a b hpos r)

theorem exists_upper_box_extension_value (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b))
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d) :
    ∃ v g, IsPoissonExtension (upperReflectedBox_contains_original a b hpos r) 2 u f v g ∧
      zeroExtendLp (openCoordinateBox_isOpen _ _).measurableSet (WeakSobolevJet.value v)=
        coordinateOddPart r (b r)
          (zeroExtendLp (openCoordinateBox_isOpen a b).measurableSet (WeakSobolevJet.value u)) :=
  exists_odd_dirichlet_extension_value (openCoordinateBox_isOpen a b) (openCoordinateBox_isOpen _ _)
    (openCoordinateBox_convex a b) (openCoordinateBox_isBounded a b)
    (openCoordinateBox_nonempty a b hpos) u hu f hf r (b r)
    (upperReflectedBox_contains_original a b hpos r) (upperReflectedBox_contains_reflection a b r)
    (fun _ hx => upperReflectedBox_no_original_overlap a b r hx) (upperReflectedBox_test_boundary a b hpos r)

end Carleman
