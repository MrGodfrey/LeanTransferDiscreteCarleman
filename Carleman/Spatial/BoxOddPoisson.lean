module

public import Carleman.Spatial.OddReflectionDirichlet
public import Carleman.Geometry.LowerReflectedBox

/-! The original weak Dirichlet Poisson solution really extends across a
box face, with the original equation and no assumed reflected test condition. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem lowerReflectedBox_test_boundary (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (r : Fin d) (φ : SpatialTest (lowerReflectedBox a b r))
    (x : SpatialCoordinates d) (hx : x ∈ frontier (openCoordinateBox a b)) :
    (φ.oddReflectionTest r (a r)).value x=0 := by
  rw [φ.oddReflectionTest_value]
  by_cases hr : x r=a r
  · rw [coordinateReflection_fixed_plane r (a r) hr,sub_self]
  · obtain ⟨h1,h2⟩ := lowerReflectedBox_boundary_exclusion a b hpos r hx hr
    rw [image_eq_zero_of_notMem_tsupport (fun h => h1 (φ.support h)),
      image_eq_zero_of_notMem_tsupport (fun h => h2 (φ.support h)),sub_self]

theorem lower_box_odd_poisson (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b))
    (f : Lp ℝ 2 (volume.restrict (openCoordinateBox a b))) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d) :
    IsWeakNegativeLaplacian
      (WeakSobolevJet.restrictDomain (lowerReflectedBox a b r)
        (WeakSobolevJet.oddExtend (openCoordinateBox_isOpen a b) u hu r (a r)))
      (Physical.restrictRegionLp (lowerReflectedBox a b r)
        (oddExtendLp (openCoordinateBox_isOpen a b).measurableSet f r (a r))) :=
  oddExtend_isWeakNegativeLaplacian (openCoordinateBox_isOpen a b) (openCoordinateBox_isOpen _ _)
    (openCoordinateBox_convex a b) (openCoordinateBox_isBounded a b)
    (openCoordinateBox_nonempty a b hpos) u hu f hf r (a r) (lowerReflectedBox_test_boundary a b hpos r)

theorem oddExtend_restrict_original {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (r : Fin d) (c : ℝ) (hdisj : ∀ x ∈ S, coordinateReflection r c x ∉ S) :
    WeakSobolevJet.restrictDomain S (WeakSobolevJet.oddExtend hS u hu r c)=u := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [WeakSobolevJet.restrictDomain_value,WeakSobolevJet.oddExtend,map_sub,
    WeakSobolevJet.reflectCoordinate_value,WeakSobolevJet.zeroExtendDirichlet_value]
  apply Lp.ext
  filter_upwards [Physical.restrictRegionLp_ae S
    (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)-
      coordinateReflectionLp r c (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u))),
    zeroExtendLp_ae_restrict hS.measurableSet
    (WeakSobolevJet.value u),
    (Lp.coeFn_sub (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u))
      (coordinateReflectionLp r c (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)))).filter_mono ae_restrict_le,
    (coordinateReflectionLp_ae r c (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u))).filter_mono ae_restrict_le,
    ((coordinateReflection_measurePreserving r c).quasiMeasurePreserving.ae
      (zeroExtendLp_ae hS.measurableSet (WeakSobolevJet.value u))).filter_mono ae_restrict_le,
    ae_restrict_mem hS.measurableSet] with x h1 h2 h3 h4 h5 hx
  rw [h1,h3,Pi.sub_apply,h2,h4,Function.comp_apply,h5,indicator_of_notMem (hdisj x hx),sub_zero]

theorem lower_box_odd_restrict (a b : Fin d → ℝ)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b)) (r : Fin d) :
    WeakSobolevJet.restrictDomain (openCoordinateBox a b)
      (WeakSobolevJet.oddExtend (openCoordinateBox_isOpen a b) u hu r (a r))=u :=
  oddExtend_restrict_original (openCoordinateBox_isOpen a b) u hu r (a r)
    (fun _ hx => lowerReflectedBox_no_original_overlap a b r hx)

theorem lower_box_odd_dirichlet (a b : Fin d → ℝ) (hpos : ∀ j, a j < b j)
    (u : WeakSobolevJet d 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (hu : u ∈ dirichletJetSpace (openCoordinateBox a b)) (r : Fin d) :
    WeakSobolevJet.restrictDomain (lowerReflectedBox a b r)
      (WeakSobolevJet.oddExtend (openCoordinateBox_isOpen a b) u hu r (a r)) ∈
        dirichletJetSpace (lowerReflectedBox a b r) :=
  WeakSobolevJet.oddExtend_mem (openCoordinateBox_isOpen a b) (openCoordinateBox_isOpen _ _) u hu r (a r)
    (lowerReflectedBox_contains_original a b hpos r) (lowerReflectedBox_contains_reflection a b r)

end Carleman
