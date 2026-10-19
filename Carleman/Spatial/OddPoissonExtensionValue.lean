module

public import Carleman.Spatial.BoxPoissonExtension
public import Carleman.Spatial.CoordinateOddPart

/-! The actual extension witness retains its global L2 reflection formula. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S T : Set (SpatialCoordinates d)}

theorem zeroExtend_restrict_of_zero_outside (hT : MeasurableSet T)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hu : ∀ᵐ x ∂volume, x ∉ T → u x=0) :
    zeroExtendLp hT (Physical.restrictRegionLp T u)=u := by
  apply Lp.ext
  filter_upwards [zeroExtendLp_ae hT (Physical.restrictRegionLp T u),
    (ae_restrict_iff' hT).mp (Physical.restrictRegionLp_ae T u),hu] with x hx hy hz
  rw [hx]
  by_cases ht : x ∈ T
  · rw [indicator_of_mem ht,hy ht]
  · rw [indicator_of_notMem ht,hz ht]

theorem oddExtendLp_zero_outside (hS : MeasurableSet S)
    (u : Lp ℝ 2 (volume.restrict S)) (r : Fin d) (c : ℝ)
    (hST : S ⊆ T) (hRT : (coordinateReflection r c) ⁻¹' S ⊆ T) :
    ∀ᵐ x ∂volume, x ∉ T → oddExtendLp hS u r c x=0 := by
  filter_upwards [coordinateOddPart_ae r c (zeroExtendLp hS u),zeroExtendLp_ae hS u,
    (coordinateReflection_measurePreserving r c).quasiMeasurePreserving.ae
      (zeroExtendLp_ae hS u)] with x hx hy hz
  intro ht
  change coordinateOddPart r c (zeroExtendLp hS u) x=0
  have hn : x ∉ S := fun h => ht (hST h)
  have hrn : coordinateReflection r c x ∉ S := fun h => ht (hRT h)
  rw [hx,hy,hz,indicator_of_notMem hn,indicator_of_notMem hrn,sub_self]

theorem exists_odd_dirichlet_extension_value (hS : IsOpen S) (hT : IsOpen T)
    (hconv : Convex ℝ S) (hb : Bornology.IsBounded S) (hne : S.Nonempty)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S)
    (f : Lp ℝ 2 (volume.restrict S)) (hf : IsWeakNegativeLaplacian u f)
    (r : Fin d) (c : ℝ) (hST : S ⊆ T) (hRT : (coordinateReflection r c) ⁻¹' S ⊆ T)
    (hdisj : ∀ x ∈ S, coordinateReflection r c x ∉ S)
    (htest : ∀ φ : SpatialTest T, ∀ x ∈ frontier S, (φ.oddReflectionTest r c).value x=0) :
    ∃ v g, IsPoissonExtension hST 2 u f v g ∧
      zeroExtendLp hT.measurableSet (WeakSobolevJet.value v)=
        coordinateOddPart r c (zeroExtendLp hS.measurableSet (WeakSobolevJet.value u)) := by
  let V := WeakSobolevJet.oddExtend hS u hu r c
  let F := oddExtendLp hS.measurableSet f r c
  refine ⟨WeakSobolevJet.restrictDomain T V,Physical.restrictRegionLp T F,?_,?_⟩
  · refine ⟨WeakSobolevJet.oddExtend_mem hS hT u hu r c hST hRT,
      oddExtend_isWeakNegativeLaplacian hS hT hconv hb hne u hu f hf r c htest,?_,?_,?_,?_⟩
    · rw [WeakSobolevJet.restrictSubdomain_restrictDomain]
      exact oddExtend_restrict_original hS u hu r c hdisj
    · exact (Physical.restrictRegionLp_norm_le T F).trans (oddExtendLp_norm_le hS.measurableSet f r c)
    · rw [WeakSobolevJet.restrictDomain_value]
      exact (Physical.restrictRegionLp_norm_le T _).trans (WeakSobolevJet.oddExtend_value_norm_le hS u hu r c)
    · exact (Physical.restrictRegionLp_norm_le T _).trans (WeakSobolevJet.oddExtend_gradient_norm_le hS u hu r c)
  · rw [WeakSobolevJet.restrictDomain_value]
    have he : WeakSobolevJet.value V=oddExtendLp hS.measurableSet (WeakSobolevJet.value u) r c := by
      simp only [V,WeakSobolevJet.oddExtend,map_sub,WeakSobolevJet.reflectCoordinate_value,
        WeakSobolevJet.zeroExtendDirichlet_value,oddExtendLp]
    rw [he,zeroExtend_restrict_of_zero_outside hT.measurableSet _
      (oddExtendLp_zero_outside hS.measurableSet _ r c hST hRT)]
    rfl

end Carleman
