module

public import Carleman.Spatial.FirstWeakProduct
public import Carleman.Spatial.DirichletSpace
public import Carleman.Spatial.IntrinsicMultipliers

/-! Smooth bounded multiplication preserves the actual H¹₀ closure, by
continuity in the weak H¹ graph topology and genuine compact test products. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem clm_mem_closed_span {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (A : Set E) (hP : ∀ x ∈ A, P x ∈ Submodule.span ℝ A)
    (u : E) (hu : u ∈ (Submodule.span ℝ A).topologicalClosure) :
    P u ∈ (Submodule.span ℝ A).topologicalClosure := by
  have hspan : (Submodule.span ℝ A).map P.toLinearMap ≤ Submodule.span ℝ A :=
    Submodule.map_le_iff_le_comap.mpr (Submodule.span_le.mpr hP)
  exact ((Submodule.topologicalClosure_map P (Submodule.span ℝ A)).trans
    (Submodule.topologicalClosure_mono hspan)) ⟨u,hu,rfl⟩

theorem weakFirstProductCLM_test (hS : IsOpen S)
    (w : BoundedMultiplier (volume.restrict S)) (dw : Fin d → BoundedMultiplier (volume.restrict S))
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : ∀ i, (dw i).value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (φ : SpatialTest S) :
    weakFirstProductCLM hS (ae_restrict_mem hS.measurableSet) w dw hw hdw φ.sobolevJet =
      (φ.mulOn hS hw).sobolevJet := by
  apply WeakSobolevJet.value_injective hS (ae_restrict_mem hS.measurableSet)
  rw [SpatialTest.sobolevJet_value,SpatialTest.mulOn_toLp]
  exact (weakFirstProduct_value hS (ae_restrict_mem hS.measurableSet) w dw hw hdw φ.sobolevJet).trans
    (congrArg w.map φ.sobolevJet_value)

theorem weakFirstProductCLM_mem_dirichlet (hS : IsOpen S)
    (w : BoundedMultiplier (volume.restrict S)) (dw : Fin d → BoundedMultiplier (volume.restrict S))
    (hw : ContDiffOn ℝ ∞ w.value S)
    (hdw : ∀ i, (dw i).value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)))
    (u : WeakSobolevJet d 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S) :
    weakFirstProductCLM hS (ae_restrict_mem hS.measurableSet) w dw hw hdw u ∈ dirichletJetSpace S := by
  apply clm_mem_closed_span (weakFirstProductCLM hS (ae_restrict_mem hS.measurableSet) w dw hw hdw)
    (Set.range (fun φ : SpatialTest S => φ.sobolevJet)) _ u hu
  rintro _ ⟨φ,rfl⟩
  rw [weakFirstProductCLM_test hS w dw hw hdw]
  exact Submodule.subset_span (Set.mem_range_self (φ.mulOn hS hw))

theorem boundedSmooth_map_mem_dirichlet (hS : IsOpen S)
    (w : BoundedMultiplier (volume.restrict S)) (hw : BoundedSmoothOn w.value S)
    (u : Lp ℝ 2 (volume.restrict S)) (hu : u ∈ dirichletSubspace S) :
    w.map u ∈ dirichletSubspace S := by
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  let dw := fun i => intrinsicWordMultiplier hS hν hw [i]
  have hdw (i : Fin d) : (dw i).value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i)) := by
    change wordDerivative [i] w.value =ᵐ[volume.restrict S]
      (fun x => fderiv ℝ w.value x (EuclideanSpace.basisFun (Fin d) ℝ i))
    simpa only [intrinsicWordMultiplier,wordDerivative_nil] using
      intrinsicWordMultiplier_derivative hS hν hw [] i
  obtain ⟨v,hv,rfl⟩ := hu
  refine ⟨weakFirstProductCLM hS hν w dw hw.1 hdw v,
    weakFirstProductCLM_mem_dirichlet hS w dw hw.1 hdw v hv,?_⟩
  exact weakFirstProduct_value hS hν w dw hw.1 hdw v

end Carleman
