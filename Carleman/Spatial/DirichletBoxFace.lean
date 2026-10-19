module

public import Carleman.Spatial.SubdomainContinuity
public import Carleman.Spatial.CoordinateBoxTraceContinuity
public import Carleman.Geometry.ClosedCoordinateFaces

/-! Original global H¹₀ states have zero genuine trace on every local box
face lying outside the open global domain. This follows from the defining
H¹ closure, not from a new boundary condition or a pointwise representative. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates (d+1))}

def subdomainBoxFaceCLM (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hi : a i < b i) (upper : Bool) (hBS : openCoordinateBox a b ⊆ S) :
    WeakSobolevJet (d+1) 1 (volume.restrict S) S →L[ℝ]
      Lp ℝ 2 (volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))) :=
  (weakJetBoxFaceCLM i a b hi upper).comp (WeakSobolevJet.restrictSubdomainCLM hBS)

theorem subdomainBoxFaceCLM_apply (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hi : a i < b i) (upper : Bool) (hBS : openCoordinateBox a b ⊆ S)
    (u : WeakSobolevJet (d+1) 1 (volume.restrict S) S) :
    subdomainBoxFaceCLM i a b hi upper hBS u=
      weakJetBoxFaceLinearMap i a b hi upper (WeakSobolevJet.restrictSubdomain hBS u) := rfl

theorem subdomainBoxFace_test_zero (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hi : a i < b i) (upper : Bool) (hBS : openCoordinateBox a b ⊆ S)
    (hFS : coordinateClosedFace i a b upper ⊆ Sᶜ) (φ : SpatialTest S) :
    subdomainBoxFaceCLM i a b hi upper hBS φ.sobolevJet=0 := by
  apply Lp.ext
  have ht := weakJetBoxFaceTrace_eq_continuous i a b hi upper
    (WeakSobolevJet.restrictSubdomain hBS φ.sobolevJet) φ.value φ.smooth.continuous
    (WeakSobolevJet.restrictSubdomain_test_value_ae hBS φ)
  filter_upwards [ht,Lp.coeFn_zero ℝ 2
    (volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))),
    ae_restrict_mem (openCoordinateBox_isOpen (a ∘ i.succAbove) (b ∘ i.succAbove)).measurableSet]
    with x hx hz hxb
  change weakJetBoxFaceTrace i a b hi upper (WeakSobolevJet.restrictSubdomain hBS φ.sobolevJet) x=_
  rw [hx,hz]
  apply image_eq_zero_of_notMem_tsupport
  intro hsupp
  apply hFS ?_ (φ.support hsupp)
  rw [coordinateClosedFace_eq_image i a b hi upper]
  refine ⟨x,?_,rfl⟩
  intro j
  exact ⟨(hxb j).1.le,(hxb j).2.le⟩

theorem dirichlet_subdomain_box_face_zero (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hi : a i < b i) (upper : Bool) (hBS : openCoordinateBox a b ⊆ S)
    (hFS : coordinateClosedFace i a b upper ⊆ Sᶜ)
    (u : WeakSobolevJet (d+1) 1 (volume.restrict S) S) (hu : u ∈ dirichletJetSpace S) :
    weakJetBoxFaceLinearMap i a b hi upper (WeakSobolevJet.restrictSubdomain hBS u)=0 := by
  let F := subdomainBoxFaceCLM i a b hi upper hBS
  have hk : dirichletJetSpace S ≤ LinearMap.ker F.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨φ,rfl⟩
      exact subdomainBoxFace_test_zero i a b hi upper hBS hFS φ
    · exact F.isClosed_ker
  exact hk hu

end Carleman
