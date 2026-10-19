module

public import Carleman.Spatial.DirichletBoxFace
public import Carleman.Spatial.BoundaryAffineLemma

/-! Apply the genuine boundary-affine lemma to every global H²∩H¹₀ state
on local physical boxes. Local boundary traces are discharged from the global
Dirichlet closure, and the Hessian norm is the actual local restriction. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman

theorem WeakSobolevJet.restrictSubdomain_truncate {d m n : ℕ}
    {S T : Set (SpatialCoordinates d)} (hTS : T ⊆ S) (hmn : m ≤ n)
    (u : WeakSobolevJet d n (volume.restrict S) S) :
    restrictSubdomain hTS (truncate hmn u)=truncate hmn (restrictSubdomain hTS u) := rfl

theorem dirichlet_h2_local_boundary_affine (d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > 0, ∀ (S : Set (SpatialCoordinates (d+1))), IsOpen S →
      ∀ (a b : Fin (d+1) → ℝ) (_hpos : ∀ i, a i < b i) (hBS : openCoordinateBox a b ⊆ S) (h : ℝ),
      0 < h → (∀ i, h/κ ≤ b i-a i) → (∀ i, b i-a i ≤ κ*h) →
      ∀ J : Finset (Fin (d+1) × Bool),
      (∀ f ∈ J, coordinateClosedFace f.1 a b f.2 ⊆ frontier S) →
      ∀ u : WeakSobolevJet (d+1) 2 (volume.restrict S) S,
      WeakSobolevJet.value u ∈ dirichletSubspace S →
      ∃ (p : SpatialCoordinates (d+1) →ᵃ[ℝ] ℝ)
        (r : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a b f.2, p y=0) ∧
        (WeakSobolevJet.value r =ᵐ[volume.restrict (openCoordinateBox a b)]
          (fun x => WeakSobolevJet.value u x-p x)) ∧
        ‖WeakSobolevJet.value r‖+h*‖WeakSobolevJet.field 1 r‖ ≤
          C*h^2*‖subdomainLp hBS (WeakSobolevJet.field 2 u)‖ := by
  obtain ⟨C,hC,hbound⟩ := OriginalForm.boundary_affine_lemma d κ hκ
  refine ⟨C,hC,?_⟩
  intro S hS a b hpos hBS h hh hlower hupper J hfaces u hu
  have hu1 : WeakSobolevJet.truncate (by decide : 1 ≤ 2) u ∈ dirichletJetSpace S := by
    apply (mem_dirichletJetSpace_iff S hS _).mpr
    exact hu
  have htrace : ∀ f ∈ J, weakJetBoxFaceLinearMap f.1 a b (hpos f.1) f.2
      (WeakSobolevJet.truncate (by decide : 1 ≤ 2) (WeakSobolevJet.restrictSubdomain hBS u))=0 := by
    intro f hf
    have hz := dirichlet_subdomain_box_face_zero f.1 a b (hpos f.1) f.2 hBS
      (fun x hx => Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hS) (hfaces f hf hx))
      (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u) hu1
    rwa [WeakSobolevJet.restrictSubdomain_truncate] at hz
  obtain ⟨p,r,hp,hr,he⟩ := hbound a b hpos h hh hlower hupper J
    (WeakSobolevJet.restrictSubdomain hBS u) htrace
  refine ⟨p,r,hp,?_,he⟩
  rw [WeakSobolevJet.restrictSubdomain_value] at hr
  filter_upwards [hr,subdomainLp_ae hBS (WeakSobolevJet.value u)] with x hx hu
  rw [hx,hu]

end Carleman
