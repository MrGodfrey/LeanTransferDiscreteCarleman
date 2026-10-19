module

public import Carleman.Spatial.DirichletLocalAffine
public import Carleman.Spatial.LocalWeightedNorm

/-! Local weighted boundary approximation for every original H²∩H¹₀ state.
Only the actual positive local weight comparison enters; the anchor cancels. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman

theorem weighted_dirichlet_h2_local_boundary_affine (d : ℕ) (κ W : ℝ) (hκ : 1 ≤ κ) (hW : 0 < W) :
    ∃ C > 0, ∀ (S : Set (SpatialCoordinates (d+1))), IsOpen S →
      ∀ (a b : Fin (d+1) → ℝ) (_hpos : ∀ i, a i < b i) (hBS : openCoordinateBox a b ⊆ S) (h : ℝ),
      0 < h → (∀ i, h/κ ≤ b i-a i) → (∀ i, b i-a i ≤ κ*h) →
      ∀ J : Finset (Fin (d+1) × Bool),
      (∀ f ∈ J, coordinateClosedFace f.1 a b f.2 ⊆ frontier S) →
      ∀ (w : BoundedMultiplier (volume.restrict S)) (s : ℝ), 0 < s →
      (∀ᵐ x ∂volume.restrict (openCoordinateBox a b), |w.value x| ≤ W*s ∧ s ≤ W*|w.value x|) →
      ∀ u : WeakSobolevJet (d+1) 2 (volume.restrict S) S,
      WeakSobolevJet.value u ∈ dirichletSubspace S →
      ∃ (p : SpatialCoordinates (d+1) →ᵃ[ℝ] ℝ)
        (r : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a b f.2, p y=0) ∧
        (WeakSobolevJet.value r =ᵐ[volume.restrict (openCoordinateBox a b)]
          (fun x => WeakSobolevJet.value u x-p x)) ∧
        (w.onSubdomain hBS).seminorm (WeakSobolevJet.value r)+
          h*(w.onSubdomain hBS).seminorm (WeakSobolevJet.field 1 r) ≤
          C*h^2*‖subdomainLp hBS (w.map (WeakSobolevJet.field 2 u))‖ := by
  obtain ⟨B,hB,hbound⟩ := dirichlet_h2_local_boundary_affine d κ hκ
  refine ⟨W^2*B,by positivity,?_⟩
  intro S hS a b hpos hBS h hh hlower hupper J hfaces w s hs hw u hu
  obtain ⟨p,r,hp,hr,he⟩ := hbound S hS a b hpos hBS h hh hlower hupper J hfaces u hu
  refine ⟨p,r,hp,hr,?_⟩
  have hw1 : ∀ᵐ x ∂volume.restrict (openCoordinateBox a b), |(w.onSubdomain hBS).value x| ≤ W*s :=
    hw.mono fun _ hx => hx.1
  have hw2 : ∀ᵐ x ∂volume.restrict (openCoordinateBox a b), s ≤ W*|(w.onSubdomain hBS).value x| :=
    hw.mono fun _ hx => hx.2
  have hv := (w.onSubdomain hBS).seminorm_le_anchor W s hw1 (WeakSobolevJet.value r)
  have hg := mul_le_mul_of_nonneg_left
    ((w.onSubdomain hBS).seminorm_le_anchor W s hw1 (WeakSobolevJet.field 1 r)) hh.le
  have hH := (w.onSubdomain hBS).norm_le_seminorm_anchor W s hs hw2
    (subdomainLp hBS (WeakSobolevJet.field 2 u))
  rw [BoundedMultiplier.onSubdomain_seminorm] at hH
  calc
    _ ≤ W*s*(‖WeakSobolevJet.value r‖+h*‖WeakSobolevJet.field 1 r‖) := by nlinarith only [hv,hg]
    _ ≤ W*s*(B*h^2*‖subdomainLp hBS (WeakSobolevJet.field 2 u)‖) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ W*s*(B*h^2*((W/s)*‖subdomainLp hBS (w.map (WeakSobolevJet.field 2 u))‖)) := by gcongr
    _ = _ := by field_simp

end Carleman
