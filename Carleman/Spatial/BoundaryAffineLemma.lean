module

public import Carleman.Spatial.PhysicalBoxBoundaryAffine

/-! Appendix B, Lemma B.1: all weak H² states on an arbitrary coordinate
box, with actual zero traces on any selected physical faces. The h² constant
is chosen before the box, mesh size, face set, and state. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman.OriginalForm

theorem boundary_affine_lemma (d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > 0, ∀ (a b : Fin (d+1) → ℝ) (hpos : ∀ i, a i < b i) (h : ℝ),
      0 < h → (∀ i, h/κ ≤ b i-a i) → (∀ i, b i-a i ≤ κ*h) →
      ∀ J : Finset (Fin (d+1) × Bool),
      ∀ u : WeakSobolevJet (d+1) 2 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b),
      (∀ f ∈ J, weakJetBoxFaceLinearMap f.1 a b (hpos f.1) f.2
        (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u)=0) →
      ∃ (p : SpatialCoordinates (d+1) →ᵃ[ℝ] ℝ)
        (r : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a b f.2, p y=0) ∧
        (WeakSobolevJet.value r =ᵐ[volume.restrict (openCoordinateBox a b)]
          (fun x => WeakSobolevJet.value u x-p x)) ∧
        ‖WeakSobolevJet.value r‖+h*‖WeakSobolevJet.field 1 r‖ ≤ C*h^2*‖WeakSobolevJet.field 2 u‖ := by
  obtain ⟨C,hC,hbound⟩ := physicalBox_h2_boundary_affine_actual d κ hκ
  refine ⟨C,hC,?_⟩
  intro a b hpos h hh hlower hupper
  let ℓ : Fin (d+1) → ℝ := fun i => b i-a i
  have hb : b=(fun i => a i+ℓ i) := by funext i; dsimp [ℓ]; ring
  have hℓ : ∀ i, 0 < ℓ i := fun i => sub_pos.mpr (hpos i)
  have hl : ∀ i, h/κ ≤ ℓ i := hlower
  have hu : ∀ i, ℓ i ≤ κ*h := hupper
  clear_value ℓ
  subst b
  exact hbound a ℓ hℓ h hh hl hu

end Carleman.OriginalForm
