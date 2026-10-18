module

public import Carleman.Spatial.PhysicalBoxH2Affine
public import Carleman.Spatial.AffineCornerKernel

/-! Boundary-preserving affine approximation on physical boxes for every
original weak H² state. The constant is uniform in location, h, all side lengths
within the comparability bound, every face subset, and every state. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman

theorem physicalBox_h2_boundary_affine (d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > 0, ∀ (a ℓ : Fin (d+1) → ℝ) (hℓ : ∀ i, 0 < ℓ i) (h : ℝ),
      0 < h → (∀ i, h/κ ≤ ℓ i) → (∀ i, ℓ i ≤ κ*h) →
      ∀ J : Finset (Fin (d+1) × Bool),
      ∀ u : WeakSobolevJet (d+1) 2 (volume.restrict (openCoordinateBox a (fun i => a i+ℓ i)))
        (openCoordinateBox a (fun i => a i+ℓ i)),
      (∀ f ∈ J, weakJetBoxFaceLinearMap f.1 a (fun i => a i+ℓ i)
        (lt_add_of_pos_right _ (hℓ f.1)) f.2 (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u)=0) →
      ∃ q : AffineCoefficients (d+1),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a (fun i => a i+ℓ i) f.2,
          affineCoefficientPolynomial q y=0) ∧
        ‖WeakSobolevJet.value (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
          affineBoxJet a (fun i => a i+ℓ i) q)‖+
          h*‖WeakSobolevJet.field 1 (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
            affineBoxJet a (fun i => a i+ℓ i) q)‖ ≤ C*h^2*‖WeakSobolevJet.field 2 u‖ := by
  obtain ⟨A,hA,hcorr⟩ := physicalBox_h1_boundary_correction d κ hκ
  obtain ⟨B,hB,happrox⟩ := physicalBox_h2_affine_approximation d κ hκ
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro a ℓ hℓ h hh hlower hupper J u hu
  obtain ⟨p,hp⟩ := happrox a ℓ hℓ h hh hupper u
  obtain ⟨q,hq,he⟩ := hcorr a ℓ hℓ h hh hlower hupper J
    (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u) hu p
  refine ⟨q,hq,he.trans ?_⟩
  calc
    _ ≤ A*(B*h^2*‖WeakSobolevJet.field 2 u‖) := mul_le_mul_of_nonneg_left hp hA.le
    _ = _ := by ring

theorem physicalBox_h2_boundary_affine_actual (d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > 0, ∀ (a ℓ : Fin (d+1) → ℝ) (hℓ : ∀ i, 0 < ℓ i) (h : ℝ),
      0 < h → (∀ i, h/κ ≤ ℓ i) → (∀ i, ℓ i ≤ κ*h) →
      ∀ J : Finset (Fin (d+1) × Bool),
      ∀ u : WeakSobolevJet (d+1) 2 (volume.restrict (openCoordinateBox a (fun i => a i+ℓ i)))
        (openCoordinateBox a (fun i => a i+ℓ i)),
      (∀ f ∈ J, weakJetBoxFaceLinearMap f.1 a (fun i => a i+ℓ i)
        (lt_add_of_pos_right _ (hℓ f.1)) f.2 (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u)=0) →
      ∃ (p : SpatialCoordinates (d+1) →ᵃ[ℝ] ℝ)
        (r : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a (fun i => a i+ℓ i)))
          (openCoordinateBox a (fun i => a i+ℓ i))),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a (fun i => a i+ℓ i) f.2, p y=0) ∧
        (WeakSobolevJet.value r =ᵐ[volume.restrict (openCoordinateBox a (fun i => a i+ℓ i))]
          (fun x => WeakSobolevJet.value u x-p x)) ∧
        ‖WeakSobolevJet.value r‖+h*‖WeakSobolevJet.field 1 r‖ ≤ C*h^2*‖WeakSobolevJet.field 2 u‖ := by
  obtain ⟨C,hC,hbound⟩ := physicalBox_h2_boundary_affine d κ hκ
  refine ⟨C,hC,?_⟩
  intro a ℓ hℓ h hh hlower hupper J u hu
  obtain ⟨q,hq,he⟩ := hbound a ℓ hℓ h hh hlower hupper J u hu
  refine ⟨affineCoefficientPolynomial q,
    WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-affineBoxJet a (fun i => a i+ℓ i) q,hq,?_,he⟩
  rw [map_sub,WeakSobolevJet.truncate_value,affineBoxJet_value]
  filter_upwards [Lp.coeFn_sub (WeakSobolevJet.value u) (affineBoxValueMap a (fun i => a i+ℓ i) q),
    affineBoxValueMap_ae a (fun i => a i+ℓ i) q] with x hx hqae
  rw [hx,Pi.sub_apply,hqae]

theorem physicalBox_h2_corner_bound (d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ C > 0, ∀ (a ℓ : Fin (d+1) → ℝ) (hℓ : ∀ i, 0 < ℓ i) (h : ℝ),
      0 < h → (∀ i, h/κ ≤ ℓ i) → (∀ i, ℓ i ≤ κ*h) →
      ∀ (i j : Fin (d+1)), i ≠ j → ∀ (ui uj : Bool),
      ∀ u : WeakSobolevJet (d+1) 2 (volume.restrict (openCoordinateBox a (fun k => a k+ℓ k)))
        (openCoordinateBox a (fun k => a k+ℓ k)),
      weakJetBoxFaceLinearMap i a (fun k => a k+ℓ k) (lt_add_of_pos_right _ (hℓ i)) ui
        (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u)=0 →
      weakJetBoxFaceLinearMap j a (fun k => a k+ℓ k) (lt_add_of_pos_right _ (hℓ j)) uj
        (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u)=0 →
      ‖WeakSobolevJet.value u‖+h*‖WeakSobolevJet.field 1 u‖ ≤ C*h^2*‖WeakSobolevJet.field 2 u‖ := by
  classical
  obtain ⟨C,hC,hbound⟩ := physicalBox_h2_boundary_affine d κ hκ
  refine ⟨C,hC,?_⟩
  intro a ℓ hℓ h hh hlower hupper i j hij ui uj u hi hj
  have hz : ∀ f ∈ ({(i,ui),(j,uj)} : Finset (Fin (d+1) × Bool)),
      weakJetBoxFaceLinearMap f.1 a (fun k => a k+ℓ k) (lt_add_of_pos_right _ (hℓ f.1)) f.2
        (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u)=0 := by
    intro f hf
    simp only [Finset.mem_insert,Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact hi
    · exact hj
  obtain ⟨q,hq,he⟩ := hbound a ℓ hℓ h hh hlower hupper {(i,ui),(j,uj)} u hz
  have hq0 := physicalBox_two_faces_affine_zero i j hij a ℓ hℓ ui uj q
    (hq (i,ui) (by simp)) (hq (j,uj) (by simp))
  have hj0 : affineBoxJet a (fun k => a k+ℓ k) q=0 := by
    rw [hq0,← affineBoxJetLinearMap_apply]
    exact map_zero _
  rw [hj0,sub_zero] at he
  exact he

end Carleman
