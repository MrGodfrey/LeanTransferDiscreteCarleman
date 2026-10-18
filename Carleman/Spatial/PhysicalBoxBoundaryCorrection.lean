module

public import Carleman.Spatial.PhysicalBoxTraceBounds

/-! Uniform physical-box correction in the actual weighted H¹ error. The
reference finite-dimensional correction is scaled, while the original weak
state and its trace remain on the physical box. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem h1_scaled_value_gradient_add_bound {S : Set (SpatialCoordinates d)}
    (h : ℝ) (hh : 0 ≤ h) (u v : WeakSobolevJet d 1 (volume.restrict S) S) :
    ‖WeakSobolevJet.value (u+v)‖+h*‖WeakSobolevJet.field 1 (u+v)‖ ≤
      (‖WeakSobolevJet.value u‖+h*‖WeakSobolevJet.field 1 u‖)+
        (‖WeakSobolevJet.value v‖+h*‖WeakSobolevJet.field 1 v‖) := by
  rw [map_add,map_add]
  have hg := mul_le_mul_of_nonneg_left (norm_add_le (WeakSobolevJet.field 1 u)
    (WeakSobolevJet.field 1 v)) hh
  linarith [norm_add_le (WeakSobolevJet.value u) (WeakSobolevJet.value v)]

theorem physicalBox_h1_boundary_correction (d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ A > 0, ∀ (a ℓ : Fin (d+1) → ℝ) (hℓ : ∀ i, 0 < ℓ i) (h : ℝ),
      0 < h → (∀ i, h/κ ≤ ℓ i) → (∀ i, ℓ i ≤ κ*h) →
      ∀ J : Finset (Fin (d+1) × Bool),
      ∀ w : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a (fun i => a i+ℓ i)))
        (openCoordinateBox a (fun i => a i+ℓ i)),
      (∀ f ∈ J, weakJetBoxFaceLinearMap f.1 a (fun i => a i+ℓ i)
        (lt_add_of_pos_right _ (hℓ f.1)) f.2 w=0) →
      ∀ p : AffineCoefficients (d+1), ∃ q : AffineCoefficients (d+1),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 a (fun i => a i+ℓ i) f.2,
          affineCoefficientPolynomial q y=0) ∧
        ‖WeakSobolevJet.value (w-affineBoxJet a (fun i => a i+ℓ i) q)‖+
          h*‖WeakSobolevJet.field 1 (w-affineBoxJet a (fun i => a i+ℓ i) q)‖ ≤
          A*(‖WeakSobolevJet.value (w-affineBoxJet a (fun i => a i+ℓ i) p)‖+
            h*‖WeakSobolevJet.field 1 (w-affineBoxJet a (fun i => a i+ℓ i) p)‖) := by
  obtain ⟨C,hC,hcorr⟩ := affineBox_uniform_h1_correction
    (fun _ : Fin (d+1) => 0) (fun _ => 1) (fun _ => zero_lt_one)
  refine ⟨1+2*κ^2*C,by positivity,?_⟩
  intro a ℓ hℓ h hh hlower hupper J w hw p
  let T := affineBoxPullback a ℓ hℓ
  obtain ⟨qr,hqr,herror⟩ := hcorr J (T p)
  let q := T.symm qr
  have hTq : T q=qr := T.apply_symm_apply qr
  refine ⟨q,?_,?_⟩
  · intro f hf
    apply (affineBoxPullback_zero_face_iff f.1 a ℓ hℓ f.2 q).mp
    change ∀ x ∈ coordinateClosedFace f.1 (fun _ => 0) (fun _ => 1) f.2,
      affineCoefficientPolynomial (T q) x=0
    rw [hTq]
    exact hqr f hf
  · have hscale := affineBox_h1_scaling_bound a ℓ hℓ h κ hh hκ hlower (p-q)
    change _ ≤ κ*Real.sqrt (∏ i, ℓ i)*
      (‖affineBoxValueMap (fun _ => 0) (fun _ => 1) (T (p-q))‖+
        ‖affineBoxGradientMap (fun _ => 0) (fun _ => 1) (T (p-q))‖) at hscale
    have hdiff : T (p-q)=T p-qr := by
      rw [map_sub,hTq]
    rw [hdiff] at hscale
    rw [affineBoxJet_value,affineBoxJet_gradient] at herror
    have hscaled := hscale.trans (mul_le_mul_of_nonneg_left herror (by positivity))
    have htrace := physicalBox_selected_reference_trace_bound a ℓ hℓ h κ hh hκ hupper J w hw p
    have hcorrphys :
        ‖WeakSobolevJet.value (affineBoxJet a (fun i => a i+ℓ i) (p-q))‖+
          h*‖WeakSobolevJet.field 1 (affineBoxJet a (fun i => a i+ℓ i) (p-q))‖ ≤
          (2*κ^2*C)*(‖WeakSobolevJet.value (w-affineBoxJet a (fun i => a i+ℓ i) p)‖+
            h*‖WeakSobolevJet.field 1 (w-affineBoxJet a (fun i => a i+ℓ i) p)‖) := by
      rw [affineBoxJet_value,affineBoxJet_gradient]
      calc
        _ ≤ _ := hscaled
        _ = (κ*C)*(Real.sqrt (∏ i, ℓ i)*
          ‖affineBoxSelectedFaceMap (fun _ => 0) (fun _ => 1) (fun _ => zero_lt_one) J (T p)‖) := by ring
        _ ≤ (κ*C)*(2*κ*(‖WeakSobolevJet.value (w-affineBoxJet a (fun i => a i+ℓ i) p)‖+
          h*‖WeakSobolevJet.field 1 (w-affineBoxJet a (fun i => a i+ℓ i) p)‖)) :=
          mul_le_mul_of_nonneg_left htrace (by positivity)
        _ = _ := by ring
    have hj : w-affineBoxJet a (fun i => a i+ℓ i) q =
        (w-affineBoxJet a (fun i => a i+ℓ i) p)+affineBoxJet a (fun i => a i+ℓ i) (p-q) := by
      change w-affineBoxJetLinearMap a (fun i => a i+ℓ i) q =
        (w-affineBoxJetLinearMap a (fun i => a i+ℓ i) p)+affineBoxJetLinearMap a (fun i => a i+ℓ i) (p-q)
      rw [map_sub]
      abel
    rw [hj]
    have ha := h1_scaled_value_gradient_add_bound h hh.le
      (w-affineBoxJet a (fun i => a i+ℓ i) p) (affineBoxJet a (fun i => a i+ℓ i) (p-q))
    nlinarith

end Carleman
