module

public import Carleman.Spatial.AffineBoxNormScaling
public import Carleman.Spatial.AffineJetTraceIdentities

/-! Scale-consistent bounds for the actual weak face traces of every H¹ state.
Only the real physical side length enters the trace bound. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem physicalBox_weak_face_scaled_bound (i : Fin (d+1)) (a ℓ : Fin (d+1) → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) (upper : Bool)
    (w : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a (fun j => a j+ℓ j)))
      (openCoordinateBox a (fun j => a j+ℓ j))) :
    Real.sqrt (ℓ i)*‖weakJetBoxFaceLinearMap i a (fun j => a j+ℓ j)
      (lt_add_of_pos_right _ (hℓ i)) upper w‖ ≤
      2*(‖WeakSobolevJet.value w‖+ℓ i*‖WeakSobolevJet.field 1 w‖) := by
  have hi := hℓ i
  have ht := weakJetBoxFaceTrace_norm_sq i a (fun j => a j+ℓ j)
    (lt_add_of_pos_right _ (hℓ i)) upper w
  change ‖weakJetBoxFaceLinearMap i a (fun j => a j+ℓ j)
    (lt_add_of_pos_right _ (hℓ i)) upper w‖^2 ≤ _ at ht
  simp only [add_sub_cancel_left] at ht
  have h := mul_le_mul_of_nonneg_left ht (hℓ i).le
  have hs : ℓ i*(2/ℓ i)=(2:ℝ) := by field_simp [(hℓ i).ne']
  rw [mul_add,← mul_assoc,hs] at h
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (hℓ i).le]
  nlinarith [sq_nonneg (‖WeakSobolevJet.value w‖),
    sq_nonneg (ℓ i*‖WeakSobolevJet.field 1 w‖),
    mul_nonneg (norm_nonneg (WeakSobolevJet.value w))
      (mul_nonneg (hℓ i).le (norm_nonneg (WeakSobolevJet.field 1 w)))]

theorem physicalBox_weak_face_uniform_bound (i : Fin (d+1)) (a ℓ : Fin (d+1) → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) (upper : Bool) (h κ : ℝ) (_hh : 0 < h) (hκ : 1 ≤ κ)
    (hupper : ℓ i ≤ κ*h)
    (w : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a (fun j => a j+ℓ j)))
      (openCoordinateBox a (fun j => a j+ℓ j))) :
    Real.sqrt (ℓ i)*‖weakJetBoxFaceLinearMap i a (fun j => a j+ℓ j)
      (lt_add_of_pos_right _ (hℓ i)) upper w‖ ≤
      2*κ*(‖WeakSobolevJet.value w‖+h*‖WeakSobolevJet.field 1 w‖) := by
  have htrace := physicalBox_weak_face_scaled_bound i a ℓ hℓ upper w
  have hg := mul_le_mul_of_nonneg_right hupper (norm_nonneg (WeakSobolevJet.field 1 w))
  have hv := mul_le_mul_of_nonneg_right hκ (norm_nonneg (WeakSobolevJet.value w))
  nlinarith

theorem physicalBox_affine_face_norm_scaling (i : Fin (d+1)) (a ℓ : Fin (d+1) → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) (upper : Bool) (p : AffineCoefficients (d+1)) :
    Real.sqrt (∏ j, ℓ j)*
      ‖affineBoxFaceMap i (fun _ => 0) (fun _ => 1) zero_lt_one upper (affineBoxPullback a ℓ hℓ p)‖ =
      Real.sqrt (ℓ i)*
        ‖affineBoxFaceMap i a (fun j => a j+ℓ j) (lt_add_of_pos_right _ (hℓ i)) upper p‖ := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt (Finset.prod_pos fun j _ => hℓ j).le,
    Real.sq_sqrt (hℓ i).le,affineBoxFaceMap_scaling_sq i a ℓ hℓ upper p]
  field_simp [(hℓ i).ne']

theorem physicalBox_selected_reference_trace_bound (a ℓ : Fin (d+1) → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) (h κ : ℝ) (hh : 0 < h) (hκ : 1 ≤ κ)
    (hupper : ∀ i, ℓ i ≤ κ*h) (J : Finset (Fin (d+1) × Bool))
    (w : WeakSobolevJet (d+1) 1 (volume.restrict (openCoordinateBox a (fun j => a j+ℓ j)))
      (openCoordinateBox a (fun j => a j+ℓ j)))
    (hw : ∀ f ∈ J, weakJetBoxFaceLinearMap f.1 a (fun j => a j+ℓ j)
      (lt_add_of_pos_right _ (hℓ f.1)) f.2 w=0) (p : AffineCoefficients (d+1)) :
    Real.sqrt (∏ j, ℓ j)*‖affineBoxSelectedFaceMap (fun _ => 0) (fun _ => 1)
      (fun _ => zero_lt_one) J (affineBoxPullback a ℓ hℓ p)‖ ≤
      2*κ*(‖WeakSobolevJet.value (w-affineBoxJet a (fun j => a j+ℓ j) p)‖+
        h*‖WeakSobolevJet.field 1 (w-affineBoxJet a (fun j => a j+ℓ j) p)‖) := by
  classical
  have hroot : 0 < Real.sqrt (∏ j, ℓ j) := Real.sqrt_pos.mpr (Finset.prod_pos fun j _ => hℓ j)
  rw [← le_div_iff₀' hroot,pi_norm_le_iff_of_nonneg (by positivity)]
  intro f
  rw [affineBoxSelectedFaceMap_apply]
  by_cases hf : f ∈ J
  · rw [ite_eq_left hf,le_div_iff₀' hroot,physicalBox_affine_face_norm_scaling]
    have ht := physicalBox_weak_face_uniform_bound f.1 a ℓ hℓ f.2 h κ hh hκ (hupper f.1)
      (w-affineBoxJet a (fun j => a j+ℓ j) p)
    rw [map_sub,hw f hf,weakJetBoxFaceLinearMap_affine,zero_sub,norm_neg] at ht
    exact ht
  · rw [ite_eq_right hf,norm_zero]
    positivity

end Carleman
