module

public import Carleman.Spatial.UnitCubeH2Affine

/-! Boundary-preserving affine approximation for all weak H² functions on
the reference cube. All selected face traces are the actual bounded weak
traces; no smoothness or prior affine approximation is an input. -/
@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem unitCube_selected_affine_trace_bound (J : Finset (Fin (d+1) × Bool))
    (w : WeakSobolevJet (d+1) 1
      (volume.restrict (openCoordinateBox (fun _ => 0) (fun _ => 1)))
      (openCoordinateBox (fun _ => 0) (fun _ => 1)))
    (hw : ∀ f ∈ J, weakJetBoxFaceLinearMap f.1 (fun _ => 0) (fun _ => 1) zero_lt_one f.2 w=0)
    (p : AffineCoefficients (d+1)) :
    ‖affineBoxSelectedFaceMap (fun _ => 0) (fun _ => 1) (fun _ => zero_lt_one) J p‖ ≤
      2*(‖WeakSobolevJet.value (w-affineBoxJet (fun _ => 0) (fun _ => 1) p)‖+
        ‖WeakSobolevJet.field 1 (w-affineBoxJet (fun _ => 0) (fun _ => 1) p)‖) := by
  classical
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro f
  rw [affineBoxSelectedFaceMap_apply]
  by_cases hf : f ∈ J
  · rw [ite_eq_left hf]
    have h := unitCubeFace_norm_le f.1 f.2 (w-affineBoxJet (fun _ => 0) (fun _ => 1) p)
    rw [map_sub,hw f hf,weakJetBoxFaceLinearMap_affine,zero_sub,norm_neg] at h
    exact h
  · rw [ite_eq_right hf,norm_zero]
    positivity

theorem unitCube_h1_boundary_correction (d : ℕ) :
    ∃ A > 0, ∀ J : Finset (Fin (d+1) × Bool),
      ∀ w : WeakSobolevJet (d+1) 1
        (volume.restrict (openCoordinateBox (fun _ => 0) (fun _ => 1)))
        (openCoordinateBox (fun _ => 0) (fun _ => 1)),
      (∀ f ∈ J, weakJetBoxFaceLinearMap f.1 (fun _ => 0) (fun _ => 1) zero_lt_one f.2 w=0) →
      ∀ p : AffineCoefficients (d+1), ∃ q : AffineCoefficients (d+1),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 (fun _ => 0) (fun _ => 1) f.2,
          affineCoefficientPolynomial q y=0) ∧
        ‖WeakSobolevJet.value (w-affineBoxJet (fun _ => 0) (fun _ => 1) q)‖+
          ‖WeakSobolevJet.field 1 (w-affineBoxJet (fun _ => 0) (fun _ => 1) q)‖ ≤
          A*(‖WeakSobolevJet.value (w-affineBoxJet (fun _ => 0) (fun _ => 1) p)‖+
            ‖WeakSobolevJet.field 1 (w-affineBoxJet (fun _ => 0) (fun _ => 1) p)‖) := by
  obtain ⟨C,hC,hcorr⟩ := affineBox_uniform_h1_correction
    (fun _ : Fin (d+1) => 0) (fun _ => 1) (fun _ => zero_lt_one)
  refine ⟨1+2*C,by positivity,?_⟩
  intro J w hw p
  obtain ⟨q,hq,he⟩ := hcorr J p
  refine ⟨q,hq,?_⟩
  have ht := unitCube_selected_affine_trace_bound J w hw p
  have hc := he.trans (mul_le_mul_of_nonneg_left ht hC.le)
  have hj : w-affineBoxJet (fun _ => 0) (fun _ => 1) q =
      (w-affineBoxJet (fun _ => 0) (fun _ => 1) p)+affineBoxJet (fun _ => 0) (fun _ => 1) (p-q) := by
    change w-affineBoxJetLinearMap (fun _ => 0) (fun _ => 1) q =
      (w-affineBoxJetLinearMap (fun _ => 0) (fun _ => 1) p)+affineBoxJetLinearMap (fun _ => 0) (fun _ => 1) (p-q)
    rw [map_sub]
    abel
  rw [hj]
  have ha := h1_value_gradient_add_bound (w-affineBoxJet (fun _ => 0) (fun _ => 1) p)
    (affineBoxJet (fun _ => 0) (fun _ => 1) (p-q))
  nlinarith

theorem unitCube_h2_boundary_affine (d : ℕ) :
    ∃ C > 0, ∀ J : Finset (Fin (d+1) × Bool),
      ∀ u : WeakSobolevJet (d+1) 2
        (volume.restrict (openCoordinateBox (fun _ => 0) (fun _ => 1)))
        (openCoordinateBox (fun _ => 0) (fun _ => 1)),
      (∀ f ∈ J, weakJetBoxFaceLinearMap f.1 (fun _ => 0) (fun _ => 1) zero_lt_one f.2
        (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u)=0) →
      ∃ q : AffineCoefficients (d+1),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 (fun _ => 0) (fun _ => 1) f.2,
          affineCoefficientPolynomial q y=0) ∧
        ‖WeakSobolevJet.value (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
          affineBoxJet (fun _ => 0) (fun _ => 1) q)‖+
          ‖WeakSobolevJet.field 1 (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
            affineBoxJet (fun _ => 0) (fun _ => 1) q)‖ ≤ C*‖WeakSobolevJet.field 2 u‖ := by
  obtain ⟨A,hA,hcorr⟩ := unitCube_h1_boundary_correction d
  obtain ⟨B,hB,happrox⟩ := unitCube_h2_affine_approximation d
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro J u hu
  obtain ⟨p,hp⟩ := happrox u
  obtain ⟨q,hq,he⟩ := hcorr J (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u) hu p
  refine ⟨q,hq,he.trans ?_⟩
  calc
    _ ≤ A*(B*‖WeakSobolevJet.field 2 u‖) := mul_le_mul_of_nonneg_left hp hA.le
    _ = _ := by ring

theorem unitCube_h2_boundary_affine_actual (d : ℕ) :
    ∃ C > 0, ∀ J : Finset (Fin (d+1) × Bool),
      ∀ u : WeakSobolevJet (d+1) 2
        (volume.restrict (openCoordinateBox (fun _ => 0) (fun _ => 1)))
        (openCoordinateBox (fun _ => 0) (fun _ => 1)),
      (∀ f ∈ J, weakJetBoxFaceLinearMap f.1 (fun _ => 0) (fun _ => 1) zero_lt_one f.2
        (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u)=0) →
      ∃ (p : SpatialCoordinates (d+1) →ᵃ[ℝ] ℝ)
        (r : WeakSobolevJet (d+1) 1
          (volume.restrict (openCoordinateBox (fun _ => 0) (fun _ => 1)))
          (openCoordinateBox (fun _ => 0) (fun _ => 1))),
        (∀ f ∈ J, ∀ y ∈ coordinateClosedFace f.1 (fun _ => 0) (fun _ => 1) f.2, p y=0) ∧
        (WeakSobolevJet.value r =ᵐ[volume.restrict (openCoordinateBox (fun _ => 0) (fun _ => 1))]
          (fun x => WeakSobolevJet.value u x-p x)) ∧
        ‖WeakSobolevJet.value r‖+‖WeakSobolevJet.field 1 r‖ ≤ C*‖WeakSobolevJet.field 2 u‖ := by
  obtain ⟨C,hC,h⟩ := unitCube_h2_boundary_affine d
  refine ⟨C,hC,?_⟩
  intro J u hu
  obtain ⟨q,hq,he⟩ := h J u hu
  refine ⟨affineCoefficientPolynomial q,
    WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-affineBoxJet (fun _ => 0) (fun _ => 1) q,hq,?_,he⟩
  rw [map_sub,WeakSobolevJet.truncate_value,affineBoxJet_value]
  filter_upwards [Lp.coeFn_sub (WeakSobolevJet.value u) (affineBoxValueMap (fun _ => 0) (fun _ => 1) q),
    affineBoxValueMap_ae (fun _ => 0) (fun _ => 1) q] with x hx hqae
  rw [hx,Pi.sub_apply,hqae]

end Carleman
