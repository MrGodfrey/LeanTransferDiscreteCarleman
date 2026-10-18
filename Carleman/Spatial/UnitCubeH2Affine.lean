module

public import Carleman.Geometry.CoordinateBoxConvexity
public import Carleman.Spatial.AffineJetTraceIdentities
public import Carleman.Spatial.ConvexH2AffineApproximation
public import Carleman.Spatial.SobolevTruncation

/-! Unconstrained affine approximation on the unit cube for every original
weak H² jet, expressed as a difference of genuine H¹ jets. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem h2AffineResidual_eq_jet_sub (a b : Fin d → ℝ)
    (u : WeakSobolevJet d 2 (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b))
    (p : AffineCoefficients d) (hp : affineCoefficientPolynomial p=h2MeanAffine u) :
    h2AffineResidual (openCoordinateBox_isBounded a b) u =
      WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-affineBoxJet a b p := by
  apply WeakSobolevJet.value_injective (openCoordinateBox_isOpen a b)
    (ae_restrict_mem (openCoordinateBox_isOpen a b).measurableSet)
  rw [h2AffineResidual_value,map_sub,WeakSobolevJet.truncate_value,affineBoxJet_value]
  change WeakSobolevJet.value u-boundedAffineLp (openCoordinateBox_isBounded a b) (h2MeanAffine u)=
    WeakSobolevJet.value u-boundedAffineLp (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial p)
  rw [hp]

theorem unitCube_h2_affine_approximation (d : ℕ) :
    ∃ B > 0, ∀ u : WeakSobolevJet (d+1) 2
      (volume.restrict (openCoordinateBox (fun _ => 0) (fun _ => 1)))
      (openCoordinateBox (fun _ => 0) (fun _ => 1)),
      ∃ p : AffineCoefficients (d+1),
        ‖WeakSobolevJet.value (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
            affineBoxJet (fun _ => 0) (fun _ => 1) p)‖+
          ‖WeakSobolevJet.field 1 (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
            affineBoxJet (fun _ => 0) (fun _ => 1) p)‖ ≤ B*‖WeakSobolevJet.field 2 u‖ := by
  refine ⟨((2:ℝ)^(d+1)+1)*(d+1:ℕ)*(d+1:ℕ)^2,by positivity,?_⟩
  intro u
  obtain ⟨p,hp⟩ := affineCoefficientPolynomial_surjective (h2MeanAffine u)
  refine ⟨p,?_⟩
  have h := h2AffineResidual_homogeneous_bound
    (openCoordinateBox_isOpen (fun _ : Fin (d+1) => 0) (fun _ => 1))
    (openCoordinateBox_convex (fun _ => 0) (fun _ => 1))
    (openCoordinateBox_isBounded (fun _ => 0) (fun _ => 1))
    (openCoordinateBox_volume_pos (fun _ => 0) (fun _ => 1) (fun _ => zero_lt_one))
    u (D := (d+1:ℕ)) (by positivity) (fun x hx y hy => unitCube_diameter_bound x y hx hy)
  rw [h2AffineResidual_eq_jet_sub _ _ u p hp] at h
  have hn : 1 ≤ (d+1:ℕ) := by omega
  have hn' : (1:ℝ) ≤ (d+1:ℕ) := by exact_mod_cast hn
  apply le_trans _ h
  apply add_le_add le_rfl
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hn'
    (norm_nonneg (WeakSobolevJet.field 1
      (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-affineBoxJet (fun _ => 0) (fun _ => 1) p)))

end Carleman
