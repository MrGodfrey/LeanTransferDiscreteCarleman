module

public import Carleman.Spatial.UnitCubeH2Affine
public import Carleman.Spatial.PhysicalBoxBoundaryCorrection

/-! Uniform h² affine approximation of every original weak H² state on the
physical box. The convex-domain mean construction is applied on that box. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem physicalBox_diameter_bound (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (L : ℝ) (hL : 0 ≤ L) (hupper : ∀ i, ℓ i ≤ L)
    (x y : SpatialCoordinates d)
    (hx : x ∈ openCoordinateBox a (fun i => a i+ℓ i))
    (hy : y ∈ openCoordinateBox a (fun i => a i+ℓ i)) : dist x y ≤ (d:ℝ)*L := by
  let Φ := physicalBoxChart a ℓ hℓ
  have hx' : Φ.symm x ∈ openCoordinateBox (fun _ => 0) (fun _ => 1) := by
    rw [← physicalBoxChart_preimage_open a ℓ hℓ]
    change Φ (Φ.symm x) ∈ openCoordinateBox a (fun i => a i+ℓ i)
    simpa using hx
  have hy' : Φ.symm y ∈ openCoordinateBox (fun _ => 0) (fun _ => 1) := by
    rw [← physicalBoxChart_preimage_open a ℓ hℓ]
    change Φ (Φ.symm y) ∈ openCoordinateBox a (fun i => a i+ℓ i)
    simpa using hy
  have hsub : x-y=coordinateDilation ℓ hℓ (Φ.symm x-Φ.symm y) := by
    have hx0 : coordinateDilation ℓ hℓ (Φ.symm x)+WithLp.toLp 2 a=x := Φ.apply_symm_apply x
    have hy0 : coordinateDilation ℓ hℓ (Φ.symm y)+WithLp.toLp 2 a=y := Φ.apply_symm_apply y
    calc
      x-y = (coordinateDilation ℓ hℓ (Φ.symm x)+WithLp.toLp 2 a)-
        (coordinateDilation ℓ hℓ (Φ.symm y)+WithLp.toLp 2 a) := by rw [hx0,hy0]
      _ = _ := by rw [map_sub]; abel
  calc
    dist x y = ‖coordinateDilation ℓ hℓ (Φ.symm x-Φ.symm y)‖ := by rw [dist_eq_norm,hsub]
    _ ≤ L*‖Φ.symm x-Φ.symm y‖ := coordinateDilation_norm_le ℓ hℓ L hL hupper _
    _ ≤ L*(d:ℝ) := mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm] using unitCube_diameter_bound (Φ.symm x) (Φ.symm y) hx' hy') hL
    _ = _ := by ring

theorem physicalBox_h2_affine_approximation (d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ B > 0, ∀ (a ℓ : Fin (d+1) → ℝ) (hℓ : ∀ i, 0 < ℓ i) (h : ℝ),
      0 < h → (∀ i, ℓ i ≤ κ*h) →
      ∀ u : WeakSobolevJet (d+1) 2 (volume.restrict (openCoordinateBox a (fun i => a i+ℓ i)))
        (openCoordinateBox a (fun i => a i+ℓ i)),
      ∃ p : AffineCoefficients (d+1),
        ‖WeakSobolevJet.value (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
          affineBoxJet a (fun i => a i+ℓ i) p)‖+
          h*‖WeakSobolevJet.field 1 (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
            affineBoxJet a (fun i => a i+ℓ i) p)‖ ≤ B*h^2*‖WeakSobolevJet.field 2 u‖ := by
  have hk : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  refine ⟨((2:ℝ)^(d+1)+1)*(d+1:ℕ)*((d+1:ℕ)*κ)^2,by positivity,?_⟩
  intro a ℓ hℓ h hh hupper u
  obtain ⟨p,hp⟩ := affineCoefficientPolynomial_surjective (h2MeanAffine u)
  refine ⟨p,?_⟩
  have hn : (1:ℝ) ≤ (d+1:ℕ) := by exact_mod_cast (show 1 ≤ d+1 by omega)
  have hD : h ≤ (d+1:ℕ)*(κ*h) := by
    calc
      h ≤ κ*h := by nlinarith
      _ ≤ (d+1:ℕ)*(κ*h) := by nlinarith [mul_pos hk hh]
  have hbound := h2AffineResidual_homogeneous_bound
    (openCoordinateBox_isOpen a (fun i => a i+ℓ i))
    (openCoordinateBox_convex a (fun i => a i+ℓ i))
    (openCoordinateBox_isBounded a (fun i => a i+ℓ i))
    (openCoordinateBox_volume_pos a (fun i => a i+ℓ i) (fun i => lt_add_of_pos_right _ (hℓ i)))
    u (D := (d+1:ℕ)*(κ*h)) (by positivity)
    (fun x hx y hy => physicalBox_diameter_bound a ℓ hℓ (κ*h) (by positivity) hupper x y hx hy)
  rw [h2AffineResidual_eq_jet_sub _ _ u p hp] at hbound
  calc
    _ ≤ ‖WeakSobolevJet.value (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
          affineBoxJet a (fun i => a i+ℓ i) p)‖+
        ((d+1:ℕ)*(κ*h))*‖WeakSobolevJet.field 1 (WeakSobolevJet.truncate (by decide : 1 ≤ 2) u-
          affineBoxJet a (fun i => a i+ℓ i) p)‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
    _ ≤ _ := hbound
    _ = _ := by ring

end Carleman
