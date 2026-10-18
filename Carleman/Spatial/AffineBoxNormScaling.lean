module

public import Carleman.Spatial.AffineBoxPullback

/-! Exact L² scaling of the genuine affine bulk and face classes, and the
complete gradient scaling bound. Measures and representatives are the original ones. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem affineBoxValueMap_norm_sq (a b : Fin d → ℝ) (p : AffineCoefficients d) :
    ‖affineBoxValueMap a b p‖^2 =
      ∫ x in openCoordinateBox a b, (affineCoefficientPolynomial p x)^2 := by
  rw [scalarLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [affineBoxValueMap_ae a b p] with x hx
  rw [hx]

theorem affineBoxFaceMap_norm_sq (i : Fin (d+1)) (a b : Fin (d+1) → ℝ)
    (hi : a i < b i) (upper : Bool) (p : AffineCoefficients (d+1)) :
    ‖affineBoxFaceMap i a b hi upper p‖^2 =
      ∫ x in openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove),
        (affineCoefficientPolynomial p
          (WithLp.toLp 2 (i.insertNth (if upper then b i else a i) (fun j => x j))))^2 := by
  rw [scalarLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [affineBoxFaceMap_ae i a b hi upper p] with x hx
  rw [hx]

theorem affineBoxValueMap_scaling_sq (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (p : AffineCoefficients d) :
    ‖affineBoxValueMap a (fun i => a i+ℓ i) p‖^2 =
      (∏ i, ℓ i) * ‖affineBoxValueMap (fun _ => 0) (fun _ => 1) (affineBoxPullback a ℓ hℓ p)‖^2 := by
  rw [affineBoxValueMap_norm_sq,affineBoxValueMap_norm_sq,integral_physicalBoxChart a ℓ hℓ]
  simp only [affineBoxPullback_apply]

theorem affineBoxFaceMap_scaling_sq (i : Fin (d+1)) (a ℓ : Fin (d+1) → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) (upper : Bool) (p : AffineCoefficients (d+1)) :
    ‖affineBoxFaceMap i a (fun j => a j+ℓ j) (lt_add_of_pos_right _ (hℓ i)) upper p‖^2 =
      ((∏ j, ℓ j)/ℓ i) *
        ‖affineBoxFaceMap i (fun _ => 0) (fun _ => 1) zero_lt_one upper (affineBoxPullback a ℓ hℓ p)‖^2 := by
  rw [affineBoxFaceMap_norm_sq,affineBoxFaceMap_norm_sq]
  have h := integral_physicalBoxChart (a ∘ i.succAbove) (ℓ ∘ i.succAbove)
    (fun j => hℓ (i.succAbove j))
    (fun x => (affineCoefficientPolynomial p
      (WithLp.toLp 2 (i.insertNth (if upper then a i+ℓ i else a i) (fun j => x j))))^2)
  change (∫ x in openCoordinateBox (a ∘ i.succAbove) ((fun j => a j+ℓ j) ∘ i.succAbove), _)=_ at h
  rw [h]
  have hj : (∏ j, (ℓ ∘ i.succAbove) j)=(∏ j, ℓ j)/ℓ i := physicalBoxChart_face_jacobian i ℓ hℓ
  rw [hj]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [affineBoxPullback_apply,physicalBoxChart_facePoint]

theorem affineBoxDerivativeMap_norm_sq (a b : Fin d → ℝ) (p : AffineCoefficients d) (i : Fin d) :
    ‖affineBoxDerivativeMap a b i p‖^2 =
      volume.real (openCoordinateBox a b) * (p.2 (EuclideanSpace.basisFun (Fin d) ℝ i))^2 := by
  rw [scalarLp_norm_sq]
  calc
    _ = ∫ _x in openCoordinateBox a b, (p.2 (EuclideanSpace.basisFun (Fin d) ℝ i))^2 := by
      apply integral_congr_ae
      filter_upwards [scalarConstantLp_ae (volume.restrict (openCoordinateBox a b))
        (p.2 (EuclideanSpace.basisFun (Fin d) ℝ i))] with x hx
      rw [show affineBoxDerivativeMap a b i p x=scalarConstantLp (volume.restrict (openCoordinateBox a b))
        (p.2 (EuclideanSpace.basisFun (Fin d) ℝ i)) x from rfl,hx]
    _ = _ := by simp

theorem coordinateBox_volume_scaling (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) :
    volume.real (openCoordinateBox a (fun i => a i+ℓ i))=
      (∏ i, ℓ i)*volume.real (openCoordinateBox (fun _ => 0) (fun _ => 1) : Set (SpatialCoordinates d)) := by
  simpa using integral_physicalBoxChart a ℓ hℓ (fun _ => 1)

theorem affineBoxGradientMap_norm_sq (a b : Fin d → ℝ) (p : AffineCoefficients d) :
    ‖affineBoxGradientMap a b p‖^2=∑ i : Fin d, ‖affineBoxDerivativeMap a b i p‖^2 :=
  coordinateFirstJet_gradient_norm_sq _ _ (fun i => affineBoxDerivativeMap_weak a b i p)

theorem affineBoxGradientMap_scaling_sq (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (p : AffineCoefficients d) :
    ‖affineBoxGradientMap (fun _ => 0) (fun _ => 1) (affineBoxPullback a ℓ hℓ p)‖^2 =
      (∏ i, ℓ i)⁻¹ * ∑ i : Fin d, (ℓ i)^2*‖affineBoxDerivativeMap a (fun j => a j+ℓ j) i p‖^2 := by
  rw [affineBoxGradientMap_norm_sq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [affineBoxDerivativeMap_norm_sq,affineBoxDerivativeMap_norm_sq,affineBoxPullback_derivative,
    coordinateBox_volume_scaling a ℓ hℓ]
  have hp : (∏ j, ℓ j) ≠ 0 := (Finset.prod_pos fun j _ => hℓ j).ne'
  field_simp

theorem affineBoxGradientMap_scaling_bound_sq (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (m : ℝ) (hm : 0 < m) (hlower : ∀ i, m ≤ ℓ i) (p : AffineCoefficients d) :
    m^2*‖affineBoxGradientMap a (fun i => a i+ℓ i) p‖^2 ≤
      (∏ i, ℓ i)*‖affineBoxGradientMap (fun _ => 0) (fun _ => 1) (affineBoxPullback a ℓ hℓ p)‖^2 := by
  rw [affineBoxGradientMap_scaling_sq,← mul_assoc,
    mul_inv_cancel₀ (Finset.prod_pos fun i _ => hℓ i).ne',one_mul,affineBoxGradientMap_norm_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ hm.le (hℓ i).le).mpr (hlower i)) (sq_nonneg _)

theorem affineBoxValueMap_scaling (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (p : AffineCoefficients d) :
    ‖affineBoxValueMap a (fun i => a i+ℓ i) p‖ =
      Real.sqrt (∏ i, ℓ i) * ‖affineBoxValueMap (fun _ => 0) (fun _ => 1) (affineBoxPullback a ℓ hℓ p)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (Finset.prod_pos fun i _ => hℓ i).le,affineBoxValueMap_scaling_sq]

theorem affineBoxGradientMap_scaling_bound (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (m : ℝ) (hm : 0 < m) (hlower : ∀ i, m ≤ ℓ i) (p : AffineCoefficients d) :
    m*‖affineBoxGradientMap a (fun i => a i+ℓ i) p‖ ≤
      Real.sqrt (∏ i, ℓ i)*‖affineBoxGradientMap (fun _ => 0) (fun _ => 1) (affineBoxPullback a ℓ hℓ p)‖ := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt (Finset.prod_pos fun i _ => hℓ i).le]
  exact affineBoxGradientMap_scaling_bound_sq a ℓ hℓ m hm hlower p

theorem affineBox_h1_scaling_bound (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (h κ : ℝ) (hh : 0 < h) (hκ : 1 ≤ κ) (hlower : ∀ i, h/κ ≤ ℓ i) (p : AffineCoefficients d) :
    ‖affineBoxValueMap a (fun i => a i+ℓ i) p‖+h*‖affineBoxGradientMap a (fun i => a i+ℓ i) p‖ ≤
      κ*Real.sqrt (∏ i, ℓ i) *
        (‖affineBoxValueMap (fun _ => 0) (fun _ => 1) (affineBoxPullback a ℓ hℓ p)‖+
          ‖affineBoxGradientMap (fun _ => 0) (fun _ => 1) (affineBoxPullback a ℓ hℓ p)‖) := by
  have hk : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hg := mul_le_mul_of_nonneg_left
    (affineBoxGradientMap_scaling_bound a ℓ hℓ (h/κ) (div_pos hh hk) hlower p) hk.le
  have he : κ*(h/κ)=h := by field_simp
  rw [← mul_assoc,he] at hg
  rw [affineBoxValueMap_scaling a ℓ hℓ]
  have hv : Real.sqrt (∏ i, ℓ i)*‖affineBoxValueMap (fun _ => 0) (fun _ => 1) (affineBoxPullback a ℓ hℓ p)‖ ≤
      κ*(Real.sqrt (∏ i, ℓ i)*‖affineBoxValueMap (fun _ => 0) (fun _ => 1) (affineBoxPullback a ℓ hℓ p)‖) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (∏ i, ℓ i))
      (norm_nonneg (affineBoxValueMap (fun _ => 0) (fun _ => 1) (affineBoxPullback a ℓ hℓ p)))]
  nlinarith

end Carleman
