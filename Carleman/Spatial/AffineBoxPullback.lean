module

public import Carleman.Geometry.PhysicalBoxChart
public import Carleman.Spatial.AffineBoundaryCorrection

/-! Actual pullback of all affine polynomials under a translated diagonal
chart. The coefficient map is invertible and respects the actual polynomials. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def affineCoefficientChange (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d)
    (b : SpatialCoordinates d) : AffineCoefficients d ≃ₗ[ℝ] AffineCoefficients d where
  toFun p := (p.1+p.2 b,p.2.comp A.toContinuousLinearMap)
  invFun q := (q.1-q.2 (A.symm b),q.2.comp A.symm.toContinuousLinearMap)
  left_inv p := by
    apply Prod.ext
    · simp
    · ext x
      simp
  right_inv q := by
    apply Prod.ext
    · simp
    · ext x
      simp
  map_add' p q := by
    apply Prod.ext
    · change (p.1+q.1)+(p.2 b+q.2 b)=(p.1+p.2 b)+(q.1+q.2 b)
      ring
    · ext x
      rfl
  map_smul' r p := by
    apply Prod.ext
    · change r*p.1+r*p.2 b=r*(p.1+p.2 b)
      ring
    · ext x
      rfl

theorem affineCoefficientChange_apply (A : SpatialCoordinates d ≃L[ℝ] SpatialCoordinates d)
    (b : SpatialCoordinates d) (p : AffineCoefficients d) (x : SpatialCoordinates d) :
    affineCoefficientPolynomial (affineCoefficientChange A b p) x=
      affineCoefficientPolynomial p (affineChange A b x) := by
  simp only [affineCoefficientPolynomial_apply,affineChange_apply,map_add]
  change (p.1+p.2 b)+p.2 (A x)=p.1+(p.2 (A x)+p.2 b)
  ring

def affineBoxPullback (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) :
    AffineCoefficients d ≃ₗ[ℝ] AffineCoefficients d :=
  affineCoefficientChange (coordinateDilation ℓ hℓ) (WithLp.toLp 2 a)

theorem affineBoxPullback_apply (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (p : AffineCoefficients d) (x : SpatialCoordinates d) :
    affineCoefficientPolynomial (affineBoxPullback a ℓ hℓ p) x=
      affineCoefficientPolynomial p (physicalBoxChart a ℓ hℓ x) :=
  affineCoefficientChange_apply _ _ p x

theorem affineBoxPullback_derivative (a ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (p : AffineCoefficients d) (i : Fin d) :
    (affineBoxPullback a ℓ hℓ p).2 (EuclideanSpace.basisFun (Fin d) ℝ i)=
      ℓ i*p.2 (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  change p.2 (coordinateDilation ℓ hℓ (EuclideanSpace.basisFun (Fin d) ℝ i))=_
  rw [coordinateDilation_basis,map_smul]
  rfl

theorem affineBoxPullback_zero_face_iff (i : Fin (d+1)) (a ℓ : Fin (d+1) → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) (upper : Bool) (p : AffineCoefficients (d+1)) :
    (∀ x ∈ coordinateClosedFace i (fun _ => 0) (fun _ => 1) upper,
      affineCoefficientPolynomial (affineBoxPullback a ℓ hℓ p) x=0) ↔
    (∀ y ∈ coordinateClosedFace i a (fun j => a j+ℓ j) upper,
      affineCoefficientPolynomial p y=0) := by
  rw [← physicalBoxChart_image_face i a ℓ hℓ upper]
  simp only [forall_mem_image,affineBoxPullback_apply]

end Carleman
