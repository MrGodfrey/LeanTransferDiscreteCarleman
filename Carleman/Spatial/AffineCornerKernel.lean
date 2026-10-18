module

public import Carleman.Spatial.AffineBoxPullback

/-! Two distinct coordinate-normal faces eliminate the entire affine kernel,
including upper faces and corners. The assertion is pointwise on the whole affine map. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

theorem unitCube_face_tangent_derivative_zero (i : Fin (d+1)) (upper : Bool)
    (p : AffineCoefficients (d+1))
    (hp : ∀ x ∈ coordinateClosedFace i (fun _ => 0) (fun _ => 1) upper,
      affineCoefficientPolynomial p x=0) (k : Fin (d+1)) (hki : k ≠ i) :
    p.2 (EuclideanSpace.basisFun (Fin (d+1)) ℝ k)=0 := by
  let x : SpatialCoordinates (d+1) := (if upper then 1 else 0) • EuclideanSpace.basisFun (Fin (d+1)) ℝ i
  have hx : x ∈ coordinateClosedFace i (fun _ => 0) (fun _ => 1) upper := by
    constructor
    · intro j
      cases upper <;> by_cases hj : j=i <;>
        simp_all [x,EuclideanSpace.basisFun_apply]
    · cases upper <;> simp [x,EuclideanSpace.basisFun_apply]
  have hy : x+EuclideanSpace.basisFun (Fin (d+1)) ℝ k ∈
      coordinateClosedFace i (fun _ => 0) (fun _ => 1) upper := by
    constructor
    · intro j
      cases upper <;> by_cases hj : j=i <;> by_cases hjk : j=k <;>
        simp_all [x,EuclideanSpace.basisFun_apply]
    · cases upper <;> simp [x,EuclideanSpace.basisFun_apply,hki]
  have h0 := hp x hx
  have h1 := hp (x+EuclideanSpace.basisFun (Fin (d+1)) ℝ k) hy
  rw [affineCoefficientPolynomial_apply] at h0 h1
  rw [map_add] at h1
  linarith

theorem unitCube_two_faces_affine_zero (i j : Fin (d+1)) (hij : i ≠ j)
    (ui uj : Bool) (p : AffineCoefficients (d+1))
    (hi : ∀ x ∈ coordinateClosedFace i (fun _ => 0) (fun _ => 1) ui, affineCoefficientPolynomial p x=0)
    (hj : ∀ x ∈ coordinateClosedFace j (fun _ => 0) (fun _ => 1) uj, affineCoefficientPolynomial p x=0) :
    p=0 := by
  have hs : ∀ k, p.2 (EuclideanSpace.basisFun (Fin (d+1)) ℝ k)=0 := by
    intro k
    by_cases hk : k=i
    · subst k
      exact unitCube_face_tangent_derivative_zero j uj p hj i hij
    · exact unitCube_face_tangent_derivative_zero i ui p hi k hk
  have hl : p.2=0 := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin (d+1)) ℝ).toBasis.ext
    intro k
    exact hs k
  have hx : (if ui then 1 else 0) • EuclideanSpace.basisFun (Fin (d+1)) ℝ i ∈
      coordinateClosedFace i (fun _ => 0) (fun _ => 1) ui := by
    constructor
    · intro k
      cases ui <;> by_cases hk : k=i <;> simp_all [EuclideanSpace.basisFun_apply]
    · cases ui <;> simp [EuclideanSpace.basisFun_apply]
  have hc := hi _ hx
  rw [affineCoefficientPolynomial_apply,hl] at hc
  change p.1+0=0 at hc
  exact Prod.ext (by simpa using hc) hl

theorem physicalBox_two_faces_affine_zero (i j : Fin (d+1)) (hij : i ≠ j)
    (a ℓ : Fin (d+1) → ℝ) (hℓ : ∀ k, 0 < ℓ k) (ui uj : Bool)
    (p : AffineCoefficients (d+1))
    (hi : ∀ x ∈ coordinateClosedFace i a (fun k => a k+ℓ k) ui, affineCoefficientPolynomial p x=0)
    (hj : ∀ x ∈ coordinateClosedFace j a (fun k => a k+ℓ k) uj, affineCoefficientPolynomial p x=0) :
    p=0 := by
  apply (affineBoxPullback a ℓ hℓ).injective
  rw [map_zero]
  exact unitCube_two_faces_affine_zero i j hij ui uj _
    ((affineBoxPullback_zero_face_iff i a ℓ hℓ ui p).mpr hi)
    ((affineBoxPullback_zero_face_iff j a ℓ hℓ uj p).mpr hj)

end Carleman
