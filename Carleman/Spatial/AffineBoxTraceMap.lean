module

public import Carleman.Spatial.CoordinateBoxTraceLinearMap
public import Carleman.Spatial.BoundedAffineSobolev
public import Carleman.Spatial.SimplexWithinInterpolation

/-! Actual affine coefficients, L² polynomial classes, and the genuine
coordinate-face trace maps. The boundary values are identified explicitly. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

abbrev AffineCoefficients (d : ℕ) := ℝ × (SpatialCoordinates d →L[ℝ] ℝ)

def affineCoefficientPolynomial (p : AffineCoefficients d) : SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  affineJetPolynomial p.1 p.2 0

theorem affineCoefficientPolynomial_apply (p : AffineCoefficients d) (x : SpatialCoordinates d) :
    affineCoefficientPolynomial p x=p.1+p.2 x := by
  rw [affineCoefficientPolynomial,affineJetPolynomial_apply,sub_zero]

def affineBoxValueMap (a b : Fin d → ℝ) :
    AffineCoefficients d →ₗ[ℝ] Lp ℝ 2 (volume.restrict (openCoordinateBox a b)) where
  toFun p := boundedAffineLp (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial p)
  map_add' p q := by
    apply Lp.ext
    filter_upwards [boundedAffineLp_ae (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial (p+q)),
      boundedAffineLp_ae (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial p),
      boundedAffineLp_ae (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial q),
      Lp.coeFn_add (boundedAffineLp (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial p))
        (boundedAffineLp (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial q))] with x hpq hp hq he
    rw [hpq,he,Pi.add_apply,hp,hq]
    simp only [affineCoefficientPolynomial_apply]
    change (p.1+q.1)+(p.2 x+q.2 x)=(p.1+p.2 x)+(q.1+q.2 x)
    ring
  map_smul' r p := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [boundedAffineLp_ae (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial (r • p)),
      boundedAffineLp_ae (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial p),
      Lp.coeFn_smul r (boundedAffineLp (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial p))] with x hr hp he
    rw [hr,he,Pi.smul_apply,hp]
    simp only [affineCoefficientPolynomial_apply]
    change r*p.1+r*p.2 x=r*(p.1+p.2 x)
    ring

theorem affineBoxValueMap_ae (a b : Fin d → ℝ) (p : AffineCoefficients d) :
    affineBoxValueMap a b p =ᵐ[volume.restrict (openCoordinateBox a b)] affineCoefficientPolynomial p :=
  boundedAffineLp_ae (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial p)

def affineBoxDerivativeMap (a b : Fin d → ℝ) (i : Fin d) :
    AffineCoefficients d →ₗ[ℝ] Lp ℝ 2 (volume.restrict (openCoordinateBox a b)) where
  toFun p := scalarConstantLp (volume.restrict (openCoordinateBox a b))
    (p.2 (EuclideanSpace.basisFun (Fin d) ℝ i))
  map_add' p q := by
    apply Lp.ext
    filter_upwards [scalarConstantLp_ae (volume.restrict (openCoordinateBox a b))
      ((p+q).2 (EuclideanSpace.basisFun (Fin d) ℝ i)),
      scalarConstantLp_ae (volume.restrict (openCoordinateBox a b)) (p.2 (EuclideanSpace.basisFun (Fin d) ℝ i)),
      scalarConstantLp_ae (volume.restrict (openCoordinateBox a b)) (q.2 (EuclideanSpace.basisFun (Fin d) ℝ i)),
      Lp.coeFn_add (scalarConstantLp (volume.restrict (openCoordinateBox a b)) (p.2 (EuclideanSpace.basisFun (Fin d) ℝ i)))
        (scalarConstantLp (volume.restrict (openCoordinateBox a b)) (q.2 (EuclideanSpace.basisFun (Fin d) ℝ i)))] with x hpq hp hq he
    rw [hpq,he,Pi.add_apply,hp,hq]
    rfl
  map_smul' r p := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [scalarConstantLp_ae (volume.restrict (openCoordinateBox a b))
      ((r • p).2 (EuclideanSpace.basisFun (Fin d) ℝ i)),
      scalarConstantLp_ae (volume.restrict (openCoordinateBox a b)) (p.2 (EuclideanSpace.basisFun (Fin d) ℝ i)),
      Lp.coeFn_smul r (scalarConstantLp (volume.restrict (openCoordinateBox a b))
        (p.2 (EuclideanSpace.basisFun (Fin d) ℝ i)))] with x hr hp he
    rw [hr,he,Pi.smul_apply,hp]
    rfl

theorem affineBoxDerivativeMap_weak (a b : Fin d → ℝ) (i : Fin d) (p : AffineCoefficients d) :
    IsWeakSpatialDerivative (volume.restrict (openCoordinateBox a b)) (openCoordinateBox a b)
      (EuclideanSpace.basisFun (Fin d) ℝ i) (affineBoxValueMap a b p) (affineBoxDerivativeMap a b i p) := by
  have h := boundedAffineLp_weak (openCoordinateBox_isBounded a b) (affineCoefficientPolynomial p)
    (EuclideanSpace.basisFun (Fin d) ℝ i)
  rw [affineCoefficientPolynomial,affineJetPolynomial_derivative] at h
  exact h

def affineBoxFaceMap (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i) (upper : Bool) :
    AffineCoefficients (d+1) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))) :=
  (coordinateBoxFaceLinearMap i a b hi upper).comp ((affineBoxValueMap a b).prod (affineBoxDerivativeMap a b i))

theorem affineBoxFaceMap_ae (i : Fin (d+1)) (a b : Fin (d+1) → ℝ) (hi : a i < b i)
    (upper : Bool) (p : AffineCoefficients (d+1)) :
    affineBoxFaceMap i a b hi upper p =ᵐ[
      volume.restrict (openCoordinateBox (a ∘ i.succAbove) (b ∘ i.succAbove))]
      (fun x => affineCoefficientPolynomial p
        (WithLp.toLp 2 (i.insertNth (if upper then b i else a i) (fun j => x j)))) :=
  coordinateBoxFaceTrace_eq_continuous i a b hi upper _ _ (affineBoxDerivativeMap_weak a b i p)
    (affineCoefficientPolynomial p) (affineCoefficientPolynomial p).continuous_of_finiteDimensional
    (affineBoxValueMap_ae a b p)

end Carleman
