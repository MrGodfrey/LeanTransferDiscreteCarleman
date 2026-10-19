module

public import Carleman.Geometry.CoordinateReflection
public import Carleman.Spatial.WeakDirections

/-! Genuine L2 reflection and transport of the complete weak derivative
identity, with the sign change in precisely the normal coordinate. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def coordinateReflectionLp (r : Fin d) (c : ℝ) :
    Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) →+ Lp ℝ 2 (volume : Measure (SpatialCoordinates d)) :=
  affineTransportLp (coordinateSignFlip r).toContinuousLinearEquiv
    ((2*c) • EuclideanSpace.basisFun (Fin d) ℝ r) (coordinateReflection_measurePreserving r c)

theorem coordinateReflectionLp_ae (r : Fin d) (c : ℝ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    coordinateReflectionLp r c u =ᵐ[volume] u ∘ coordinateReflection r c := by
  have h := affineTransportLp_ae (coordinateSignFlip r).toContinuousLinearEquiv
    ((2*c) • EuclideanSpace.basisFun (Fin d) ℝ r) (coordinateReflection_measurePreserving r c) u
  change coordinateReflectionLp r c u =ᵐ[volume] u ∘ (coordinateReflection r c).symm at h
  rwa [coordinateReflection_symm] at h

theorem coordinateReflectionLp_norm (r : Fin d) (c : ℝ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    ‖coordinateReflectionLp r c u‖=‖u‖ := affineTransportLp_norm _ _ _ _

theorem integral_mul_coordinateReflectionLp (r : Fin d) (c : ℝ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) (a : SpatialCoordinates d → ℝ) :
    (∫ x, a x*coordinateReflectionLp r c u x)=∫ x, a (coordinateReflection r c x)*u x :=
  integral_mul_affineTransportLp _ _ _ _ _

theorem coordinateReflectionLp_inner (r : Fin d) (c : ℝ)
    (u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    inner ℝ (coordinateReflectionLp r c u) v=inner ℝ u (coordinateReflectionLp r c v) := by
  rw [L2.inner_def,L2.inner_def]
  simp only [RCLike.inner_apply,conj_trivial]
  rw [integral_mul_coordinateReflectionLp]
  apply integral_congr_ae
  filter_upwards [coordinateReflectionLp_ae r c v] with x hx
  rw [hx]
  rfl

theorem coordinateReflectionLp_involutive (r : Fin d) (c : ℝ)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    coordinateReflectionLp r c (coordinateReflectionLp r c u)=u := by
  apply Lp.ext
  filter_upwards [coordinateReflectionLp_ae r c (coordinateReflectionLp r c u),
    (coordinateReflection_measurePreserving r c).quasiMeasurePreserving.ae
      (coordinateReflectionLp_ae r c u)] with x h1 h2
  change coordinateReflectionLp r c (coordinateReflectionLp r c u) x=
    coordinateReflectionLp r c u (coordinateReflection r c x) at h1
  change coordinateReflectionLp r c u (coordinateReflection r c x)=
    u (coordinateReflection r c (coordinateReflection r c x)) at h2
  rw [h1,h2,coordinateReflection_involutive]

theorem coordinateReflectionLp_inner_both (r : Fin d) (c : ℝ)
    (u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    inner ℝ (coordinateReflectionLp r c u) (coordinateReflectionLp r c v)=inner ℝ u v := by
  rw [coordinateReflectionLp_inner,coordinateReflectionLp_involutive]

theorem IsWeakSpatialDerivative.coordinate_reflection (r : Fin d) (c : ℝ) (i : Fin d)
    {u g : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (h : IsWeakSpatialDerivative volume univ (EuclideanSpace.basisFun (Fin d) ℝ i) u g) :
    IsWeakSpatialDerivative volume univ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (coordinateReflectionLp r c u) (coordinateReflectionSign r i • coordinateReflectionLp r c g) := by
  have ht := h.affine_transport (coordinateSignFlip r).toContinuousLinearEquiv
    ((2*c) • EuclideanSpace.basisFun (Fin d) ℝ r) (coordinateReflection_measurePreserving r c)
    (S := univ) (T := univ) (subset_univ _)
  change IsWeakSpatialDerivative volume univ (coordinateSignFlip r (EuclideanSpace.basisFun (Fin d) ℝ i))
    (coordinateReflectionLp r c u) (coordinateReflectionLp r c g) at ht
  rw [coordinateSignFlip_basis] at ht
  have hs := ht.direction_smul (coordinateReflectionSign r i)
  simpa only [smul_smul,← pow_two,coordinateReflectionSign_sq,one_smul] using hs

end Carleman
