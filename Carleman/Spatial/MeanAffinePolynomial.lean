module

public import Carleman.Spatial.BoundedAffineSobolev
public import Carleman.Spatial.SimplexWithinInterpolation

/-! An actual affine polynomial with prescribed gradient and with its
constant term chosen so the genuine L² residual has zero mean. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

def coordinateFunctional (g : Fin d → ℝ) : SpatialCoordinates d →L[ℝ] ℝ :=
  ∑ i : Fin d, g i • EuclideanSpace.proj i

theorem coordinateFunctional_basis (g : Fin d → ℝ) (i : Fin d) :
    coordinateFunctional g (EuclideanSpace.basisFun (Fin d) ℝ i)=g i := by
  classical
  simp [coordinateFunctional,EuclideanSpace.basisFun_apply]

def meanAffinePolynomial (u : Lp ℝ 2 (volume.restrict S))
    (A : SpatialCoordinates d →L[ℝ] ℝ) : SpatialCoordinates d →ᵃ[ℝ] ℝ :=
  affineJetPolynomial (((∫ x in S, u x)-(∫ x in S, A x))/volume.real S) A 0

theorem meanAffinePolynomial_apply (u : Lp ℝ 2 (volume.restrict S))
    (A : SpatialCoordinates d →L[ℝ] ℝ) (x : SpatialCoordinates d) :
    meanAffinePolynomial u A x = ((∫ y in S, u y)-(∫ y in S, A y))/volume.real S+A x := by
  rw [meanAffinePolynomial,affineJetPolynomial_apply,sub_zero]

theorem meanAffinePolynomial_derivative (u : Lp ℝ 2 (volume.restrict S))
    (A : SpatialCoordinates d →L[ℝ] ℝ) : affineScalarDerivative (meanAffinePolynomial u A)=A :=
  affineJetPolynomial_derivative _ A 0

theorem meanAffinePolynomial_residual_ae (hb : Bornology.IsBounded S)
    (u : Lp ℝ 2 (volume.restrict S)) (A : SpatialCoordinates d →L[ℝ] ℝ) :
    u-boundedAffineLp hb (meanAffinePolynomial u A) =ᵐ[volume.restrict S]
      (fun x => u x-meanAffinePolynomial u A x) := by
  filter_upwards [Lp.coeFn_sub u (boundedAffineLp hb (meanAffinePolynomial u A)),
    boundedAffineLp_ae hb (meanAffinePolynomial u A)] with x hx hp
  rw [hx,Pi.sub_apply,hp]

theorem meanAffinePolynomial_mean_residual (hb : Bornology.IsBounded S) (hvol : 0 < volume.real S)
    (u : Lp ℝ 2 (volume.restrict S)) (A : SpatialCoordinates d →L[ℝ] ℝ) :
    (∫ x in S, (u-boundedAffineLp hb (meanAffinePolynomial u A)) x)=0 := by
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hb.measure_lt_top (μ := volume)⟩
  have hA : Integrable (fun x => A x) (volume.restrict S) :=
    (boundedAffine_memLp hb A.toLinearMap.toAffineMap).integrable (by norm_num)
  rw [integral_congr_ae (meanAffinePolynomial_residual_ae hb u A)]
  simp_rw [meanAffinePolynomial_apply]
  have hp : Integrable (fun x => ((∫ y in S, u y)-(∫ y in S, A y))/volume.real S+A x)
      (volume.restrict S) := (integrable_const _).add hA
  rw [integral_sub ((Lp.memLp u).integrable (by norm_num)) hp,
    integral_add (integrable_const _) hA,integral_const,
    smul_eq_mul,measureReal_restrict_apply_univ]
  field_simp
  ring

end Carleman
