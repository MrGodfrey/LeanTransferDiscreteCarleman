module

public import Carleman.Spatial.SimplexLoadPolynomial

/-! Exact unweighted L² energy of the true local affine load polynomial. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

theorem integral_simplexLoadPolynomial (c : Fin (d+1) → ℝ) :
    (∫ x in simplicialCell T.points, simplexLoadPolynomial T c x)=
      (volume.real (simplicialCell T.points)/(d+1:ℝ))*(∑ k, c k) := by
  have hi (k : Fin (d+1)) : IntegrableOn (simplexBarycentric T k) (simplicialCell T.points) :=
    (simplexBarycentric T k).continuous_of_finiteDimensional.continuousOn.integrableOn_compact
      (simplicialCell_compact _)
  have hic (k : Fin (d+1)) : IntegrableOn
      (fun x => c k*((d+2:ℝ)*simplexBarycentric T k x-1)) (simplicialCell T.points) :=
    (((hi k).const_mul (d+2)).sub (integrable_const 1)).const_mul (c k)
  unfold simplexLoadPolynomial
  rw [integral_finsetSum _ (fun k _ => hic k)]
  simp_rw [integral_const_mul,integral_sub ((hi _).const_mul _) (integrable_const 1),
    integral_const_mul,integral_simplexBarycentric]
  simp only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ]
  change (∑ k, c k*((d+2:ℝ)*(volume.real (simplicialCell T.points)/(d+1:ℝ))-
    volume.real (simplicialCell T.points)))=_
  rw [← Finset.sum_mul,mul_comm]
  congr 1
  have hd : (d+1:ℝ) ≠ 0 := by positivity
  simp only [Measure.real]
  field_simp
  ring

theorem integral_simplexLoadPolynomial_sq (c : Fin (d+1) → ℝ) :
    (∫ x in simplicialCell T.points, (simplexLoadPolynomial T c x)^2)=
      (volume.real (simplicialCell T.points)/(d+1:ℝ))*
        ((d+2:ℝ)*(∑ k, (c k)^2)-(∑ k, c k)^2) := by
  let L := simplexLoadPolynomial T c
  have hL : IntegrableOn L (simplicialCell T.points) :=
    (simplexLoadPolynomial_continuous T c).continuousOn.integrableOn_compact (simplicialCell_compact _)
  have hprod (k : Fin (d+1)) : IntegrableOn (fun x => L x*simplexBarycentric T k x)
      (simplicialCell T.points) :=
    ((simplexLoadPolynomial_continuous T c).mul
      (simplexBarycentric T k).continuous_of_finiteDimensional).continuousOn.integrableOn_compact
        (simplicialCell_compact _)
  have he : (fun x => (L x)^2)=(fun x => ∑ k, c k*((d+2:ℝ)*(L x*simplexBarycentric T k x)-L x)) := by
    funext x
    calc
      _ = L x*(∑ k, c k*((d+2:ℝ)*simplexBarycentric T k x-1)) := by rw [← simplexLoadPolynomial]; exact sq _
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  change (∫ x in simplicialCell T.points, (L x)^2)=_
  have hic (k : Fin (d+1)) : IntegrableOn
      (fun x => c k*((d+2:ℝ)*(L x*simplexBarycentric T k x)-L x)) (simplicialCell T.points) :=
    (((hprod k).const_mul _).sub hL).const_mul _
  rw [he,integral_finsetSum _ (fun k _ => hic k)]
  simp_rw [integral_const_mul,integral_sub ((hprod _).const_mul _) hL,integral_const_mul]
  change (∑ k, c k*((d+2:ℝ)*(∫ x in simplicialCell T.points,
    simplexLoadPolynomial T c x*simplexBarycentric T k x)-∫ x in simplicialCell T.points,
      simplexLoadPolynomial T c x))=_
  simp_rw [integral_simplexLoadPolynomial_barycentric,integral_simplexLoadPolynomial]
  simp only [mul_sub,Finset.sum_sub_distrib]
  have hs : (∑ k, c k*((d+2:ℝ)*(c k*(volume.real (simplicialCell T.points)/(d+1:ℝ)))) )=
      (volume.real (simplicialCell T.points)/(d+1:ℝ))*(d+2:ℝ)*(∑ k, (c k)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs,← Finset.sum_mul]
  ring

theorem integral_simplexLoadPolynomial_sq_le (c : Fin (d+1) → ℝ) :
    (∫ x in simplicialCell T.points, (simplexLoadPolynomial T c x)^2) ≤
      (d+2:ℝ)*(volume.real (simplicialCell T.points)/(d+1:ℝ))*(∑ k, (c k)^2) := by
  rw [integral_simplexLoadPolynomial_sq]
  have hm : 0 ≤ volume.real (simplicialCell T.points)/(d+1:ℝ) := by positivity
  nlinarith [mul_nonneg hm (sq_nonneg (∑ k, c k))]

end Carleman
