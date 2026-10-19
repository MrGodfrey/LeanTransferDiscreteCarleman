module

public import Carleman.Spatial.SimplexMassIntegral

/-! The actual local affine load polynomial and its exact dual moments. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} (T : Affine.Simplex ℝ (SpatialCoordinates d) d)

def simplexLoadPolynomial (c : Fin (d+1) → ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∑ k, c k*((d+2:ℝ)*simplexBarycentric T k x-1)

theorem simplexLoadPolynomial_continuous (c : Fin (d+1) → ℝ) :
    Continuous (simplexLoadPolynomial T c) := by
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul
    ((continuous_const.mul (simplexBarycentric T k).continuous_of_finiteDimensional).sub continuous_const)

theorem integral_simplex_dual_barycentric (i j : Fin (d+1)) :
    (∫ x in simplicialCell T.points,
      ((d+2:ℝ)*simplexBarycentric T i x-1)*simplexBarycentric T j x)=
      if i=j then volume.real (simplicialCell T.points)/(d+1:ℝ) else 0 := by
  have hi : IntegrableOn (fun x => simplexBarycentric T i x*simplexBarycentric T j x)
      (simplicialCell T.points) :=
    ((simplexBarycentric T i).continuous_of_finiteDimensional.mul
      (simplexBarycentric T j).continuous_of_finiteDimensional).continuousOn.integrableOn_compact
        (simplicialCell_compact _)
  have hj : IntegrableOn (simplexBarycentric T j) (simplicialCell T.points) :=
    (simplexBarycentric T j).continuous_of_finiteDimensional.continuousOn.integrableOn_compact
      (simplicialCell_compact _)
  simp_rw [sub_mul,one_mul,mul_assoc]
  rw [integral_sub (hi.const_mul _) hj,integral_const_mul,
    integral_simplexBarycentric_mul,integral_simplexBarycentric]
  have hd1 : (d+1:ℝ) ≠ 0 := by positivity
  have hd2 : (d+2:ℝ) ≠ 0 := by positivity
  split_ifs <;> field_simp <;> ring

theorem integral_simplexLoadPolynomial_barycentric (c : Fin (d+1) → ℝ) (j : Fin (d+1)) :
    (∫ x in simplicialCell T.points, simplexLoadPolynomial T c x*simplexBarycentric T j x)=
      c j*(volume.real (simplicialCell T.points)/(d+1:ℝ)) := by
  simp only [simplexLoadPolynomial,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul,integral_simplex_dual_barycentric]
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · intro i _
    exact (continuous_const.mul
      (((continuous_const.mul (simplexBarycentric T i).continuous_of_finiteDimensional).sub continuous_const).mul
        (simplexBarycentric T j).continuous_of_finiteDimensional)).continuousOn.integrableOn_compact
          (simplicialCell_compact _)

end Carleman
