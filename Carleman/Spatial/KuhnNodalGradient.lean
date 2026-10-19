module

public import Carleman.Geometry.CartesianKuhnSimplex
public import Carleman.Spatial.SimplexReferenceInverse
public import Carleman.Spatial.AffineWeakGradient

/-! Exact coordinate derivatives on the actual physical Kuhn simplex.
The adjacent-vertex formula follows from the real affine polynomial, not
from a separately assigned discrete gradient. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianKuhnNodalDerivative_basis (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (c : Fin (d+1) → ℝ)
    (x : SpatialCoordinates d) (k : Fin d) :
    fderiv ℝ (simplexNodalInterpolant (cartesianKuhnSimplex o δ hδ z π) c) x
      (EuclideanSpace.basisFun (Fin d) ℝ (π k))=(c k.succ-c k.castSucc)/δ (π k) := by
  let T := cartesianKuhnSimplex o δ hδ z π
  let p := simplexNodalInterpolant T c
  have he : affineScalarDerivative p (T.points k.succ-T.points k.castSucc)=c k.succ-c k.castSucc := by
    change p.linear (T.points k.succ-T.points k.castSucc)=_
    rw [← vsub_eq_sub, p.linear_apply_vsub]
    exact congrArg₂ (fun a b : ℝ => a-b) (simplexNodalInterpolant_vertex T c k.succ)
      (simplexNodalInterpolant_vertex T c k.castSucc)
  rw [cartesianKuhnSimplex_points_step,map_smul,smul_eq_mul] at he
  rw [(affineScalar_hasFDerivAt p x).fderiv]
  apply (eq_div_iff (hδ (π k)).ne').mpr
  nlinarith only [he]

theorem derivativeOneFiber_inner (A B : SpatialCoordinates d →L[ℝ] ℝ) :
    inner ℝ (derivativeOneFiber A) (derivativeOneFiber B)=
      ∑ j : Fin d, A (EuclideanSpace.basisFun (Fin d) ℝ j)*B (EuclideanSpace.basisFun (Fin d) ℝ j) := by
  rw [PiLp.inner_apply,← Equiv.sum_comp Sym.oneEquiv]
  apply Finset.sum_congr rfl
  intro j _
  change inner ℝ (A (EuclideanSpace.basisFun (Fin d) ℝ (Sym.oneEquiv.symm (Sym.oneEquiv j))))
    (B (EuclideanSpace.basisFun (Fin d) ℝ (Sym.oneEquiv.symm (Sym.oneEquiv j))))=_
  rw [Equiv.symm_apply_apply]
  exact real_inner_comm _ _

theorem cartesianKuhnNodalGradient_inner (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (c b : Fin (d+1) → ℝ) (x : SpatialCoordinates d) :
    inner ℝ
      (derivativeOneFiber (fderiv ℝ (simplexNodalInterpolant (cartesianKuhnSimplex o δ hδ z π) c) x))
      (derivativeOneFiber (fderiv ℝ (simplexNodalInterpolant (cartesianKuhnSimplex o δ hδ z π) b) x))=
      ∑ k : Fin d, ((c k.succ-c k.castSucc)/δ (π k))*((b k.succ-b k.castSucc)/δ (π k)) := by
  rw [derivativeOneFiber_inner,← Equiv.sum_comp π]
  apply Finset.sum_congr rfl
  intro k _
  rw [cartesianKuhnNodalDerivative_basis,cartesianKuhnNodalDerivative_basis]

theorem cartesianKuhnNodalGradientLp_inner (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (c b : Fin (d+1) → ℝ) :
    inner ℝ (simplexNodalGradientLp (cartesianKuhnSimplex o δ hδ z π) c)
      (simplexNodalGradientLp (cartesianKuhnSimplex o δ hδ z π) b)=
      volume.real (simplicialCell (cartesianKuhnSimplex o δ hδ z π).points)*
        ∑ k : Fin d, ((c k.succ-c k.castSucc)/δ (π k))*((b k.succ-b k.castSucc)/δ (π k)) := by
  rw [L2.inner_def]
  calc
    _ = ∫ _x in simplicialCell (cartesianKuhnSimplex o δ hδ z π).points,
        ∑ k : Fin d, ((c k.succ-c k.castSucc)/δ (π k))*((b k.succ-b k.castSucc)/δ (π k)) := by
      apply integral_congr_ae
      filter_upwards [simplexNodalGradientLp_ae (cartesianKuhnSimplex o δ hδ z π) c,
        simplexNodalGradientLp_ae (cartesianKuhnSimplex o δ hδ z π) b] with x hc hb
      rw [hc,hb,cartesianKuhnNodalGradient_inner]
    _ = _ := by simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]

end Carleman
