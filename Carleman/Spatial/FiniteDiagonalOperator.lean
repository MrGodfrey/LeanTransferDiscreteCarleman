module

public import Carleman.Spatial.CartesianDiagonalTest
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Actual continuous diagonal operators on the full finite nodal space.
The coefficient map is continuous linear, so coordinate derivatives give
genuine derivatives in operator norm. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {ι : Type*} [Fintype ι]

def finiteDiagonalOperatorFamily : (ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] (ι → ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun b => ContinuousLinearMap.pi (fun i => b i • ContinuousLinearMap.proj i)
      map_add' := by intro b c; ext f i; simp [add_mul]
      map_smul' := by intro c b; ext f i; simp [mul_assoc] }

theorem finiteDiagonalOperatorFamily_apply (b f : ι → ℝ) (i : ι) :
    finiteDiagonalOperatorFamily b f i=b i*f i := rfl

theorem finiteDiagonalOperatorFamily_hasDerivWithinAt (b : ℝ → ι → ℝ)
    (b' : ι → ℝ) (S : Set ℝ) (t : ℝ)
    (hb : ∀ i, HasDerivWithinAt (fun s => b s i) (b' i) S t) :
    HasDerivWithinAt (fun s => finiteDiagonalOperatorFamily (b s))
      (finiteDiagonalOperatorFamily b') S t :=
  finiteDiagonalOperatorFamily.hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_pi.mpr hb)

theorem cartesianPhysicalInner_diagonal_bound {d : ℕ}
    (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j) (N : Fin d → ℕ)
    (σ : SpatialCoordinates d → ℝ) (b f : CartesianInteriorIndex N → ℝ)
    (K : ℝ) (hb : ∀ a, |b a| ≤ K*(σ (cartesianInteriorPoint o δ N a))^2) :
    |cartesianPhysicalInner δ N f (finiteDiagonalOperatorFamily b f)| ≤
      K*cartesianWeightedNodeEnergy o δ N σ f := by
  classical
  have hp : 0 ≤ ∏ j, δ j := Finset.prod_nonneg (fun j _ => (hδ j).le)
  rw [cartesianPhysicalInner,abs_mul,abs_of_nonneg hp]
  calc
    _ ≤ (∏ j, δ j)*∑ a, |f a*(finiteDiagonalOperatorFamily b f) a| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hp
    _ = (∏ j, δ j)*∑ a, |b a| * (f a)^2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [finiteDiagonalOperatorFamily_apply]
      have he : f a*(b a*f a)=b a*(f a)^2 := by ring
      rw [he,abs_mul,abs_of_nonneg (sq_nonneg (f a))]
    _ ≤ (∏ j, δ j)*∑ a, K*(σ (cartesianInteriorPoint o δ N a))^2*(f a)^2 := by
      apply mul_le_mul_of_nonneg_left _ hp
      exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (hb a) (sq_nonneg _))
    _ = _ := by
      simp only [cartesianWeightedNodeEnergy,mul_pow,mul_assoc,← Finset.mul_sum]
      ring

end Carleman
