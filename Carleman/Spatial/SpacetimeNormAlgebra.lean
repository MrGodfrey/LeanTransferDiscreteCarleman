module

public import Carleman.Spatial.SpacetimeWeightedNorm
public import Carleman.Continuous.BochnerNormAlgebra

/-! Norm algebra for the genuine sum of squared Bochner derivative norms.
Field finiteness is explicit, so totalized L² norms cannot hide infinity. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
  {S : Set (SpatialCoordinates d)}

theorem parameterTimeField_add (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u v : ℝ → WeakSobolevJet d n ν S) (k : Fin (n+1)) :
    parameterTimeField r σ (u+v) k = parameterTimeField r σ u k+parameterTimeField r σ v k := by
  funext t
  simp only [parameterTimeField,Pi.add_apply,map_add,BoundedMultiplier.map_add,smul_add]

theorem spacetimeWeightedNorm_add_le (g : TimeGrid) (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    (u v : ℝ → WeakSobolevJet d n ν S)
    (hu : ∀ k, MemLp (parameterTimeField r σ u k) 2 g.timeMeasure)
    (hv : ∀ k, MemLp (parameterTimeField r σ v k) 2 g.timeMeasure) :
    spacetimeWeightedNorm g r σ (u+v) ≤ spacetimeWeightedNorm g r σ u+spacetimeWeightedNorm g r σ v := by
  let U := fun k => bochnerL2Norm g.timeMeasure (parameterTimeField r σ u k)
  let V := fun k => bochnerL2Norm g.timeMeasure (parameterTimeField r σ v k)
  have hU (k) : 0 ≤ U k := bochnerL2Norm_nonneg _
  have hV (k) : 0 ≤ V k := bochnerL2Norm_nonneg _
  have hc : ∑ k, U k*V k ≤ spacetimeWeightedNorm g r σ u*spacetimeWeightedNorm g r σ v :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ U V
  have hs : spacetimeWeightedSq g r σ (u+v) ≤
      spacetimeWeightedSq g r σ u+spacetimeWeightedSq g r σ v+2*(∑ k, U k*V k) := by
    calc
      _ ≤ ∑ k, (U k+V k)^2 := by
        apply Finset.sum_le_sum
        intro k _
        apply (sq_le_sq₀ (bochnerL2Norm_nonneg _) (add_nonneg (hU k) (hV k))).mpr
        rw [parameterTimeField_add]
        exact bochnerL2Norm_add (hu k) (hv k)
      _ = _ := by
        simp only [add_sq,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum,spacetimeWeightedSq,U,V]
        ring
  apply (sq_le_sq₀ (spacetimeWeightedNorm_nonneg _ _ _ _)
    (add_nonneg (spacetimeWeightedNorm_nonneg _ _ _ _) (spacetimeWeightedNorm_nonneg _ _ _ _))).mp
  rw [spacetimeWeightedNorm_sq]
  rw [← spacetimeWeightedNorm_sq g r σ u,← spacetimeWeightedNorm_sq g r σ v] at hs
  nlinarith only [hs,hc]

theorem spacetimeWeightedNorm_congr_ae (g : TimeGrid) (r : ℝ → ℝ) (σ : ℝ → BoundedMultiplier ν)
    {u v : ℝ → WeakSobolevJet d n ν S} (h : u =ᵐ[g.timeMeasure] v) :
    spacetimeWeightedNorm g r σ u = spacetimeWeightedNorm g r σ v := by
  unfold spacetimeWeightedNorm spacetimeWeightedSq
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact bochnerL2Norm_congr_ae (h.mono fun t ht => by simp only [parameterTimeField,ht])

end Carleman.WeakSobolevJet
