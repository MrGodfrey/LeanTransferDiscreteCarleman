module

public import Carleman.Spatial.SpacetimeNormAlgebra
public import Carleman.Spatial.WeightedEnergySeminorm
public import Carleman.Weights.WeightedAffineDefect

/-! The actual piecewise constant weak Sobolev energy is controlled by its
nodal energy. The enlarged exponent is used only for analytic cell bounds,
never as an additional numerical allowed-weight assumption. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman.WeakSobolevJet
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [SFinite ν] {S : Set (SpatialCoordinates d)}
  (g : TimeGrid) (s : Orientation) (w : TimeWeight) (ρ : SpatialProfile ν)

theorem spacetimeWeightedNorm_extension_le {β τ τStar : ℝ}
    (h : TimeWeightRegularity w g β) (hτStar : 0 ≤ τStar) (hτ : |τ| ≤ τStar)
    (hmesh : g.dt*w.max^2 ≤ cellThreshold β (τStar+n) ρ.bound)
    (u : g.Sequence (WeakSobolevJet d n ν S)) :
    spacetimeWeightedNorm g w.q (ρ.multiplier w τ) (s.extension g u) ≤
      3*g.weightedNorm (fun i => weightedSeminorm (w.nodes g i) (ρ.multiplier w τ (g.nodeTime i))) u := by
  have hfields (k : Fin (n+1)) : MemLp
      (parameterTimeField w.q (ρ.multiplier w τ) (s.extension g u) k) 2 g.timeMeasure := by
    simpa only [one_mul] using memLp_parameterTimeField g w ρ τ 1 h.aestronglyMeasurable
      (s.memLp_extension g u) k
  have hb := h.mesh_bounds (τStar+n) ρ.bound (by positivity) ρ.bound_nonneg hmesh
  have hcomponent (k : Fin (n+1)) :
      (bochnerL2Norm g.timeMeasure (parameterTimeField w.q (ρ.multiplier w τ) (s.extension g u) k))^2 ≤
        9*(g.dt*∑ i, (w.nodes g i^(n-k.val)*(ρ.multiplier w τ (g.nodeTime i)).seminorm (field k (u i)))^2) := by
    have hk : |τ+(((n-k.val)*2:ℕ):ℝ)/2| ≤ τStar+n := by
      have ht := abs_add_le τ ((((n-k.val)*2:ℕ):ℝ)/2)
      have hn : ((n-k.val:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k.val
      simp only [Nat.cast_mul,Nat.cast_ofNat,mul_div_cancel_right₀ _ (by norm_num : (2:ℝ) ≠ 0),
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n-k.val))] at ht ⊢
      linarith only [ht,hτ,hn]
    have hc := (ρ.powerSq_timeSq_comparison_comp h (field k) s τ (((n-k.val)*2:ℕ):ℝ)
      (τStar+n) hk hb.1 hb.2 u).2.1
    have he : (bochnerL2Norm g.timeMeasure
        (parameterTimeField w.q (ρ.multiplier w τ) (s.extension g u) k))^2 =
        timeSq g w.q (((n-k.val)*2:ℕ):ℝ)
          (fun t => (ρ.multiplier w τ t).seminorm.comp (field k)) (s.extension g u) := by
      rw [bochnerL2Norm_sq_integral (hfields k)]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      change ‖parameterTimeField w.q (ρ.multiplier w τ) (s.extension g u) k t‖^2 = _
      rw [parameterTimeField_norm _ _ _ _ (w.nonneg t)]
      simp only [timeDensity,Real.rpow_natCast,pow_mul,mul_pow,Seminorm.comp_apply]
    rw [he]
    convert hc using 1
    simp only [TimeGrid.powerSq,Real.rpow_natCast,pow_mul,mul_pow,Seminorm.comp_apply]
  apply (sq_le_sq₀ (spacetimeWeightedNorm_nonneg _ _ _ _)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  rw [mul_pow,spacetimeWeightedNorm_sq,Real.sq_sqrt (g.weightedSq_nonneg _ _)]
  calc
    _ ≤ ∑ k : Fin (n+1), 9*(g.dt*∑ i,
        (w.nodes g i^(n-k.val)*(ρ.multiplier w τ (g.nodeTime i)).seminorm (field k (u i)))^2) :=
      Finset.sum_le_sum fun k _ => hcomponent k
    _ = _ := by
      have hs (i : g.Index) : weightedSeminorm (w.nodes g i) (ρ.multiplier w τ (g.nodeTime i)) (u i) =
          weightedNorm (w.nodes g i) (ρ.multiplier w τ (g.nodeTime i)) (u i) :=
        weightedSeminorm_apply (w.nonneg _) _ _
      simp only [TimeGrid.weightedSq,hs,weightedNorm_sq,weightedSq,
        ← Finset.mul_sum]
      rw [Finset.sum_comm]
      norm_num

end Carleman.WeakSobolevJet
