module

public import Carleman.Spatial.WeightedTime
public import Carleman.Weights.AllowedFormBounds
public import Carleman.Continuous.BochnerNormAlgebra

/-! The actual allowed spatial multiplier acting on Bochner time L² classes.
Inverse weights and pairings are proved on a.e. representatives. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.SpatialProfile
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : Measure Ω} (ρ : SpatialProfile ν)
  (g : TimeGrid) (w : TimeWeight) (τ : ℝ)
  (hq : AEStronglyMeasurable w.q g.timeMeasure)

/-- Multiplication by q^tau exp(q rho), at the actual time variable. -/
def timeMap : Lp (Lp E 2 ν) 2 g.timeMeasure →ₗ[ℝ] Lp (Lp E 2 ν) 2 g.timeMeasure where
  toFun u := (ρ.memLp_map w τ hq (Lp.memLp u)).toLp (fun t => (ρ.multiplier w τ t).map (u t))
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(ρ.memLp_map w τ hq (Lp.memLp (u+v))).coeFn_toLp,
      (ρ.memLp_map w τ hq (Lp.memLp u)).coeFn_toLp,
      (ρ.memLp_map w τ hq (Lp.memLp v)).coeFn_toLp, Lp.coeFn_add u v,
      Lp.coeFn_add ((ρ.memLp_map w τ hq (Lp.memLp u)).toLp _) ((ρ.memLp_map w τ hq (Lp.memLp v)).toLp _)]
      with t huv hu hv ha hb
    simp only [Pi.add_apply] at ha hb
    rw [huv, hb, hu, hv, ha, BoundedMultiplier.map_add]
  map_smul' c u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(ρ.memLp_map w τ hq (Lp.memLp (c • u))).coeFn_toLp,
      (ρ.memLp_map w τ hq (Lp.memLp u)).coeFn_toLp, Lp.coeFn_smul c u,
      Lp.coeFn_smul c ((ρ.memLp_map w τ hq (Lp.memLp u)).toLp _)] with t hcu hu ha hb
    simp only [Pi.smul_apply] at ha hb
    rw [hcu, hb, hu, ha, BoundedMultiplier.map_smul]

theorem timeMap_ae (u : Lp (Lp E 2 ν) 2 g.timeMeasure) :
    ρ.timeMap g w τ hq u =ᵐ[g.timeMeasure] (fun t => (ρ.multiplier w τ t).map (u t)) :=
  (ρ.memLp_map w τ hq (Lp.memLp u)).coeFn_toLp

theorem timeMap_toLp {u : ℝ → Lp E 2 ν} (hu : MemLp u 2 g.timeMeasure) :
    ρ.timeMap g w τ hq (hu.toLp u) =
      (ρ.memLp_map w τ hq hu).toLp (fun t => (ρ.multiplier w τ t).map (u t)) := by
  apply Lp.ext
  filter_upwards [ρ.timeMap_ae g w τ hq (hu.toLp u), hu.coeFn_toLp,
    (ρ.memLp_map w τ hq hu).coeFn_toLp] with t h1 h2 h3
  rw [h1, h2, h3]

/-- This global bound proves continuity only; uniform error estimates never use it. -/
theorem timeMap_norm_le (u : Lp (Lp E 2 ν) 2 g.timeMeasure) :
    ‖ρ.timeMap g w τ hq u‖ ≤
      (max 1 (w.max^τ) * Real.exp (ρ.bound*w.max)) * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ρ.timeMap_ae g w τ hq u] with t ht
  rw [ht]
  exact ρ.seminorm_global_le w τ t (u t)

theorem timeMap_inverse (u : Lp (Lp E 2 ν) 2 g.timeMeasure) :
    ρ.timeMap g w τ hq (ρ.neg.timeMap g w (-τ) hq u) = u := by
  apply Lp.ext
  filter_upwards [ρ.timeMap_ae g w τ hq (ρ.neg.timeMap g w (-τ) hq u),
    ρ.neg.timeMap_ae g w (-τ) hq u] with t h1 h2
  rw [h1, h2, ρ.multiplier_inverse_map]

theorem timeMap_inner_inverse (u v : Lp (Lp E 2 ν) 2 g.timeMeasure) :
    inner ℝ (ρ.timeMap g w τ hq u) (ρ.neg.timeMap g w (-τ) hq v) = inner ℝ u v := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ρ.timeMap_ae g w τ hq u, ρ.neg.timeMap_ae g w (-τ) hq v] with t h1 h2
  rw [h1,h2]
  exact BoundedMultiplier.inner_inverse _ _
    (Filter.Eventually.of_forall (ρ.multiplier_inverse w τ t)) _ _

theorem timeMap_inner_twice (u : Lp (Lp E 2 ν) 2 g.timeMeasure) :
    inner ℝ u (ρ.timeMap g w τ hq (ρ.timeMap g w τ hq u)) = ‖ρ.timeMap g w τ hq u‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ρ.timeMap_ae g w τ hq (ρ.timeMap g w τ hq u),
    ρ.timeMap_ae g w τ hq u] with t h1 h2
  rw [h1,h2,BoundedMultiplier.inner_map_twice, real_inner_self_eq_norm_sq]

end Carleman.SpatialProfile
