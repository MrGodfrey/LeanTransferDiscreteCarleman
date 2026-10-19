module

public import Carleman.Control.TimeCellReconstruction

/-! Norm comparisons for the actual Bochner time reconstruction, including a fixed time domain. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Carleman
variable {H G : Type*} [NormedAddCommGroup H] [NormedAddCommGroup G]

theorem timeCellReconstruction_sub (g : TimeGrid) (u v : Fin g.steps → H) :
    timeCellReconstruction g (fun i => u i-v i)=timeCellReconstruction g u-timeCellReconstruction g v := by
  simp only [timeCellReconstruction,← indicatorConstLp_sub,Finset.sum_sub_distrib]

variable [InnerProductSpace ℝ H] [CompleteSpace H] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem timeCellReconstruction_norm_le (g : TimeGrid) (u : Fin g.steps → H)
    (v : Fin g.steps → G) {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖u i‖ ≤ C*‖v i‖) :
    ‖timeCellReconstruction g u‖ ≤ C*‖timeCellReconstruction g v‖ := by
  have he (w : Fin g.steps → H) :
      ‖timeCellReconstruction g w‖^2=g.dt*∑ i, ‖w i‖^2 := by
    rw [← real_inner_self_eq_norm_sq,timeCellReconstruction_inner]
    simp only [real_inner_self_eq_norm_sq]
  have he' : ‖timeCellReconstruction g v‖^2=g.dt*∑ i, ‖v i‖^2 := by
    rw [← real_inner_self_eq_norm_sq,timeCellReconstruction_inner]
    simp only [real_inner_self_eq_norm_sq]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [he,mul_pow,he']
  calc
    _ ≤ g.dt*∑ i, (C*‖v i‖)^2 := by
      apply mul_le_mul_of_nonneg_left _ g.dt_pos.le
      exact Finset.sum_le_sum (fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr (h i))
    _ = _ := by simp only [mul_pow,← Finset.mul_sum]; ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
def fixedTimeCellReconstruction (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (u : Fin g.steps → H) : Lp H 2 (volume.restrict (Ioc 0 T)) :=
  hT ▸ timeCellReconstruction g u

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem fixedTimeCellReconstruction_sub (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (u v : Fin g.steps → H) :
    fixedTimeCellReconstruction T g hT (fun i => u i-v i)=
      fixedTimeCellReconstruction T g hT u-fixedTimeCellReconstruction T g hT v := by
  subst T
  exact timeCellReconstruction_sub g u v

theorem fixedTimeCellReconstruction_norm_le (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (u : Fin g.steps → H) (v : Fin g.steps → G) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖u i‖ ≤ C*‖v i‖) :
    ‖fixedTimeCellReconstruction T g hT u‖ ≤ C*‖fixedTimeCellReconstruction T g hT v‖ := by
  subst T
  exact timeCellReconstruction_norm_le g u v hC h

end Carleman
