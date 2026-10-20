module

public import Carleman.Control.TimeReconstructionEstimates

/-! Exact Bochner time pairings for the difference of a full physical test sequence. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {X H : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem timeCellReconstruction_difference_inner (g : TimeGrid) (E : X →ₗᵢ[ℝ] H)
    (y φ : Fin (g.steps+1) → X) :
    inner ℝ (timeCellReconstruction g (fun i => E (y i.succ)))
      (timeCellReconstruction g (fun i => E (g.dt⁻¹ • (φ i.succ-φ i.castSucc)))) =
        ∑ i : Fin g.steps, inner ℝ (y i.succ) (φ i.succ-φ i.castSucc) := by
  rw [timeCellReconstruction_inner]
  simp only [LinearIsometry.inner_map_map,real_inner_smul_right,← Finset.mul_sum,
    ← mul_assoc,mul_inv_cancel₀ g.dt_pos.ne',one_mul]

theorem fixedTimeCellReconstruction_inner (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (u v : Fin g.steps → H) :
    inner ℝ (fixedTimeCellReconstruction T g hT u) (fixedTimeCellReconstruction T g hT v)=
      g.dt*∑ i, inner ℝ (u i) (v i) := by
  subst T
  exact timeCellReconstruction_inner g u v

theorem fixedTimeCellReconstruction_difference_inner (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (E : X →ₗᵢ[ℝ] H) (y φ : Fin (g.steps+1) → X) :
    inner ℝ (fixedTimeCellReconstruction T g hT (fun i => E (y i.succ)))
      (fixedTimeCellReconstruction T g hT (fun i => E (g.dt⁻¹ • (φ i.succ-φ i.castSucc)))) =
        ∑ i : Fin g.steps, inner ℝ (y i.succ) (φ i.succ-φ i.castSucc) := by
  subst T
  exact timeCellReconstruction_difference_inner g E y φ

end Carleman
