module

public import Carleman.Control.FixedTimeCellStrongConvergence
public import Carleman.Control.TimeReconstructionEstimates
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Actual backward time differences are the cell averages of the derivative; hence they converge strongly. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology BigOperators NNReal
namespace Carleman

theorem fixedTimeCellIsometry_eq_reconstruction (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (v : PhysicalFiniteSpace (Fin g.steps) g.dt g.dt_pos) :
    fixedTimeCellIsometry T g hT v=fixedTimeCellReconstruction T g hT (fun i => v i) := by
  subst T
  apply Lp.ext
  exact (finiteCellLinear_ae g.physicalTimeCell (fun _ => measurableSet_Ioc) g.dt_pos v).trans
    (timeCellReconstruction_ae g (fun i => v i)).symm

theorem timeCell_derivative_average (g : TimeGrid) (φ f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 g.period)))
    (hd : ∀ t∈Icc 0 g.period, HasDerivWithinAt φ (f t) (Icc 0 g.period) t) (i : Fin g.steps) :
    g.dt⁻¹*∫ t in g.physicalTimeCell i, f t=
      g.dt⁻¹*(φ (((i.val:ℝ)+1)*g.dt)-φ ((i.val:ℝ)*g.dt)) := by
  apply congrArg (g.dt⁻¹ * ·)
  have hab : g.nodeTime i ≤ g.nodeTime i+g.dt := by linarith [g.dt_pos]
  have hdom : Icc (g.nodeTime i) (g.nodeTime i+g.dt) ⊆ Icc 0 g.period := by
    intro t ht
    have hn : (i.val:ℝ)+1 ≤ g.steps := by exact_mod_cast i.isLt
    exact ⟨(g.nodeTime_nonneg i).trans ht.1, ht.2.trans (by dsimp [TimeGrid.nodeTime,TimeGrid.period]; nlinarith [g.dt_pos])⟩
  have hfi : IntegrableOn f (g.physicalTimeCell i) :=
    (hf.integrable (by norm_num)).mono_measure (g.physicalTimeCell_restrict_le i)
  have hinterval : IntervalIntegrable f volume (g.nodeTime i) (g.nodeTime i+g.dt) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hfi
  have hc : ContinuousOn φ (Icc 0 g.period) := fun t ht => (hd t ht).continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hc.mono hdom)
    (fun t ht => (hd t (hdom ⟨ht.1.le,ht.2.le⟩)).hasDerivAt
      (Icc_mem_nhds ((g.nodeTime_nonneg i).trans_lt ht.1)
        (ht.2.trans_le (hdom ⟨hab,le_rfl⟩).2))) hinterval
  rw [intervalIntegral.integral_of_le hab] at he
  simpa only [TimeGrid.physicalTimeCell,TimeGrid.nodeTime,add_mul,one_mul] using he

theorem timeCell_test_difference_eq_projection (g : TimeGrid) (φ f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 g.period)))
    (hd : ∀ t∈Icc 0 g.period, HasDerivWithinAt φ (f t) (Icc 0 g.period) t) :
    timeCellReconstruction g (fun i => g.dt⁻¹*(φ (((i.val:ℝ)+1)*g.dt)-φ ((i.val:ℝ)*g.dt)))=
      fixedTimeCellIsometry g.period g rfl
        ((fixedTimeCellIsometry g.period g rfl).toContinuousLinearMap.adjoint (hf.toLp f)) := by
  rw [fixedTimeCellIsometry_eq_reconstruction]
  change timeCellReconstruction g _=timeCellReconstruction g _
  congr 1
  funext i
  rw [fixedTimeCellIsometry_adjoint_average]
  apply (timeCell_derivative_average g φ f hf hd i).symm.trans
  apply congrArg (g.dt⁻¹ * ·)
  exact integral_congr_ae (Filter.EventuallyEq.symm (ae_mono (g.physicalTimeCell_restrict_le i) hf.coeFn_toLp))

theorem fixedTimeCell_test_difference_eq_projection (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (φ f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Ioc 0 T)))
    (hd : ∀ t∈Icc 0 T, HasDerivWithinAt φ (f t) (Icc 0 T) t) :
    fixedTimeCellReconstruction T g hT
      (fun i => g.dt⁻¹*(φ (((i.val:ℝ)+1)*g.dt)-φ ((i.val:ℝ)*g.dt)))=
      fixedTimeCellIsometry T g hT
        ((fixedTimeCellIsometry T g hT).toContinuousLinearMap.adjoint (hf.toLp f)) := by
  subst T
  exact timeCell_test_difference_eq_projection g φ f hf hd

theorem time_test_difference_strong_convergence (T : ℝ) (hTpos : 0 ≤ T)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (φ f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Ioc 0 T)))
    (hd : ∀ t∈Icc 0 T, HasDerivWithinAt φ (f t) (Icc 0 T) t) :
    Tendsto (fun n => fixedTimeCellReconstruction T (g n) (hT n)
      (fun i => (g n).dt⁻¹*(φ (((i.val:ℝ)+1)*(g n).dt)-φ ((i.val:ℝ)*(g n).dt))))
      atTop (𝓝 (hf.toLp f)) := by
  simp_rw [fixedTimeCell_test_difference_eq_projection T _ _ φ f hf hd]
  exact fixedTimeCell_average_strong_convergence T hTpos g hT htlim (hf.toLp f)

end Carleman
