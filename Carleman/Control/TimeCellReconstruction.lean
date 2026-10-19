module

public import Carleman.Control.TimeCellAverage
public import Carleman.Control.PhysicalEnergy
public import Mathlib.MeasureTheory.Function.L2Space

/-! The actual piecewise-constant Bochner L² reconstruction on all physical time steps. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
namespace TimeGrid

theorem physicalTimeCell_disjoint (g : TimeGrid) :
    Pairwise fun i j : Fin g.steps => Disjoint (g.physicalTimeCell i) (g.physicalTimeCell j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hh : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast hlt
    have hm := mul_le_mul_of_nonneg_right hh g.dt_pos.le
    dsimp only [physicalTimeCell,mem_Ioc,nodeTime] at hi hj
    nlinarith [hi.1,hi.2,hj.1,hj.2]
  · have hh : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast hlt
    have hm := mul_le_mul_of_nonneg_right hh g.dt_pos.le
    dsimp only [physicalTimeCell,mem_Ioc,nodeTime] at hi hj
    nlinarith [hi.1,hi.2,hj.1,hj.2]

theorem physicalTimeCell_restrict_volume (g : TimeGrid) (i : Fin g.steps) :
    (volume.restrict (Ioc 0 g.period)).real (g.physicalTimeCell i) = g.dt := by
  rw [Measure.real,Measure.restrict_apply (show MeasurableSet (g.physicalTimeCell i) from measurableSet_Ioc),
    Set.inter_eq_left.mpr (g.physicalTimeCell_subset i)]
  exact g.physicalTimeCell_volume i

end TimeGrid

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (g : TimeGrid)

def timeCellReconstruction (u : Fin g.steps → H) : Lp H 2 (volume.restrict (Ioc 0 g.period)) :=
  ∑ i, indicatorConstLp 2 (show MeasurableSet (g.physicalTimeCell i) from measurableSet_Ioc)
    (measure_ne_top _ _) (u i)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem timeCellReconstruction_ae (u : Fin g.steps → H) :
    timeCellReconstruction g u =ᵐ[volume.restrict (Ioc 0 g.period)]
      fun t => ∑ i, (g.physicalTimeCell i).indicator (fun _ => u i) t := by
  apply (Lp.coeFn_finsetSum Finset.univ _).trans
  have hi (i : Fin g.steps) :
      (indicatorConstLp 2 (show MeasurableSet (g.physicalTimeCell i) from measurableSet_Ioc)
        (measure_ne_top (volume.restrict (Ioc 0 g.period)) _) (u i))
      =ᵐ[volume.restrict (Ioc 0 g.period)] (g.physicalTimeCell i).indicator (fun _ => u i) :=
    indicatorConstLp_coeFn
  have hh := eventuallyEq_sum (s := Finset.univ) fun i _ => hi i
  filter_upwards [hh] with x hx
  simpa only [Finset.sum_apply] using hx

theorem timeCellReconstruction_inner (u v : Fin g.steps → H) :
    inner ℝ (timeCellReconstruction g u) (timeCellReconstruction g v) =
      g.dt * ∑ i, inner ℝ (u i) (v i) := by
  have hcell (i j : Fin g.steps) :
      (volume.restrict (Ioc 0 g.period)).real (g.physicalTimeCell i ∩ g.physicalTimeCell j) =
        if i=j then g.dt else 0 := by
    by_cases hij : i=j
    · subst j
      simp only [inter_self,g.physicalTimeCell_restrict_volume,ite_true]
    · rw [Set.disjoint_iff_inter_eq_empty.mp (g.physicalTimeCell_disjoint hij)]
      simp only [Measure.real,measure_empty,ENNReal.toReal_zero,ite_eq_right hij]
  simp only [timeCellReconstruction,sum_inner,inner_sum,
    L2.inner_indicatorConstLp_indicatorConstLp,hcell,smul_eq_mul,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact (Finset.mul_sum ..).symm

theorem timeCellReconstruction_norm (u : Fin g.steps → H) :
    ‖timeCellReconstruction g u‖ = Physical.controlNorm g.dt u := by
  have he : ‖timeCellReconstruction g u‖^2 = g.dt*∑ i, ‖u i‖^2 := by
    rw [← real_inner_self_eq_norm_sq,timeCellReconstruction_inner]
    simp only [real_inner_self_eq_norm_sq]
  rw [Physical.controlNorm,← he,Real.sqrt_sq (norm_nonneg _)]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem timeCellReconstruction_on_cell (u : Fin g.steps → H) (i : Fin g.steps) :
    ∀ᵐ t ∂volume.restrict (g.physicalTimeCell i), timeCellReconstruction g u t = u i := by
  have he := ae_mono (g.physicalTimeCell_restrict_le i) (timeCellReconstruction_ae g u)
  filter_upwards [he,ae_restrict_mem (show MeasurableSet (g.physicalTimeCell i) from measurableSet_Ioc)]
    with t ht hti
  rw [ht]
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hti _
  · intro j _ hji
    exact Set.indicator_of_notMem (fun htj =>
      Set.disjoint_left.mp (g.physicalTimeCell_disjoint hji) htj hti) _
  · simp

end Carleman
