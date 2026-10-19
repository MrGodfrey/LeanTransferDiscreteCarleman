module

public import Carleman.Control.TimeCellReconstruction
public import Carleman.Spatial.FiniteCellStrongConvergence

/-! Actual time-cell averages on a fixed interval converge for arbitrary scalar L² data. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman

def fixedTimeCellIsometry (T : ℝ) (g : TimeGrid) (hT : g.period=T) :
    PhysicalFiniteSpace (Fin g.steps) g.dt g.dt_pos →ₗᵢ[ℝ] Lp ℝ 2 (volume.restrict (Ioc 0 T)) :=
  finiteCellIsometry g.physicalTimeCell (fun _ => measurableSet_Ioc) g.dt_pos
    g.physicalTimeCell_disjoint (by intro i; rw [← hT]; exact g.physicalTimeCell_restrict_volume i)

theorem fixedTimeCellIsometry_adjoint_average (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (u : Lp ℝ 2 (volume.restrict (Ioc 0 T))) (i : Fin g.steps) :
    ((fixedTimeCellIsometry T g hT).toContinuousLinearMap.adjoint u) i=
      g.dt⁻¹ * ∫ t in g.physicalTimeCell i, u t := by
  rw [fixedTimeCellIsometry,finiteCellIsometry_adjoint]
  congr 1
  rw [Measure.restrict_restrict (show MeasurableSet (g.physicalTimeCell i) from measurableSet_Ioc),
    inter_eq_left.mpr (by rw [← hT]; exact g.physicalTimeCell_subset i)]

theorem fixedTimeCell_uncovered_volume (T : ℝ) (hTpos : 0 ≤ T) (g : TimeGrid) (hT : g.period=T) :
    (volume.restrict (Ioc 0 T)).real (⋃ i, g.physicalTimeCell i)ᶜ=0 := by
  rw [measureReal_compl (MeasurableSet.iUnion (fun i =>
      (show MeasurableSet (g.physicalTimeCell i) from measurableSet_Ioc))),
    finiteCells_union_volume g.physicalTimeCell (fun _ => measurableSet_Ioc) g.physicalTimeCell_disjoint
      (by intro i; rw [← hT]; exact g.physicalTimeCell_restrict_volume i)]
  have hfull : (volume.restrict (Ioc 0 T)).real univ=T := by
    simp only [Measure.real,Measure.restrict_apply_univ]
    rw [← Measure.real,Real.volume_real_Ioc_of_le hTpos,sub_zero]
  rw [hfull,Fintype.card_fin,show (g.steps:ℝ)*g.dt=T from hT,sub_self]

theorem fixedTimeCell_average_strong_convergence (T : ℝ) (hTpos : 0 ≤ T)
    (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T)
    (htlim : Tendsto (fun n => (g n).dt) atTop (𝓝 0))
    (u : Lp ℝ 2 (volume.restrict (Ioc 0 T))) :
    Tendsto (fun n => fixedTimeCellIsometry T (g n) (hT n)
      ((fixedTimeCellIsometry T (g n) (hT n)).toContinuousLinearMap.adjoint u)) atTop (𝓝 u) := by
  have hp n i : (g n).nodeTime i ∈ Icc 0 T := by
    have he := (g n).physicalTimeCell_subset i
      (show (g n).nodeTime i+(g n).dt ∈ (g n).physicalTimeCell i from
        ⟨by linarith [(g n).dt_pos],le_rfl⟩)
    rw [hT n] at he
    exact ⟨(g n).nodeTime_nonneg i,by linarith [(g n).dt_pos,he.2]⟩
  have hinc n i : (g n).physicalTimeCell i ⊆ Icc 0 T := by
    intro t ht
    have he := (g n).physicalTimeCell_subset i ht
    rw [hT n] at he
    exact ⟨he.1.le,he.2⟩
  have hd n i t (ht : t ∈ (g n).physicalTimeCell i) : dist t ((g n).nodeTime i) ≤ (g n).dt := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr ht.1)]
    linarith [ht.2]
  have hstrip : Tendsto (fun n => (volume.restrict (Ioc 0 T)).real
      (⋃ i, (g n).physicalTimeCell i)ᶜ) atTop (𝓝 0) := by
    simp_rw [fixedTimeCell_uncovered_volume T hTpos _ (hT _)]
    exact tendsto_const_nhds
  exact finiteCell_average_strong_convergence (fun n => (g n).physicalTimeCell)
    (fun _ _ => measurableSet_Ioc) (fun n => (g n).dt) (fun n => (g n).dt_pos)
    (fun n => (g n).physicalTimeCell_disjoint)
    (by intro n i; rw [← hT n]; exact (g n).physicalTimeCell_restrict_volume i)
    (Icc 0 T) isCompact_Icc (fun n => (g n).nodeTime) hp hinc
    (fun n => (g n).dt) htlim hd hstrip u

end Carleman
