module

public import Carleman.Spatial.BoundedMultiplierAverage
public import Carleman.Transfer.Weights
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The original backward-Euler time cells and actual time-averaged L∞ potential. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace Carleman
namespace TimeGrid

def physicalTimeCell (g : TimeGrid) (i : Fin g.steps) : Set ℝ :=
  Ioc (g.nodeTime i) (g.nodeTime i+g.dt)

instance physicalTimeCell_finite (g : TimeGrid) (i : Fin g.steps) :
    IsFiniteMeasure (volume.restrict (g.physicalTimeCell i)) := by
  dsimp only [physicalTimeCell]
  infer_instance

theorem physicalTimeCell_subset (g : TimeGrid) (i : Fin g.steps) :
    g.physicalTimeCell i ⊆ Ioc 0 g.period := by
  intro t ht
  have hi : (i.val:ℝ)+1 ≤ g.steps := by exact_mod_cast i.isLt
  exact ⟨lt_of_le_of_lt (g.nodeTime_nonneg i) ht.1,
    ht.2.trans (by dsimp [nodeTime,period]; nlinarith [mul_le_mul_of_nonneg_right hi g.dt_pos.le])⟩

theorem physicalTimeCell_volume (g : TimeGrid) (i : Fin g.steps) :
    volume.real (g.physicalTimeCell i) = g.dt := by
  rw [physicalTimeCell,Real.volume_real_Ioc_of_le (by linarith [g.dt_pos])]
  ring

theorem physicalTimeCell_restrict_le (g : TimeGrid) (i : Fin g.steps) :
    volume.restrict (g.physicalTimeCell i) ≤ volume.restrict (Ioc 0 g.period) :=
  Measure.restrict_mono (g.physicalTimeCell_subset i) le_rfl

end TimeGrid

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]

def timeCellPotential (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod ν)) (i : Fin g.steps) :
    BoundedMultiplier ν :=
  (b.ofMeasureLE (Measure.prod_mono (g.physicalTimeCell_restrict_le i) le_rfl)).averageFirst
    g.dt g.dt_pos (by simpa only [Measure.real,Measure.restrict_apply_univ] using
      g.physicalTimeCell_volume i)

theorem timeCellPotential_value (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod ν)) (i : Fin g.steps) (x : Ω) :
    (timeCellPotential g b i).value x = g.dt⁻¹ * ∫ t in g.physicalTimeCell i, b.value (t,x) := rfl

theorem timeCellPotential_bound (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod ν)) (i : Fin g.steps) :
    (timeCellPotential g b i).bound = b.bound := by
  unfold timeCellPotential
  rw [BoundedMultiplier.averageFirst_bound,BoundedMultiplier.ofMeasureLE_bound]

theorem timeCellPotential_congr (g : TimeGrid)
    (b c : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod ν))
    (h : b.value =ᵐ[(volume.restrict (Ioc 0 g.period)).prod ν] c.value) (i : Fin g.steps) :
    (timeCellPotential g b i).value =ᵐ[ν] (timeCellPotential g c i).value := by
  apply BoundedMultiplier.averageFirst_congr
  exact ae_mono (Measure.prod_mono (g.physicalTimeCell_restrict_le i) le_rfl) h

theorem timeCellPotential_setIntegral [IsFiniteMeasure ν] (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod ν))
    (i : Fin g.steps) (K : Set Ω) :
    (∫ x in K, (timeCellPotential g b i).value x ∂ν) =
      g.dt⁻¹ * ∫ t in g.physicalTimeCell i, ∫ x in K, b.value (t,x) ∂ν :=
  BoundedMultiplier.averageFirst_setIntegral _ _ _ _ _

end Carleman
