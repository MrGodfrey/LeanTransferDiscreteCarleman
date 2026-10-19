module

public import Carleman.Control.TimeCellReconstruction
public import Carleman.Spatial.FiniteCellMultiplier

/-! The original finite-element potential: actual time averages, constant on each time cell. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]

def timeReconstructedPotential (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod ν)) :
    BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod ν) where
  value z := finiteCellFunction g.physicalTimeCell (fun i => (timeCellPotential g b i).value z.2) z.1
  measurable := by
    change AEStronglyMeasurable (fun z : ℝ × Ω => ∑ i,
      (g.physicalTimeCell i).indicator (fun _ => (timeCellPotential g b i).value z.2) z.1)
      ((volume.restrict (Ioc 0 g.period)).prod ν)
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    have he : (fun z : ℝ × Ω => (g.physicalTimeCell i).indicator
        (fun _ => (timeCellPotential g b i).value z.2) z.1)=
      (Prod.fst ⁻¹' g.physicalTimeCell i).indicator (fun z => (timeCellPotential g b i).value z.2) := by
      funext z
      by_cases hz : z.1 ∈ g.physicalTimeCell i <;> simp [hz]
    rw [he]
    exact ((timeCellPotential g b i).measurable.comp_quasiMeasurePreserving quasiMeasurePreserving_snd).indicator
      (measurableSet_Ioc.preimage measurable_fst)
  bound := b.bound
  bound_nonneg := b.bound_nonneg
  bounded := by
    have hc : ∀ i, ∀ᵐ x ∂ν, |(timeCellPotential g b i).value x| ≤ b.bound := by
      intro i
      simpa only [timeCellPotential_bound] using (timeCellPotential g b i).bounded
    filter_upwards [quasiMeasurePreserving_snd.ae (ae_all_iff.mpr hc)] with z hz
    exact finiteCellFunction_bound _ g.physicalTimeCell_disjoint _ b.bound_nonneg hz z.1

theorem timeReconstructedPotential_bound (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod ν)) :
    (timeReconstructedPotential g b).bound=b.bound := rfl

theorem timeReconstructedPotential_on_cell (g : TimeGrid)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 g.period)).prod ν))
    (i : Fin g.steps) {t : ℝ} (ht : t ∈ g.physicalTimeCell i) (x : Ω) :
    (timeReconstructedPotential g b).value (t,x)=(timeCellPotential g b i).value x :=
  finiteCellFunction_on_cell _ g.physicalTimeCell_disjoint _ i ht

def fixedTimePotential (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν)) :
    BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν) := by
  subst T
  exact timeReconstructedPotential g b

theorem fixedTimePotential_bound (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν)) :
    (fixedTimePotential T g hT b).bound=b.bound := by
  subst T
  rfl

theorem fixedTimePotential_value (T : ℝ) (g : TimeGrid) (hT : g.period=T)
    (b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod ν)) (t : ℝ) (x : Ω) :
    (fixedTimePotential T g hT b).value (t,x)=
      finiteCellFunction g.physicalTimeCell (fun i => g.dt⁻¹*∫ s in g.physicalTimeCell i, b.value (s,x)) t := by
  subst T
  rfl

end Carleman
