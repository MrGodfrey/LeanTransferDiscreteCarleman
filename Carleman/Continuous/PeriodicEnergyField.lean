module

public import Carleman.Continuous.FormEnergyClass
public import Carleman.Continuous.PeriodicGraphSpace

/-! The original energy-space field as an actual continuous map on the full periodic graph. -/
@[expose] public noncomputable section
open MeasureTheory
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid)

def periodicEnergy : b.PeriodicGraph g →L[ℝ] Lp V 2 g.timeMeasure :=
  ((b.resolventEnergy 1 zero_le_one).compLpL 2 g.timeMeasure).comp
    ((g.fieldsOperator+g.fieldsValue).comp (b.periodicGraphSubmodule g).subtypeL)

theorem periodicEnergy_eq (p : b.PeriodicGraph g) :
    b.periodicEnergy g p=b.timeEnergy (g.pathL2 p.val.1) p.val.2.2 := rfl

theorem periodicEnergy_embed (p : b.PeriodicGraph g) :
    b.embed.compLp (b.periodicEnergy g p)=g.pathL2 p.val.1 :=
  b.timeEnergy_embed (((b.periodicGraph_mem g p.val).mp p.property).2.1)

theorem periodicEnergy_embed_ae (p : b.PeriodicGraph g) :
    (fun t => b.embed (b.periodicEnergy g p t)) =ᵐ[g.timeMeasure] g.pathL2 p.val.1 := by
  have h := b.embed.coeFn_compLp (b.periodicEnergy g p)
  rw [b.periodicEnergy_embed] at h
  filter_upwards [h] with t ht
  exact ht.symm

end Carleman.CoerciveForm
