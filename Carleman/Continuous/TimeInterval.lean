module

public import Carleman.Continuous.WeakSolution
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.Order.ProjIcc

/-! Continuous H representatives on the closed period, with a bounded
linear extension to real time and their actual Bochner L² classes. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace Carleman.TimeGrid
variable (g : TimeGrid) {H : Type*} [NormedAddCommGroup H]

abbrev TracePath := C(Icc (0 : ℝ) g.period, H)

instance timeMeasure_finite : IsFiniteMeasure g.timeMeasure := by
  dsimp [timeMeasure]
  infer_instance

def clampPath (u : g.TracePath (H := H)) : ℝ →ᵇ H :=
  (BoundedContinuousFunction.mkOfCompact u).compContinuous
    ⟨projIcc 0 g.period g.period_pos.le, continuous_projIcc⟩

theorem clampPath_apply (u : g.TracePath (H := H)) (t : ℝ) :
    g.clampPath u t = u (projIcc 0 g.period g.period_pos.le t) := rfl

theorem clampPath_on (u : g.TracePath (H := H)) (t : ℝ) (ht : t ∈ Icc 0 g.period) :
    g.clampPath u t = u ⟨t,ht⟩ := by simp [clampPath, projIcc_of_mem g.period_pos.le ht]

variable [NormedSpace ℝ H]

def clampPathCLM : g.TracePath (H := H) →L[ℝ] (ℝ →ᵇ H) :=
  LinearMap.mkContinuous
    { toFun := g.clampPath
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun u => by
      simp only [one_mul]
      exact BoundedContinuousFunction.norm_le (norm_nonneg u) |>.mpr
        (fun t => u.norm_coe_le_norm _))

def pathL2 : g.TracePath (H := H) →L[ℝ] Lp H 2 g.timeMeasure :=
  (BoundedContinuousFunction.toLp 2 g.timeMeasure ℝ).comp g.clampPathCLM

theorem pathL2_ae (u : g.TracePath (H := H)) :
    g.pathL2 u =ᵐ[g.timeMeasure] (g.clampPath u : ℝ → H) :=
  BoundedContinuousFunction.coeFn_toLp 2 g.timeMeasure ℝ (g.clampPath u)

theorem pathL2_memLp (u : g.TracePath (H := H)) :
    MemLp (g.clampPath u : ℝ → H) 2 g.timeMeasure :=
  (Lp.memLp (g.pathL2 u)).ae_eq (g.pathL2_ae u)

end Carleman.TimeGrid
