module

public import Carleman.Continuous.WeakIntervalRepresentative

/-! The canonical continuous trace path is a bounded linear operator on
the entire genuine weak H¹ graph, with its explicit interval-length bound. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.TimeGrid
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (g : TimeGrid)

def weakTracePath (z : weakTimeSubmodule (H := H) g) : g.TracePath (H := H) :=
  Classical.choose (g.exists_tracePath z)

theorem weakTracePath_value (z : weakTimeSubmodule (H := H) g) :
    g.pathL2 (g.weakTracePath z)=z.val.1 := Classical.choose_spec (g.exists_tracePath z)

theorem weakTracePath_ae (z : weakTimeSubmodule (H := H) g) :
    z.val.1 =ᵐ[g.timeMeasure] (g.clampPath (g.weakTracePath z) : ℝ → H) := by
  rw [← g.weakTracePath_value z]
  exact g.pathL2_ae _

theorem weakTracePath_weak (z : weakTimeSubmodule (H := H) g) :
    HasWeakTimeDerivative g (g.clampPath (g.weakTracePath z)) z.val.2 :=
  (IsWeakTimeClass.iff_weakDerivative.mp z.property).congr_value (g.weakTracePath_ae z)

theorem weakTracePath_point_bound (z : weakTimeSubmodule (H := H) g)
    (t : Icc (0 : ℝ) g.period) :
    ‖g.weakTracePath z t‖ ≤ Real.sqrt g.period/g.period*‖z.val.1‖+
      Real.sqrt g.period*‖z.val.2‖ := by
  have hc : ContinuousOn (g.clampPath (g.weakTracePath z) : ℝ → H) (Icc 0 g.period) :=
    (g.clampPath (g.weakTracePath z)).continuous.continuousOn
  have hv : (g.memLp_of_continuousOn hc).toLp (g.clampPath (g.weakTracePath z))=z.val.1 := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (g.weakTracePath_ae z).symm
  have he := (g.weakTracePath_weak z).trace_bound hc (Lp.memLp z.val.2) t.property
  rw [hv,Lp.toLp_coeFn,g.clampPath_on _ t t.property] at he
  exact he

theorem weakTracePath_norm_bound (z : weakTimeSubmodule (H := H) g) :
    ‖g.weakTracePath z‖ ≤ (Real.sqrt g.period/g.period+Real.sqrt g.period)*‖z‖ := by
  have hT := g.period_pos
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hu : ‖z.val.1‖ ≤ ‖z‖ := norm_fst_le z.val
  have hd : ‖z.val.2‖ ≤ ‖z‖ := norm_snd_le z.val
  exact (g.weakTracePath_point_bound z t).trans ((add_le_add
    (mul_le_mul_of_nonneg_left hu (by positivity))
    (mul_le_mul_of_nonneg_left hd (by positivity))).trans_eq (by ring))

def weakTracePathCLM : weakTimeSubmodule (H := H) g →L[ℝ] g.TracePath (H := H) :=
  LinearMap.mkContinuous
    { toFun := g.weakTracePath
      map_add' := fun u v => by
        apply g.pathL2_injective
        rw [map_add,g.weakTracePath_value,g.weakTracePath_value,g.weakTracePath_value]
        rfl
      map_smul' := fun c u => by
        apply g.pathL2_injective
        rw [map_smul,g.weakTracePath_value,g.weakTracePath_value]
        rfl }
    (Real.sqrt g.period/g.period+Real.sqrt g.period) (g.weakTracePath_norm_bound)

theorem weakTracePathCLM_value (z : weakTimeSubmodule (H := H) g) :
    g.pathL2 (g.weakTracePathCLM z)=z.val.1 := g.weakTracePath_value z

theorem weakTracePathCLM_eq_of_representative (z : weakTimeSubmodule (H := H) g)
    (p : g.TracePath (H := H)) (hp : g.pathL2 p=z.val.1) : g.weakTracePathCLM z=p :=
  g.pathL2_injective ((g.weakTracePathCLM_value z).trans hp.symm)

def weakIntervalTrace (t : Icc (0 : ℝ) g.period) : weakTimeSubmodule (H := H) g →L[ℝ] H :=
  (ContinuousMap.evalCLM ℝ t).comp g.weakTracePathCLM

theorem weakIntervalTrace_bound (z : weakTimeSubmodule (H := H) g)
    (t : Icc (0 : ℝ) g.period) :
    ‖g.weakIntervalTrace t z‖ ≤ Real.sqrt g.period/g.period*‖z.val.1‖+
      Real.sqrt g.period*‖z.val.2‖ := g.weakTracePath_point_bound z t

theorem weakIntervalTrace_fundamental (z : weakTimeSubmodule (H := H) g)
    (a b : Icc (0 : ℝ) g.period) :
    g.weakIntervalTrace b z-g.weakIntervalTrace a z=∫ t in a.val..b.val, z.val.2 t := by
  have he := (g.weakTracePath_weak z).integral_eq_sub
    (g.clampPath (g.weakTracePath z)).continuous.continuousOn (Lp.memLp z.val.2) a.property b.property
  rw [g.clampPath_on _ a a.property,g.clampPath_on _ b b.property] at he
  exact he.symm

end Carleman.TimeGrid
