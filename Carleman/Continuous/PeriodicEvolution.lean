module

public import Carleman.Continuous.PeriodicGraphEquivalence
public import Carleman.Spatial.MultiplierContinuity
public import Carleman.Periodic.CellIntegral

/-! The actual signed evolution equation is a continuous map from the
complete periodic graph space. Its a.e. interpretation matches B1, including
frozen nodal coefficients, and strong graph limits preserve the equation. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace Carleman

namespace Orientation

def frozenMultiplier (s : Orientation) (g : TimeGrid) (μ : g.Sequence ℝ) :
    BoundedMultiplier g.timeMeasure where
  value := s.extension g μ
  measurable := by
    have he : s.extension g μ = fun t => μ (s.extension g (fun i => i) t) := by
      funext t
      cases s <;> rfl
    rw [he]
    exact (s.aestronglyMeasurable_cell_select g (fun i _ => μ i)
      (fun _ => aestronglyMeasurable_const))
  bound := ∑ i, |μ i|
  bound_nonneg := Finset.sum_nonneg fun i _ => abs_nonneg _
  bounded := Eventually.of_forall fun t => by
    have he : s.extension g μ t = μ (s.extension g (fun i => i) t) := by cases s <;> rfl
    rw [he]
    exact Finset.single_le_sum (fun i _ => abs_nonneg (μ i)) (Finset.mem_univ _)
end Orientation

namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid)

/-- The multiplier norm here may depend on its size; no uniform a priori
estimate is inferred from this continuity statement. -/
def evolutionFields (s : Orientation) (μ : BoundedMultiplier g.timeMeasure) :
    g.PeriodicFields (H := H) →L[ℝ] Lp H 2 g.timeMeasure :=
  s.sign • g.fieldsDerivative + g.fieldsOperator + μ.continuousLinearMap.comp g.fieldsValue

def evolution (s : Orientation) (μ : BoundedMultiplier g.timeMeasure) :
    b.PeriodicGraph g →L[ℝ] Lp H 2 g.timeMeasure :=
  (evolutionFields g s μ).comp (b.periodicGraphSubmodule g).subtypeL

theorem evolution_ae (s : Orientation) (μ : BoundedMultiplier g.timeMeasure)
    (p : b.PeriodicGraph g) :
    b.evolution g s μ p =ᵐ[g.timeMeasure] (fun t => s.sign • p.toTrajectory.derivative t +
      b.operator (p.toTrajectory.domainValue t) + μ.value t • p.toTrajectory.value t) := by
  change s.sign • p.val.2.1 + p.val.2.2 + μ.map (g.pathL2 p.val.1) =ᵐ[g.timeMeasure] _
  filter_upwards [Lp.coeFn_add (s.sign • p.val.2.1 + p.val.2.2) (μ.map (g.pathL2 p.val.1)),
    Lp.coeFn_add (s.sign • p.val.2.1) p.val.2.2, Lp.coeFn_smul s.sign p.val.2.1,
    μ.map_ae (g.pathL2 p.val.1), g.pathL2_ae p.val.1, p.toTrajectory_operator_ae]
    with t ht hsum hsmul hμ hv ha
  simp only [Pi.add_apply, Pi.smul_apply] at ht hsum hsmul
  rw [ht, hsum, hsmul, hμ, hv, ← ha]
  rfl

theorem evolution_eq_iff (s : Orientation) (μ : BoundedMultiplier g.timeMeasure)
    (p : b.PeriodicGraph g) (f : Lp H 2 g.timeMeasure) :
    b.evolution g s μ p = f ↔ ∀ᵐ t ∂g.timeMeasure,
      s.sign • p.toTrajectory.derivative t + b.operator (p.toTrajectory.domainValue t) +
        μ.value t • p.toTrajectory.value t = f t := by
  constructor
  · intro he
    exact (b.evolution_ae g s μ p).symm.trans (by rw [he])
  · intro he
    exact Lp.ext ((b.evolution_ae g s μ p).trans he)

omit [CompleteSpace H] in
/-- A strong limit of genuine graph trajectories retains the original weak
regularity and endpoint traces. This proves preservation, not existence of limits. -/
theorem periodicGraph_mem_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (p : ι → b.PeriodicGraph g) (q : g.PeriodicFields (H := H))
    (htrace : Tendsto (fun i => (p i).val.1) l (𝓝 q.1))
    (hderivative : Tendsto (fun i => (p i).val.2.1) l (𝓝 q.2.1))
    (hoperator : Tendsto (fun i => (p i).val.2.2) l (𝓝 q.2.2)) :
    q ∈ b.periodicGraphSubmodule g := by
  apply (b.periodicGraph_isClosed g).mem_of_tendsto
    (htrace.prodMk_nhds (hderivative.prodMk_nhds hoperator))
  exact Eventually.of_forall fun i => (p i).property

omit [CompleteSpace H] in
/-- The prescribed loads converge to the prescribed equation at the limit. -/
theorem evolution_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (s : Orientation) (μ : BoundedMultiplier g.timeMeasure)
    (p : ι → b.PeriodicGraph g) (q : b.PeriodicGraph g) (f : ι → Lp H 2 g.timeMeasure)
    (F : Lp H 2 g.timeMeasure)
    (hp : Tendsto p l (𝓝 q)) (hf : Tendsto f l (𝓝 F))
    (he : ∀ i, b.evolution g s μ (p i) = f i) : b.evolution g s μ q = F := by
  have h := (b.evolution g s μ).continuous.continuousAt.tendsto.comp hp
  have hfun : (fun i => b.evolution g s μ (p i)) = f := funext he
  change Tendsto (fun i => b.evolution g s μ (p i)) l (𝓝 (b.evolution g s μ q)) at h
  rw [hfun] at h
  exact tendsto_nhds_unique h hf
end CoerciveForm
end Carleman
