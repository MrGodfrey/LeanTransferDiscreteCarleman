module

public import Carleman.Continuous.TimeGraphBound
public import Carleman.Continuous.HarmonicDensity

/-! Arbitrary Bochner L² loads: the proved finite harmonic density,
integrated graph bounds and H¹-to-C control give a closed, surjective range.
No density, limit, trace convergence or existence premise is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A proved norm bound on a linear core gives closed range on its closure. -/
theorem closedRange_on_core_closure (S : Submodule ℝ E) (L : E →L[ℝ] F)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x ∈ S, ‖x‖ ≤ C*‖L x‖) :
    IsClosed (Set.range (L.comp S.topologicalClosure.subtypeL)) := by
  let : IsClosed (S.topologicalClosure : Set E) := S.isClosed_topologicalClosure
  let : CompleteSpace S.topologicalClosure := IsClosed.completeSpace_coe
  have hbound : ∀ x : S.topologicalClosure, ‖x‖ ≤ C*‖(L.comp S.topologicalClosure.subtypeL) x‖ := by
    intro x
    exact (closure_minimal hb
      (isClosed_le continuous_norm (continuous_const.mul L.continuous.norm))) x.property
  have hanti := ContinuousLinearMap.antilipschitz_of_bound
    (L.comp S.topologicalClosure.subtypeL) (K := C.toNNReal) (fun x => by
      simpa only [Real.coe_toNNReal C hC] using hbound x)
  exact hanti.isClosed_range (L.comp S.topologicalClosure.subtypeL).uniformContinuous
end Carleman

namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (s : Orientation) (r : ℝ) (hr : 0 ≤ r)
include hr

/-- Every L² load has a solution in the closure of the actual classical graph core. -/
theorem exists_constant_periodic_in_core_closure (f : Lp H 2 g.timeMeasure) :
    ∃ p : b.PeriodicGraph g, p ∈ (b.regularTimeCore g).topologicalClosure ∧
      b.evolution g s (g.constantMultiplier r) p = f := by
  let S := (b.regularTimeCore g).topologicalClosure
  let L : S →L[ℝ] Lp H 2 g.timeMeasure := (b.evolution g s (g.constantMultiplier r)).comp S.subtypeL
  obtain ⟨C, hC, hbound⟩ := b.regularTimeCore_norm_bound g s r hr
  have hclosed := closedRange_on_core_closure (E := b.PeriodicGraph g) (F := Lp H 2 g.timeMeasure)
    (b.regularTimeCore g) (b.evolution g s (g.constantMultiplier r)) C hC.le hbound
  change IsClosed (Set.range L) at hclosed
  have hspan : g.harmonicSpan (H := H) ≤ L.range := by
    apply Submodule.span_le.mpr
    rintro v ⟨n, a, k, rfl⟩
    refine ⟨⟨b.frequencyGraph g s r hr n a k, ?_⟩, ?_⟩
    · exact (b.regularTimeCore g).le_topologicalClosure (b.frequencyGraph_mem_core g s r hr n a k)
    · exact b.frequencyGraph_equation g s r hr n a k
  have hdense : Dense (Set.range L) := (g.harmonicSpan_dense (H := H)).mono hspan
  have hf : f ∈ Set.range L := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
    trivial
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.val, p.property, hp⟩

theorem evolution_constant_surjective : Function.Surjective (b.evolution g s (g.constantMultiplier r)) := by
  intro f
  obtain ⟨p, _, hp⟩ := b.exists_constant_periodic_in_core_closure g s r hr f
  exact ⟨p, hp⟩

theorem existsUnique_constant_periodic (f : Lp H 2 g.timeMeasure) :
    ∃! p : b.PeriodicGraph g, b.evolution g s (g.constantMultiplier r) p = f := by
  obtain ⟨p, hp⟩ := b.evolution_constant_surjective g s r hr f
  exact ⟨p, hp, fun q hq => b.evolution_injective g s (g.constantMultiplier r)
    (Filter.Eventually.of_forall fun _ => hr) (hq.trans hp.symm)⟩

omit s r hr in
/-- Density is now proved in the full graph topology, including the continuous trace. -/
theorem regularTimeCore_dense : Dense (b.regularTimeCore g : Set (b.PeriodicGraph g)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  intro p _
  obtain ⟨q, hq, he⟩ := b.exists_constant_periodic_in_core_closure g Carleman.Orientation.plus 0 le_rfl
    (b.evolution g Carleman.Orientation.plus (g.constantMultiplier 0) p)
  have hpq := b.evolution_injective g Carleman.Orientation.plus (g.constantMultiplier 0)
    (Filter.Eventually.of_forall fun _ => le_rfl) he
  exact hpq ▸ hq

omit s r hr in
/-- The time/operator cancellation extends to every original weak graph trajectory. -/
theorem periodic_graph_cross_zero (p : b.PeriodicGraph g) : inner ℝ p.val.2.1 p.val.2.2 = 0 := by
  have hc : IsClosed {p : b.PeriodicGraph g | inner ℝ p.val.2.1 p.val.2.2 = 0} :=
    isClosed_eq ((continuous_subtype_val.snd.fst).inner (continuous_subtype_val.snd.snd)) continuous_const
  apply hc.closure_subset_iff.mpr (fun p hp => b.regularTimeCore_cross_zero p hp)
  rw [(b.regularTimeCore_dense g).closure_eq]
  trivial

/-- T-uniform derivative/operator/shift graph estimate for every weak solution. -/
theorem periodic_graph_sq (p : b.PeriodicGraph g) :
    ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 + r^2 * ‖g.pathL2 p.val.1‖^2 ≤
      ‖b.evolution g s (g.constantMultiplier r) p‖^2 := by
  have hc : IsClosed {p : b.PeriodicGraph g |
      ‖p.val.2.1‖^2 + ‖p.val.2.2‖^2 + r^2 * ‖g.pathL2 p.val.1‖^2 ≤
        ‖b.evolution g s (g.constantMultiplier r) p‖^2} := by
    apply isClosed_le <;> fun_prop
  apply hc.closure_subset_iff.mpr (fun p hp => b.regularTimeCore_graph_sq s r hr p hp)
  rw [(b.regularTimeCore_dense g).closure_eq]
  trivial

/-- The constructed solution uses exactly the original weak-trajectory interface. -/
theorem exists_constant_weak_periodic (f : Lp H 2 g.timeMeasure) :
    ∃ u : PeriodicWeakTrajectory g b.domain b.operator, ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.derivative t + b.operator (u.domainValue t) + r • u.value t = f t := by
  obtain ⟨p, hp⟩ := b.evolution_constant_surjective g s r hr f
  exact ⟨p.toTrajectory, (b.evolution_eq_iff g s (g.constantMultiplier r) p f).mp hp⟩

end Carleman.CoerciveForm
