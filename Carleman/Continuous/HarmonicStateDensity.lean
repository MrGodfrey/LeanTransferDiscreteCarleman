module

public import Carleman.Continuous.HarmonicGraphContinuity
public import Carleman.Continuous.PeriodicSolutionOperator

/-! Finite harmonics are dense in the full periodic operator graph, not just in value L². -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid)

theorem harmonicGraph_mem_core (n : ℤ) (x y : b.operatorGraph) :
    b.harmonicGraph g n x y ∈ b.regularTimeCore g := by
  let ω := g.angularFrequency n
  refine ⟨fun t => Real.cos (ω*t) • x + Real.sin (ω*t) • y,
    fun t => (-ω*Real.sin (ω*t)) • x + (ω*Real.cos (ω*t)) • y,
    by fun_prop, by fun_prop, ?_, ?_⟩
  · intro t
    have hc : HasDerivAt (fun z => Real.cos (ω*z)) (-ω*Real.sin (ω*t)) t := by
      simpa [mul_comm] using ((hasDerivAt_id t).const_mul ω).cos
    have hs : HasDerivAt (fun z => Real.sin (ω*z)) (ω*Real.cos (ω*t)) t := by
      simpa [mul_comm] using ((hasDerivAt_id t).const_mul ω).sin
    exact (hc.smul_const x).fun_add (hs.smul_const y)
  · intro t
    rw [b.harmonicGraph_trace]
    simp only [map_add, map_smul, harmonicValue]
    rfl

def harmonicStateSpan : Submodule ℝ (b.PeriodicGraph g) :=
  Submodule.span ℝ {p | ∃ n x y, p = b.harmonicGraph g n x y}

theorem harmonicStateSpan_le_core : b.harmonicStateSpan g ≤ b.regularTimeCore g := by
  apply Submodule.span_le.mpr
  rintro p ⟨n,x,y,rfl⟩
  exact b.harmonicGraph_mem_core g n x y

theorem frequencyGraph_mem_harmonicStateSpan (s : Orientation) (r : ℝ) (hr : 0 ≤ r)
    (n : ℤ) (f k : H) : b.frequencyGraph g s r hr n f k ∈ b.harmonicStateSpan g := by
  apply Submodule.subset_span
  refine ⟨n, b.graphOfDomain (b.frequencyCos r hr (s.sign*g.angularFrequency n) f k),
    b.graphOfDomain (b.frequencySin r hr (s.sign*g.angularFrequency n) f k), ?_⟩
  apply PeriodicGraph.trace_injective
  apply ContinuousMap.ext
  intro t
  rfl

theorem constantSolve_harmonic_mem (s : Orientation) (r : ℝ) (hr : 0 ≤ r)
    (f : Lp H 2 g.timeMeasure) (hf : f ∈ g.harmonicSpan (H := H)) :
    b.constantSolve g s r hr f ∈ b.harmonicStateSpan g := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n,a,k,rfl⟩ := hf
    have he : b.constantSolve g s r hr (g.harmonicLp n a k)=b.frequencyGraph g s r hr n a k := by
      apply b.evolution_injective g s (g.constantMultiplier r) (Filter.Eventually.of_forall fun _ => hr)
      rw [b.constantSolve_equation,b.frequencyGraph_equation]
    rw [he]
    exact b.frequencyGraph_mem_harmonicStateSpan g s r hr n a k
  | zero => simpa only [map_zero] using (b.harmonicStateSpan g).zero_mem
  | add f k _ _ hf hk =>
    simpa only [map_add] using (b.harmonicStateSpan g).add_mem hf hk
  | smul c f _ hf =>
    simpa only [map_smul] using (b.harmonicStateSpan g).smul_mem c hf

/-- The norm includes the continuous H trace, time derivative and actual operator in L². -/
theorem harmonicStateSpan_dense : Dense (b.harmonicStateSpan g : Set (b.PeriodicGraph g)) := by
  let L := b.constantSolve g Orientation.plus 0 le_rfl
  have hsurj : Function.Surjective L := (b.constantEvolutionEquiv g Orientation.plus 0 le_rfl).symm.surjective
  have hi : Dense (L '' (g.harmonicSpan (H := H) : Set (Lp H 2 g.timeMeasure))) :=
    by
      convert! hsurj.denseRange.dense_image (s := (g.harmonicSpan (H := H) : Set (Lp H 2 g.timeMeasure)))
        L.continuous (g.harmonicSpan_dense (H := H)) using 1
  apply hi.mono
  rintro p ⟨f,hf,rfl⟩
  exact b.constantSolve_harmonic_mem g Orientation.plus 0 le_rfl f hf

/-- Density transfers through the actual continuous harmonic coefficient map. -/
theorem dense_of_harmonic_approximation (S : Submodule ℝ (b.PeriodicGraph g))
    (h : ∀ n x y, ∃ X Y : ℕ → b.operatorGraph,
      Filter.Tendsto X Filter.atTop (nhds x) ∧ Filter.Tendsto Y Filter.atTop (nhds y) ∧
      ∀ k, b.harmonicGraph g n (X k) (Y k) ∈ S) : Dense (S : Set (b.PeriodicGraph g)) := by
  have hc : b.harmonicStateSpan g ≤ S.topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro p ⟨n,x,y,rfl⟩
    obtain ⟨X,Y,hX,hY,hXY⟩ := h n x y
    have ht := ((b.harmonicGraphCLM g n).continuous.tendsto (x,y)).comp (hX.prodMk_nhds hY)
    change Filter.Tendsto (fun k => b.harmonicGraph g n (X k) (Y k)) Filter.atTop
      (nhds (b.harmonicGraph g n x y)) at ht
    exact mem_closure_of_tendsto ht (Filter.Eventually.of_forall hXY)
  have hh : Dense (S.topologicalClosure : Set (b.PeriodicGraph g)) := (b.harmonicStateSpan_dense g).mono hc
  exact hh.of_closure

end Carleman.CoerciveForm
