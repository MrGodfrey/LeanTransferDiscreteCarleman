module

public import Carleman.Continuous.FiniteHarmonic
public import Carleman.Continuous.WeakTimeEnergy
public import Carleman.Continuous.TimeTraceBound

/-! A classical dense approximation core in the actual associated operator
graph. Timewise domain regularity belongs only to this approximation core. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V)

def graphH : b.operatorGraph →L[ℝ] H :=
  (ContinuousLinearMap.fst ℝ H H).comp b.operatorGraph.subtypeL

def graphA : b.operatorGraph →L[ℝ] H :=
  (ContinuousLinearMap.snd ℝ H H).comp b.operatorGraph.subtypeL

def graphDomain (z : b.operatorGraph) : b.domain :=
  ⟨z.val.1, by
    obtain ⟨v, hv, _⟩ := (b.operatorGraph_mem _ _).mp z.property
    exact hv ▸ v.property⟩

omit [CompleteSpace H] [CompleteSpace V] in
theorem graphDomain_operator (z : b.operatorGraph) : b.operator (b.graphDomain z) = b.graphA z := by
  obtain ⟨v, hv, ha⟩ := (b.operatorGraph_mem _ _).mp z.property
  have he : b.graphDomain z = v := Subtype.ext hv.symm
  rw [he]
  exact ha

omit [CompleteSpace H] [CompleteSpace V] in
theorem graphH_injective : Function.Injective b.graphH := by
  intro x y hxy
  have hd : b.graphDomain x = b.graphDomain y := Subtype.ext hxy
  apply Subtype.ext
  apply Prod.ext hxy
  change b.graphA x = b.graphA y
  rw [← b.graphDomain_operator, ← b.graphDomain_operator, hd]

omit [CompleteSpace H] [CompleteSpace V] in
theorem graph_symmetric (x y : b.operatorGraph) :
    inner ℝ (b.graphA x) (b.graphH y) = inner ℝ (b.graphH x) (b.graphA y) := by
  have he := b.operator_symmetric (b.graphDomain x) (b.graphDomain y)
  rw [b.graphDomain_operator, b.graphDomain_operator] at he
  exact he

def graphOfDomain (x : b.domain) : b.operatorGraph :=
  ⟨((x : H), b.operator x), (b.operatorGraph_mem _ _).mpr ⟨x, rfl, rfl⟩⟩

def IsRegularTimeCore (g : TimeGrid) (p : b.PeriodicGraph g) : Prop :=
  ∃ U dU : ℝ → b.operatorGraph, Continuous U ∧ Continuous dU ∧
    (∀ t, HasDerivAt U (dU t) t) ∧
    ∀ t : Icc 0 g.period, p.val.1 t = b.graphH (U t)

def regularTimeCore (g : TimeGrid) : Submodule ℝ (b.PeriodicGraph g) where
  carrier := b.IsRegularTimeCore g
  zero_mem' := ⟨fun _ => 0, fun _ => 0, continuous_const, continuous_const,
    fun t => hasDerivAt_const t 0, fun _ => by simp⟩
  add_mem' := by
    rintro p q ⟨U, dU, hU, hdU, hderU, hp⟩ ⟨W, dW, hW, hdW, hderW, hq⟩
    refine ⟨fun t => U t + W t, fun t => dU t + dW t, hU.add hW, hdU.add hdW,
      fun t => (hderU t).fun_add (hderW t), ?_⟩
    intro t
    change p.val.1 t + q.val.1 t = _
    rw [hp, hq, map_add]
  smul_mem' := by
    rintro c p ⟨U, dU, hU, hdU, hder, hp⟩
    refine ⟨fun t => c • U t, fun t => c • dU t, hU.const_smul c, hdU.const_smul c,
      fun t => (hder t).const_smul c, ?_⟩
    intro t
    change c • p.val.1 t = _
    rw [hp, map_smul]

theorem frequencyGraph_mem_core (g : TimeGrid) (s : Orientation) (r : ℝ) (hr : 0 ≤ r)
    (n : ℤ) (f k : H) : b.frequencyGraph g s r hr n f k ∈ b.regularTimeCore g := by
  let x := b.graphOfDomain (b.frequencyCos r hr (s.sign*g.angularFrequency n) f k)
  let y := b.graphOfDomain (b.frequencySin r hr (s.sign*g.angularFrequency n) f k)
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
    change harmonicValue ω _ _ t = _
    simp only [map_add, map_smul]
    rfl

/-- The genuine L² derivative and operator coincide with the smooth core fields a.e. -/
theorem regularTimeCore_fields {g : TimeGrid} (p : b.PeriodicGraph g)
    (U dU : ℝ → b.operatorGraph) (hU : Continuous U) (hdU : Continuous dU)
    (hder : ∀ t, HasDerivAt U (dU t) t)
    (hp : ∀ t : Icc 0 g.period, p.val.1 t = b.graphH (U t)) :
    (g.pathL2 p.val.1 =ᵐ[g.timeMeasure] fun t => b.graphH (U t)) ∧
    (p.val.2.1 =ᵐ[g.timeMeasure] fun t => b.graphH (dU t)) ∧
    (p.val.2.2 =ᵐ[g.timeMeasure] fun t => b.graphA (U t)) := by
  have hu : g.pathL2 p.val.1 =ᵐ[g.timeMeasure] (fun t => b.graphH (U t)) := by
    filter_upwards [g.pathL2_ae p.val.1, ae_restrict_mem measurableSet_Ioo] with t ht hm
    rw [ht, g.clampPath_on _ _ ⟨hm.1.le, hm.2.le⟩]
    exact hp ⟨t, ⟨hm.1.le, hm.2.le⟩⟩
  have hdLp := g.memLp_of_continuousOn (b.graphH.continuous.comp hdU).continuousOn
  have hw : HasWeakTimeDerivative g (fun t => b.graphH (U t)) (fun t => b.graphH (dU t)) :=
    HasWeakTimeDerivative.of_hasDerivAt (b.graphH.continuous.comp hU).continuousOn
      (fun t _ => b.graphH.hasFDerivAt.comp_hasDerivAt t (hder t))
      (b.graphH.continuous.comp hdU).continuousOn.intervalIntegrable
  have hclass : IsWeakTimeClass g (g.pathL2 p.val.1) (hdLp.toLp (fun t => b.graphH (dU t))) :=
    IsWeakTimeClass.iff_weakDerivative.mpr ((hw.congr hu.symm).congr_derivative hdLp.coeFn_toLp.symm)
  have he := ((b.periodicGraph_mem g p.val).mp p.property).1.unique hclass
  refine ⟨hu, ?_, ?_⟩
  · rw [he]
    exact hdLp.coeFn_toLp
  · have hgraph := (b.timeOperatorGraph_ae g.timeMeasure _ _).mp
      ((b.periodicGraph_mem g p.val).mp p.property).2.1
    filter_upwards [hu, hgraph] with t ht hgt
    obtain ⟨v, hv, ha⟩ := (b.operatorGraph_mem _ _).mp hgt
    have hvd : v = b.graphDomain (U t) := Subtype.ext (hv.trans ht)
    rw [← ha, hvd, b.graphDomain_operator]

end Carleman.CoerciveForm
