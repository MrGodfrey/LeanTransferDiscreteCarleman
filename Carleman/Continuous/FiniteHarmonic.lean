module

public import Carleman.Continuous.HarmonicTrajectory
public import Carleman.Continuous.PeriodicEvolution
public import Carleman.Continuous.FormAssociated

/-! Solve every finite H-valued time Fourier polynomial in the complete
periodic graph space, with both orientations and the original associated A.
Extension from this class to arbitrary L² loads remains a separate theorem. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
namespace TimeGrid
variable (g : TimeGrid) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def constantMultiplier (r : ℝ) : BoundedMultiplier g.timeMeasure where
  value := fun _ => r
  measurable := aestronglyMeasurable_const
  bound := |r|
  bound_nonneg := abs_nonneg _
  bounded := Filter.Eventually.of_forall fun _ => le_rfl

def harmonicLp (n : ℤ) (f k : H) : Lp H 2 g.timeMeasure :=
  (g.memLp_of_continuousOn (harmonic_continuous (g.angularFrequency n) f k).continuousOn).toLp
    (harmonicValue (g.angularFrequency n) f k)

theorem harmonicLp_ae (n : ℤ) (f k : H) : g.harmonicLp n f k =ᵐ[g.timeMeasure]
    harmonicValue (g.angularFrequency n) f k :=
  (g.memLp_of_continuousOn (harmonic_continuous (g.angularFrequency n) f k).continuousOn).coeFn_toLp
end TimeGrid
namespace CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (b : CoerciveForm H V) (g : TimeGrid) (s : Orientation) (r : ℝ) (hr : 0 ≤ r)

def frequencyGraph (n : ℤ) (f k : H) : b.PeriodicGraph g :=
  (b.frequencyTrajectory g s r hr n f k).toPeriodicGraph

theorem frequencyGraph_equation (n : ℤ) (f k : H) :
    b.evolution g s (g.constantMultiplier r) (b.frequencyGraph g s r hr n f k) =
      g.harmonicLp n f k := by
  apply (b.evolution_eq_iff g s (g.constantMultiplier r) _ _).mpr
  let u := b.frequencyTrajectory g s r hr n f k
  filter_upwards [u.toPeriodicGraph_derivative_ae, u.toPeriodicGraph_operator_ae,
    g.harmonicLp_ae n f k, ae_restrict_mem measurableSet_Ioo] with t hd ha hf ht
  change s.sign • u.toPeriodicGraph.toTrajectory.derivative t +
    b.operator (u.toPeriodicGraph.toTrajectory.domainValue t) +
    r • u.toPeriodicGraph.toTrajectory.value t = _
  rw [hd, ha, u.toPeriodicGraph_value_on t ⟨ht.1.le, ht.2.le⟩, hf]
  exact b.frequencyTrajectory_equation g s r hr n f k t

def finiteFrequencyGraph (I : Finset ℤ) (f k : ℤ → H) : b.PeriodicGraph g :=
  ∑ n ∈ I, b.frequencyGraph g s r hr n (f n) (k n)

theorem finiteFrequencyGraph_equation (I : Finset ℤ) (f k : ℤ → H) :
    b.evolution g s (g.constantMultiplier r) (b.finiteFrequencyGraph g s r hr I f k) =
      ∑ n ∈ I, g.harmonicLp n (f n) (k n) := by
  simp only [finiteFrequencyGraph, map_sum, b.frequencyGraph_equation]

include hr in
/-- Actual weak solutions for all finite time Fourier loads. The finite
frequency restriction is stated explicitly and is not the full B1 result. -/
theorem exists_finite_harmonic (I : Finset ℤ) (f k : ℤ → H) :
    ∃ u : PeriodicWeakTrajectory g b.domain b.operator, ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.derivative t + b.operator (u.domainValue t) + r • u.value t =
        ∑ n ∈ I, harmonicValue (g.angularFrequency n) (f n) (k n) t := by
  let p := b.finiteFrequencyGraph g s r hr I f k
  refine ⟨p.toTrajectory, ?_⟩
  have he := (b.evolution_eq_iff g s (g.constantMultiplier r) p _).mp
    (b.finiteFrequencyGraph_equation g s r hr I f k)
  have hs := Lp.coeFn_fun_finsetSum (μ := g.timeMeasure) I (fun n => g.harmonicLp n (f n) (k n))
  filter_upwards [he, hs, ae_all_iff.mpr (fun n => g.harmonicLp_ae n (f n) (k n))]
    with t ht hsum hcoeff
  change s.sign • p.toTrajectory.derivative t + b.operator (p.toTrajectory.domainValue t) +
    r • p.toTrajectory.value t = _ at ht ⊢
  rw [ht, hsum]
  exact Finset.sum_congr rfl fun n _ => hcoeff n

include hr in
/-- Transfer to the original D/A by its full A1 variational characterization. -/
theorem IsAssociated.exists_finite_harmonic {D : Submodule ℝ H} {A : D →ₗ[ℝ] H}
    (h : b.IsAssociated A) (I : Finset ℤ) (f k : ℤ → H) :
    ∃ u : PeriodicWeakTrajectory g D A, ∀ᵐ t ∂g.timeMeasure,
      s.sign • u.derivative t + A (u.domainValue t) + r • u.value t =
        ∑ n ∈ I, harmonicValue (g.angularFrequency n) (f n) (k n) t := by
  have hd := h.domain_eq b
  subst D
  have ha := h.operator_eq b
  subst A
  exact b.exists_finite_harmonic g s r hr I f k
end CoerciveForm
end Carleman
