module

public import Carleman.Continuous.FrequencyEnergy
public import Carleman.Continuous.PeriodicGraphEquivalence
public import Carleman.Continuous.ClassicalWeakTime
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Construct actual H-valued periodic weak trajectories for every harmonic
load, in both time directions, from the solved frequency equations. -/
@[expose] public noncomputable section
open Set MeasureTheory
namespace Carleman

namespace TimeGrid

def angularFrequency (g : TimeGrid) (n : ℤ) : ℝ := n * (2 * Real.pi) / g.period

theorem angularFrequency_period (g : TimeGrid) (n : ℤ) :
    g.angularFrequency n * g.period = n * (2 * Real.pi) :=
  div_mul_cancel₀ _ (ne_of_gt g.period_pos)
end TimeGrid

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def harmonicValue (ω : ℝ) (x y : H) (t : ℝ) : H :=
  Real.cos (ω*t) • x + Real.sin (ω*t) • y

def harmonicDerivative (ω : ℝ) (x y : H) (t : ℝ) : H :=
  (-ω * Real.sin (ω*t)) • x + (ω * Real.cos (ω*t)) • y

theorem harmonic_hasDerivAt (ω : ℝ) (x y : H) (t : ℝ) :
    HasDerivAt (harmonicValue ω x y) (harmonicDerivative ω x y t) t := by
  change HasDerivAt (fun z => Real.cos (ω*z) • x + Real.sin (ω*z) • y)
    ((-ω * Real.sin (ω*t)) • x + (ω * Real.cos (ω*t)) • y) t
  simpa [mul_comm] using
    ((((hasDerivAt_id t).const_mul ω).cos.smul_const x).fun_add
      (((hasDerivAt_id t).const_mul ω).sin.smul_const y))

theorem harmonic_continuous (ω : ℝ) (x y : H) : Continuous (harmonicValue ω x y) := by
  unfold harmonicValue
  fun_prop

theorem harmonicDerivative_continuous (ω : ℝ) (x y : H) :
    Continuous (harmonicDerivative ω x y) := by
  unfold harmonicDerivative
  fun_prop

theorem harmonic_periodic_trace (g : TimeGrid) (n : ℤ) (x y : H) :
    harmonicValue (g.angularFrequency n) x y 0 = harmonicValue (g.angularFrequency n) x y g.period := by
  have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    rw [show (n : ℝ) * (2 * Real.pi) = 2 * (n * Real.pi) by ring,
      Real.sin_two_mul, Real.sin_int_mul_pi]
    ring
  simp only [harmonicValue, mul_zero, Real.cos_zero, Real.sin_zero, one_smul, zero_smul,
    add_zero, g.angularFrequency_period, Real.cos_int_mul_two_pi, hs]

namespace CoerciveForm
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : CoerciveForm H V)

def harmonicDomain (ω : ℝ) (x y : b.domain) (t : ℝ) : b.domain :=
  Real.cos (ω*t) • x + Real.sin (ω*t) • y

theorem harmonicDomain_value (ω : ℝ) (x y : b.domain) (t : ℝ) :
    (b.harmonicDomain ω x y t : H) = harmonicValue ω (x : H) (y : H) t := rfl

theorem harmonicDomain_operator (ω : ℝ) (x y : b.domain) (t : ℝ) :
    b.operator (b.harmonicDomain ω x y t) = harmonicValue ω (b.operator x) (b.operator y) t := by
  simp only [harmonicDomain, harmonicValue, map_add, map_smul]

theorem harmonicDomain_representative (ω : ℝ) (x y : b.domain) (t : ℝ) :
    domainRepresentative b.domain (harmonicValue ω (x : H) (y : H)) t = b.harmonicDomain ω x y t := by
  apply Subtype.ext
  have hd : harmonicValue ω (x : H) (y : H) t ∈ b.domain := (b.harmonicDomain ω x y t).property
  simp only [domainRepresentative, dite_eq_left hd]
  rfl

variable [CompleteSpace H]

def harmonicTrajectory (g : TimeGrid) (n : ℤ) (x y : b.domain) :
    PeriodicWeakTrajectory g b.domain b.operator where
  value := harmonicValue (g.angularFrequency n) (x : H) (y : H)
  derivative := harmonicDerivative (g.angularFrequency n) (x : H) (y : H)
  continuous := (harmonic_continuous _ _ _).continuousOn
  periodic_trace := harmonic_periodic_trace g n _ _
  value_L2 := g.memLp_of_continuousOn (harmonic_continuous _ _ _).continuousOn
  derivative_L2 := g.memLp_of_continuousOn (harmonicDerivative_continuous _ _ _).continuousOn
  domain_ae := Filter.Eventually.of_forall fun t => (b.harmonicDomain _ x y t).property
  operator_L2 := by
    simp only [b.harmonicDomain_representative, b.harmonicDomain_operator]
    exact g.memLp_of_continuousOn (harmonic_continuous _ _ _).continuousOn
  weak_derivative := HasWeakTimeDerivative.of_hasDerivAt (harmonic_continuous _ _ _).continuousOn
    (fun t _ => harmonic_hasDerivAt _ _ _ t)
    (harmonicDerivative_continuous _ _ _).continuousOn.intervalIntegrable

variable [CompleteSpace V]

def frequencyTrajectory (g : TimeGrid) (s : Orientation) (r : ℝ) (hr : 0 ≤ r)
    (n : ℤ) (f k : H) : PeriodicWeakTrajectory g b.domain b.operator :=
  b.harmonicTrajectory g n (b.frequencyCos r hr (s.sign*g.angularFrequency n) f k)
    (b.frequencySin r hr (s.sign*g.angularFrequency n) f k)

/-- The constructed trajectory solves the original signed time equation.
The right side is an actual H-valued harmonic load. -/
theorem frequencyTrajectory_equation (g : TimeGrid) (s : Orientation) (r : ℝ) (hr : 0 ≤ r)
    (n : ℤ) (f k : H) (t : ℝ) :
    s.sign • (b.frequencyTrajectory g s r hr n f k).derivative t +
      b.operator ((b.frequencyTrajectory g s r hr n f k).domainValue t) +
      r • (b.frequencyTrajectory g s r hr n f k).value t =
      harmonicValue (g.angularFrequency n) f k t := by
  let ω := g.angularFrequency n
  let x := b.frequencyCos r hr (s.sign*ω) f k
  let y := b.frequencySin r hr (s.sign*ω) f k
  change s.sign • harmonicDerivative ω (x : H) (y : H) t +
    b.operator (domainRepresentative b.domain (harmonicValue ω (x : H) (y : H)) t) +
    r • harmonicValue ω (x : H) (y : H) t = harmonicValue ω f k t
  rw [b.harmonicDomain_representative, b.harmonicDomain_operator]
  have hx : b.operator x + r • (x : H) + (s.sign*ω) • (y : H) = f :=
    b.frequencyCos_equation r hr (s.sign*ω) f k
  have hy : b.operator y + r • (y : H) - (s.sign*ω) • (x : H) = k :=
    b.frequencySin_equation r hr (s.sign*ω) f k
  rw [← hx, ← hy]
  simp only [harmonicValue, harmonicDerivative, smul_add, smul_sub, smul_smul]
  module
end CoerciveForm
end Carleman
