module

public import Carleman.Continuous.FormOperator
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Real sine/cosine frequency equations for the original associated operator.
A skew time-frequency coupling is solved by the original coercive form, on
the full infinite-dimensional energy space. No spectral decomposition or
assumed continuous solution is used. -/
@[expose] public noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] (b : CoerciveForm H V)

abbrev FrequencySpace := PiLp 2 (fun _ : Fin 2 => V)

def frequencyProjection (i : Fin 2) : FrequencySpace (V := V) →L[ℝ] H :=
  b.embed.comp (PiLp.proj 2 (fun _ : Fin 2 => V) i)

def frequencyForm (r ω : ℝ) : FrequencySpace (V := V) →L[ℝ] FrequencySpace (V := V) →L[ℝ] ℝ :=
  (b.shiftedForm r).bilinearComp (PiLp.proj 2 (fun _ : Fin 2 => V) 0)
    (PiLp.proj 2 (fun _ : Fin 2 => V) 0) +
  (b.shiftedForm r).bilinearComp (PiLp.proj 2 (fun _ : Fin 2 => V) 1)
    (PiLp.proj 2 (fun _ : Fin 2 => V) 1) +
  ω • (((innerSL ℝ).bilinearComp (b.frequencyProjection 1) (b.frequencyProjection 0) :
    FrequencySpace (V := V) →L[ℝ] FrequencySpace (V := V) →L[ℝ] ℝ) -
    ((innerSL ℝ).bilinearComp (b.frequencyProjection 0) (b.frequencyProjection 1) :
      FrequencySpace (V := V) →L[ℝ] FrequencySpace (V := V) →L[ℝ] ℝ))

theorem frequencyForm_apply (r ω : ℝ) (u v : FrequencySpace (V := V)) :
    b.frequencyForm r ω u v =
      b.shiftedForm r (u.ofLp 0) (v.ofLp 0) + b.shiftedForm r (u.ofLp 1) (v.ofLp 1) +
      ω * (inner ℝ (b.embed (u.ofLp 1)) (b.embed (v.ofLp 0)) -
        inner ℝ (b.embed (u.ofLp 0)) (b.embed (v.ofLp 1))) := rfl

theorem frequencyForm_coercive {r : ℝ} (hr : 0 ≤ r) (ω : ℝ) :
    IsCoercive (b.frequencyForm r ω) := by
  obtain ⟨c, hc, hb⟩ := b.shiftedForm_coercive hr
  refine ⟨c, hc, fun u => ?_⟩
  rw [b.frequencyForm_apply, real_inner_comm (b.embed (u.ofLp 0)) (b.embed (u.ofLp 1))]
  have hn : ‖u‖ ^ 2 = ‖u.ofLp 0‖ ^ 2 + ‖u.ofLp 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  nlinarith [hb (u.ofLp 0), hb (u.ofLp 1)]

def frequencyLoad (f k : H) : FrequencySpace (V := V) →L[ℝ] ℝ :=
  (b.loadFunctional f).comp (PiLp.proj 2 (fun _ : Fin 2 => V) 0) +
  (b.loadFunctional k).comp (PiLp.proj 2 (fun _ : Fin 2 => V) 1)

theorem frequencyLoad_apply (f k : H) (v : FrequencySpace (V := V)) :
    b.frequencyLoad f k v = inner ℝ f (b.embed (v.ofLp 0)) +
      inner ℝ k (b.embed (v.ofLp 1)) := rfl

variable [CompleteSpace V]

def frequencyEnergy (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (f k : H) : FrequencySpace (V := V) :=
  variationalSolve (b.frequencyForm r ω) (b.frequencyForm_coercive hr ω) (b.frequencyLoad f k)

theorem frequencyEnergy_test_zero (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (f k : H) (w : V) :
    b.form ((b.frequencyEnergy r hr ω f k).ofLp 0) w =
      inner ℝ (f - r • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 0) -
        ω • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 1)) (b.embed w) := by
  have he := variationalSolve_spec (b.frequencyForm r ω) (b.frequencyForm_coercive hr ω)
    (b.frequencyLoad f k) (PiLp.single 2 0 w : FrequencySpace (V := V))
  change b.frequencyForm r ω (b.frequencyEnergy r hr ω f k) _ = _ at he
  rw [b.frequencyForm_apply, b.frequencyLoad_apply] at he
  simp only [PiLp.single_apply, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
    map_zero, inner_zero_right, add_zero, sub_zero, b.shiftedForm_apply] at he
  rw [inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  linarith

theorem frequencyEnergy_test_one (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (f k : H) (w : V) :
    b.form ((b.frequencyEnergy r hr ω f k).ofLp 1) w =
      inner ℝ (k - r • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 1) +
        ω • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 0)) (b.embed w) := by
  have he := variationalSolve_spec (b.frequencyForm r ω) (b.frequencyForm_coercive hr ω)
    (b.frequencyLoad f k) (PiLp.single 2 1 w : FrequencySpace (V := V))
  change b.frequencyForm r ω (b.frequencyEnergy r hr ω f k) _ = _ at he
  rw [b.frequencyForm_apply, b.frequencyLoad_apply] at he
  simp only [PiLp.single_apply, ite_true, show (0 : Fin 2) ≠ 1 by decide, ite_false,
    map_zero, inner_zero_right, zero_add, zero_sub, b.shiftedForm_apply] at he
  rw [inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  linarith

def frequencyCos (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (f k : H) : b.domain :=
  b.domainElement ((b.frequencyEnergy r hr ω f k).ofLp 0)
    (f - r • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 0) -
      ω • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 1))
    (b.frequencyEnergy_test_zero r hr ω f k)

def frequencySin (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (f k : H) : b.domain :=
  b.domainElement ((b.frequencyEnergy r hr ω f k).ofLp 1)
    (k - r • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 1) +
      ω • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 0))
    (b.frequencyEnergy_test_one r hr ω f k)

theorem frequencyCos_equation (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (f k : H) :
    b.operator (b.frequencyCos r hr ω f k) + r • (b.frequencyCos r hr ω f k : H) +
      ω • (b.frequencySin r hr ω f k : H) = f := by
  rw [frequencyCos, b.operator_domainElement]
  change (f - r • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 0) -
    ω • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 1)) +
    r • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 0) +
    ω • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 1) = f
  abel

theorem frequencySin_equation (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (f k : H) :
    b.operator (b.frequencySin r hr ω f k) + r • (b.frequencySin r hr ω f k : H) -
      ω • (b.frequencyCos r hr ω f k : H) = k := by
  rw [frequencySin, b.operator_domainElement]
  change (k - r • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 1) +
    ω • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 0)) +
    r • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 1) -
    ω • b.embed ((b.frequencyEnergy r hr ω f k).ofLp 0) = k
  abel
end Carleman.CoerciveForm
