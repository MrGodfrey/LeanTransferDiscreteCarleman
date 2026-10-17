module

public import Carleman.Continuous.FrequencySolve

/-! Exact frequency energy and graph estimates, independent of period and
frequency. The frequency solutions are unique on the full associated domain. -/
@[expose] public noncomputable section
namespace Carleman.CoerciveForm
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] (b : CoerciveForm H V)

/-- Skew time coupling cancels by symmetry of the original operator. -/
theorem frequency_energy_identity (r ω : ℝ) (x y : b.domain) :
    ‖b.operator x + r • (x : H) + ω • (y : H)‖^2 +
      ‖b.operator y + r • (y : H) - ω • (x : H)‖^2 =
    ‖b.operator x + r • (x : H)‖^2 + ‖b.operator y + r • (y : H)‖^2 +
      ω^2 * (‖(x : H)‖^2 + ‖(y : H)‖^2) := by
  have hs : inner ℝ (b.operator x) (y : H) = inner ℝ (b.operator y) (x : H) :=
    (b.operator_symmetric x y).trans (real_inner_comm _ _)
  simp only [norm_add_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, inner_add_left, real_inner_smul_left, real_inner_smul_right]
  rw [hs, real_inner_comm (x : H) (y : H)]
  ring

/-- All three graph terms have coefficient one, uniform in r≥0 and ω∈ℝ. -/
theorem frequency_graph_sq (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (x y : b.domain) :
    ‖b.operator x‖^2 + ‖b.operator y‖^2 +
      (r^2 + ω^2) * (‖(x : H)‖^2 + ‖(y : H)‖^2) ≤
    ‖b.operator x + r • (x : H) + ω • (y : H)‖^2 +
      ‖b.operator y + r • (y : H) - ω • (x : H)‖^2 := by
  rw [b.frequency_energy_identity]
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right]
  have hx := mul_nonneg hr (b.operator_nonneg x)
  have hy := mul_nonneg hr (b.operator_nonneg y)
  nlinarith

theorem frequency_kernel (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (x y : b.domain)
    (hx : b.operator x + r • (x : H) + ω • (y : H) = 0)
    (hy : b.operator y + r • (y : H) - ω • (x : H) = 0) : x = 0 ∧ y = 0 := by
  obtain ⟨c, hc, hb⟩ := b.coercive
  have he₀ := congrArg (fun z => inner ℝ z (x : H)) hx
  have he₁ := congrArg (fun z => inner ℝ z (y : H)) hy
  have hax : inner ℝ (b.operator x) (x : H) = b.form (b.energy x) (b.energy x) := by
    rw [← b.embed_energy x, b.operator_test]
  have hay : inner ℝ (b.operator y) (y : H) = b.form (b.energy y) (b.energy y) := by
    rw [← b.embed_energy y, b.operator_test]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_zero_left,
    real_inner_self_eq_norm_sq, hax, hay] at he₀ he₁
  rw [real_inner_comm (x : H) (y : H)] at he₀
  have hnonx := mul_nonneg hr (sq_nonneg ‖(x : H)‖)
  have hnony := mul_nonneg hr (sq_nonneg ‖(y : H)‖)
  have hz (z : b.domain) (hf : b.form (b.energy z) (b.energy z) ≤ 0) : b.energy z = 0 := by
    have hn : c * ‖b.energy z‖^2 ≤ 0 := by nlinarith [hb (b.energy z)]
    have hn' : ‖b.energy z‖^2 ≤ 0 := nonpos_of_mul_nonpos_right hn hc
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (b.energy z)])
  have hnex : b.energy x = 0 := hz x (by linarith [b.form_nonneg (b.energy y)])
  have hney : b.energy y = 0 := hz y (by linarith [b.form_nonneg (b.energy x)])
  constructor
  · apply Subtype.ext
    rw [← b.embed_energy x, hnex, map_zero, Submodule.coe_zero]
  · apply Subtype.ext
    rw [← b.embed_energy y, hney, map_zero, Submodule.coe_zero]

variable [CompleteSpace V]

theorem frequency_solution_graph (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (f k : H) :
    ‖b.operator (b.frequencyCos r hr ω f k)‖^2 +
      ‖b.operator (b.frequencySin r hr ω f k)‖^2 +
      (r^2 + ω^2) * (‖(b.frequencyCos r hr ω f k : H)‖^2 +
        ‖(b.frequencySin r hr ω f k : H)‖^2) ≤ ‖f‖^2 + ‖k‖^2 := by
  simpa only [b.frequencyCos_equation, b.frequencySin_equation] using
    b.frequency_graph_sq r hr ω (b.frequencyCos r hr ω f k) (b.frequencySin r hr ω f k)

theorem frequency_unique (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (f k : H) (x y : b.domain)
    (hx : b.operator x + r • (x : H) + ω • (y : H) = f)
    (hy : b.operator y + r • (y : H) - ω • (x : H) = k) :
    x = b.frequencyCos r hr ω f k ∧ y = b.frequencySin r hr ω f k := by
  let a := b.frequencyCos r hr ω f k
  let z := b.frequencySin r hr ω f k
  have ha : b.operator a + r • (a : H) + ω • (z : H) = f := b.frequencyCos_equation r hr ω f k
  have hz : b.operator z + r • (z : H) - ω • (a : H) = k := b.frequencySin_equation r hr ω f k
  have h₀ : b.operator (x-a) + r • ((x-a : b.domain) : H) +
      ω • ((y-z : b.domain) : H) = 0 := by
    calc
      _ = (b.operator x + r • (x : H) + ω • (y : H)) -
          (b.operator a + r • (a : H) + ω • (z : H)) := by
        simp only [map_sub, Submodule.coe_sub, smul_sub]
        abel
      _ = 0 := by rw [hx, ha, sub_self]
  have h₁ : b.operator (y-z) + r • ((y-z : b.domain) : H) -
      ω • ((x-a : b.domain) : H) = 0 := by
    calc
      _ = (b.operator y + r • (y : H) - ω • (x : H)) -
          (b.operator z + r • (z : H) - ω • (a : H)) := by
        simp only [map_sub, Submodule.coe_sub, smul_sub]
        abel
      _ = 0 := by rw [hy, hz, sub_self]
  exact ⟨sub_eq_zero.mp (b.frequency_kernel r hr ω (x-a) (y-z) h₀ h₁).1,
    sub_eq_zero.mp (b.frequency_kernel r hr ω (x-a) (y-z) h₀ h₁).2⟩

theorem existsUnique_frequency (r : ℝ) (hr : 0 ≤ r) (ω : ℝ) (f k : H) :
    ∃! p : b.domain × b.domain,
      b.operator p.1 + r • (p.1 : H) + ω • (p.2 : H) = f ∧
      b.operator p.2 + r • (p.2 : H) - ω • (p.1 : H) = k := by
  refine ⟨(b.frequencyCos r hr ω f k, b.frequencySin r hr ω f k),
    ⟨b.frequencyCos_equation r hr ω f k, b.frequencySin_equation r hr ω f k⟩, ?_⟩
  intro p hp
  have he := b.frequency_unique r hr ω f k p.1 p.2 hp.1 hp.2
  exact Prod.ext he.1 he.2
end Carleman.CoerciveForm
