module

public import Carleman.Spatial.PairwiseL2Limit

/-! Almost-everywhere convergence and an upper bound by the limiting L²
energy imply strong L² convergence. The proof applies Fatou to the sum and
uses the exact parallelogram identity; no dominating function is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem l2_square_tendsto_zero_of_ae_of_energy_le {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hb : ∀ n, (∫ x, (F n x)^2 ∂ν) ≤ ∫ x, (f x)^2 ∂ν) :
    Tendsto (fun n => ∫ x, (F n x-f x)^2 ∂ν) atTop (𝓝 0) := by
  let E := ∫ x, (f x)^2 ∂ν
  have hid (n : ℕ) : (∫ x, (F n x+f x)^2 ∂ν)+(∫ x, (F n x-f x)^2 ∂ν) =
      2*(∫ x, (F n x)^2 ∂ν)+2*E := by
    have hsum := integral_add ((hF n).add hf).integrable_sq ((hF n).sub hf).integrable_sq
    simp only [Pi.add_apply,Pi.sub_apply] at hsum
    rw [← hsum]
    have he : (fun x => (F n x+f x)^2+(F n x-f x)^2) =
        (fun x => 2*(F n x)^2+2*(f x)^2) := by funext x; ring
    rw [he,integral_add ((hF n).integrable_sq.const_mul 2) (hf.integrable_sq.const_mul 2),
      integral_const_mul,integral_const_mul]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n => ha.trans_le (integral_nonneg fun x => sq_nonneg _)
  · intro b hb0
    by_contra hbad
    have hfreq : ∃ᶠ n in atTop, b ≤ ∫ x, (F n x-f x)^2 ∂ν := by
      simpa only [not_lt] using (not_eventually.mp hbad)
    obtain ⟨φ,hφ,hbadφ⟩ := exists_seq_forall_of_frequently hfreq
    have hplus (n : ℕ) : (∫ x, (F (φ n) x+f x)^2 ∂ν) ≤ 4*E-b := by
      have h := hid (φ n)
      have h₁ := hb (φ n)
      have h₂ := hbadφ n
      linarith
    have hC : 0 ≤ 4*E-b := (integral_nonneg fun x => sq_nonneg _).trans (hplus 0)
    have hsumlim : ∀ᵐ x ∂ν, Tendsto (fun n => F (φ n) x+f x) atTop (𝓝 (f x+f x)) := by
      filter_upwards [hlim] with x hx
      exact (hx.comp hφ).add_const (f x)
    have he := l2_square_bound_of_ae_tendsto (hf.add hf)
      (fun n => (hF (φ n)).add hf) hsumlim hC (Filter.Eventually.of_forall hplus)
    have htwo : (∫ x, (f x+f x)^2 ∂ν)=4*E := by
      have hpoint : (fun x => (f x+f x)^2) = (fun x => 4*(f x)^2) := by funext x; ring
      rw [hpoint,integral_const_mul]
    simp only [Pi.add_apply] at he
    rw [htwo] at he
    linarith

end Carleman
