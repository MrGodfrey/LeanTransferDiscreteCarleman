module

public import Carleman.Spatial.StrongL2Limit

/-! Convergence of the actual L² energies, together with almost-everywhere
convergence, implies strong L² convergence. No common majorant is needed. -/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Carleman
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem l2_square_tendsto_zero_of_ae_of_energy_tendsto {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (henergy : Tendsto (fun n => ∫ x, (F n x)^2 ∂ν) atTop (𝓝 (∫ x, (f x)^2 ∂ν))) :
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
  · intro b hb
    by_contra hbad
    have hfreq : ∃ᶠ n in atTop, b ≤ ∫ x, (F n x-f x)^2 ∂ν := by
      simpa only [not_lt] using not_eventually.mp hbad
    obtain ⟨φ,hφ,hbadφ⟩ := exists_seq_forall_of_frequently hfreq
    have hupper : ∀ᶠ n in atTop, (∫ x, (F (φ n) x)^2 ∂ν) < E+b/4 :=
      (henergy.comp hφ).eventually (gt_mem_nhds (by dsimp only [E]; linarith))
    have hplus : ∀ᶠ n in atTop, (∫ x, (F (φ n) x+f x)^2 ∂ν) ≤ 4*E-b/2 := by
      filter_upwards [hupper] with n hn
      have h := hid (φ n)
      have hh := hbadφ n
      linarith
    have hC : 0 ≤ 4*E-b/2 := by
      obtain ⟨n,hn⟩ := hplus.exists
      exact (integral_nonneg fun x => sq_nonneg _).trans hn
    have hsumlim : ∀ᵐ x ∂ν, Tendsto (fun n => F (φ n) x+f x) atTop (𝓝 (f x+f x)) := by
      filter_upwards [hlim] with x hx
      exact (hx.comp hφ).add_const (f x)
    have he := l2_square_bound_of_ae_tendsto (hf.add hf)
      (fun n => (hF (φ n)).add hf) hsumlim hC hplus
    have htwo : (∫ x, (f x+f x)^2 ∂ν)=4*E := by
      have hpoint : (fun x => (f x+f x)^2)=(fun x => 4*(f x)^2) := by funext x; ring
      rw [hpoint,integral_const_mul]
    simp only [Pi.add_apply] at he
    rw [htwo] at he
    linarith

theorem l2_error_tendsto_of_ae_of_energy_tendsto {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (henergy : Tendsto (fun n => ∫ x, (F n x)^2 ∂ν) atTop (𝓝 (∫ x, (f x)^2 ∂ν))) :
    Tendsto (fun n => bochnerL2Norm ν (fun x => F n x-f x)) atTop (𝓝 0) := by
  have he (n : ℕ) := integral_sq_eq_bochnerL2Norm_sq ((hF n).sub hf)
  simp only [Pi.sub_apply] at he
  have ht := (l2_square_tendsto_zero_of_ae_of_energy_tendsto hf hF hlim henergy).sqrt
  change Tendsto (fun n => bochnerL2Norm ν (F n-f)) atTop (𝓝 0)
  simpa only [he,Real.sqrt_sq (bochnerL2Norm_nonneg _),Real.sqrt_zero] using ht

end Carleman
