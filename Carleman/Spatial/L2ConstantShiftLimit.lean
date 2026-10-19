module

public import Carleman.Spatial.StrongL2NormLimit

/-! Strong L² convergence is preserved when subtracting convergent constants
on a finite-measure set, with the actual constant-function L² norm. -/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Carleman

theorem l2_error_sub_constant_tendsto {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsFiniteMeasure ν] {f : Ω → ℝ} {F : ℕ → Ω → ℝ} {c : ℕ → ℝ} {b : ℝ}
    (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (ht : Tendsto (fun n => bochnerL2Norm ν (fun x => F n x-f x)) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 b)) :
    Tendsto (fun n => bochnerL2Norm ν (fun x => (F n x-c n)-(f x-b))) atTop (𝓝 0) := by
  have h1 : MemLp (fun _ : Ω => (1:ℝ)) 2 ν := memLp_const 1
  have hb (n : ℕ) : bochnerL2Norm ν (fun x => (F n x-c n)-(f x-b)) ≤
      bochnerL2Norm ν (fun x => F n x-f x)+|c n-b| *bochnerL2Norm ν (fun _ : Ω => (1:ℝ)) := by
    have he : (fun x => (F n x-c n)-(f x-b))=
        (F n-f)-(c n-b) • (fun _ : Ω => (1:ℝ)) := by
      funext x
      simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [he]
    have hh := bochnerL2Norm_sub ((hF n).sub hf) (h1.const_smul (c n-b))
    rw [bochnerL2Norm_const_smul] at hh
    exact hh
  apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) hb
  simpa only [sub_self,abs_zero,zero_mul,add_zero] using
    ht.add ((hc.sub_const b).abs.mul_const (bochnerL2Norm ν (fun _ : Ω => (1:ℝ))))

end Carleman
