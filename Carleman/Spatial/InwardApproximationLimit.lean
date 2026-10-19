module

public import Carleman.Spatial.StrongInwardPullback

/-! Strong L² convergence survives simultaneous inward pullback and scalar
factors tending to one. This applies to each actual derivative component. -/
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Carleman
variable {d : ℕ}

theorem inwardPullback_L2_error_tendsto_diagonal (a : SpatialCoordinates d)
    {f : SpatialCoordinates d → ℝ} {F : ℕ → SpatialCoordinates d → ℝ}
    (hf : MemLp f 2 volume) (hF : ∀ n, MemLp (F n) 2 volume)
    (ht : Tendsto (fun n => bochnerL2Norm volume (fun x => F n x-f x)) atTop (𝓝 0)) :
    Tendsto (fun n => bochnerL2Norm volume (fun x => inwardPullback a n (F n) x-f x))
      atTop (𝓝 0) := by
  have hb (n : ℕ) : bochnerL2Norm volume (fun x => inwardPullback a n (F n) x-f x) ≤
      (2:ℝ)^d*bochnerL2Norm volume (fun x => F n x-f x)+
        bochnerL2Norm volume (fun x => inwardPullback a n f x-f x) := by
    have he : (fun x => inwardPullback a n (F n) x-f x)=
        (fun x => inwardPullback a n (F n-f) x+(inwardPullback a n f x-f x)) := by
      funext x
      simp only [inwardPullback,Pi.sub_apply]
      ring
    rw [he]
    exact (bochnerL2Norm_add (inwardPullback_memLp a n ((hF n).sub hf))
      ((inwardPullback_memLp a n hf).sub hf)).trans
      (add_le_add (inwardPullback_L2_le a n ((hF n).sub hf)) le_rfl)
  apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) hb
  simpa only [mul_zero,add_zero] using
    (ht.const_mul ((2:ℝ)^d)).add (inwardPullback_L2_error_tendsto a hf)

theorem l2_scaled_error_tendsto {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {f : Ω → ℝ} {F : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (ht : Tendsto (fun n => bochnerL2Norm ν (fun x => F n x-f x)) atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun n => bochnerL2Norm ν (fun x => c n*F n x-f x)) atTop (𝓝 0) := by
  have hb (n : ℕ) : bochnerL2Norm ν (fun x => c n*F n x-f x) ≤
      |c n| *bochnerL2Norm ν (fun x => F n x-f x)+|c n-1| *bochnerL2Norm ν f := by
    have he : (fun x => c n*F n x-f x)=(c n • (F n-f)+(c n-1) • f) := by
      funext x
      simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [he]
    have hb := bochnerL2Norm_add (((hF n).sub hf).const_smul (c n)) (hf.const_smul (c n-1))
    simp only [bochnerL2Norm_const_smul] at hb
    exact hb
  apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) hb
  have h := (hc.abs.mul ht).add ((hc.sub_const 1).abs.mul_const (bochnerL2Norm ν f))
  simpa only [abs_one,mul_zero,sub_self,abs_zero,zero_mul,add_zero] using h

theorem inwardPullback_scaled_L2_error_tendsto (a : SpatialCoordinates d) (k : ℕ)
    {f : SpatialCoordinates d → ℝ} {F : ℕ → SpatialCoordinates d → ℝ}
    (hf : MemLp f 2 volume) (hF : ∀ n, MemLp (F n) 2 volume)
    (ht : Tendsto (fun n => bochnerL2Norm volume (fun x => F n x-f x)) atTop (𝓝 0)) :
    Tendsto (fun n => bochnerL2Norm volume (fun x =>
      (inwardRatio n)^k*inwardPullback a n (F n) x-f x)) atTop (𝓝 0) :=
  l2_scaled_error_tendsto hf (fun n => inwardPullback_memLp a n (hF n))
    (inwardPullback_L2_error_tendsto_diagonal a hf hF ht)
    (by simpa only [one_pow] using inwardRatio_tendsto.pow k)

end Carleman
