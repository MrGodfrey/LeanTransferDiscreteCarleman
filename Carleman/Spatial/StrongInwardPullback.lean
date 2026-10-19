module

public import Carleman.Spatial.ScalarAffineL2
public import Carleman.Spatial.StrongL2EnergyLimit

/-! The actual inward affine pullbacks converge strongly on every full-space
L² function. Smooth convolution supplies density; no pointwise convergence
of an arbitrary representative under dilation is assumed. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology Convolution
namespace Carleman
variable {d : ℕ}

theorem inwardPullback_L2_error_tendsto_of_continuous (a : SpatialCoordinates d)
    {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 volume) (hc : Continuous f) :
    Tendsto (fun n => bochnerL2Norm volume (fun x => inwardPullback a n f x-f x))
      atTop (𝓝 0) := by
  apply l2_error_tendsto_of_ae_of_energy_tendsto hf (fun n => inwardPullback_memLp a n hf)
    (Filter.Eventually.of_forall fun x => hc.continuousAt.tendsto.comp (inwardPoint_tendsto a x))
  have he (n : ℕ) : (∫ x, (inwardPullback a n f x)^2) =
      ((inwardRatio n)^d)⁻¹*(∫ x, (f x)^2) :=
    integral_scalarAffine_univ (fun x => (f x)^2) (inwardRatio_pos n) _
  simp only [he]
  simpa only [one_pow,inv_one,one_mul] using
    ((inwardRatio_tendsto.pow d).inv₀ (by simp)).mul_const (∫ x, (f x)^2)

theorem inwardPullback_L2_error_tendsto (a : SpatialCoordinates d)
    {f : SpatialCoordinates d → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun n => bochnerL2Norm volume (fun x => inwardPullback a n f x-f x))
      atTop (𝓝 0) := by
  let u := hf.toLp f
  let G := fun m => u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (spatialMollifier d m).value
  have hG (m : ℕ) : MemLp (G m) 2 volume :=
    ((spatialMollifier d m).convolution_right_memLp_norm_le
      (spatialMollifier_nonneg m) (spatialMollifier_integral m) u).1
  have hGc (m : ℕ) : Continuous (G m) := (spatialMollifier d m).smooth_convolution u |>.continuous
  have happrox : Tendsto (fun m => bochnerL2Norm volume (fun x => G m x-f x)) atTop (𝓝 0) := by
    apply (spatialMollifier_L2_error_tendsto u).congr'
    apply Filter.Eventually.of_forall
    intro m
    apply bochnerL2Norm_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  have hrev (m : ℕ) : bochnerL2Norm volume (f-G m)=bochnerL2Norm volume (fun x => G m x-f x) := by
    have he : f-G m=-(G m-f) := by funext x; simp only [Pi.sub_apply,Pi.neg_apply]; ring
    rw [he,bochnerL2Norm_neg]
    rfl
  let C : ℝ := (2:ℝ)^d
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hbound (m n : ℕ) :
      bochnerL2Norm volume (fun x => inwardPullback a n f x-f x) ≤
        (C+1)*bochnerL2Norm volume (fun x => G m x-f x)+
        bochnerL2Norm volume (fun x => inwardPullback a n (G m) x-G m x) := by
    have he : (fun x => inwardPullback a n f x-f x)=
        (fun x => (inwardPullback a n (f-G m) x+
          (inwardPullback a n (G m) x-G m x))+(G m x-f x)) := by
      funext x
      simp only [inwardPullback,Pi.sub_apply]
      ring
    rw [he]
    have hm₁ := inwardPullback_memLp a n (hf.sub (hG m))
    have hm₂ := (inwardPullback_memLp a n (hG m)).sub (hG m)
    have ht := (bochnerL2Norm_add (hm₁.add hm₂) ((hG m).sub hf)).trans
      (add_le_add (bochnerL2Norm_add hm₁ hm₂) le_rfl)
    have hp := inwardPullback_L2_le a n (hf.sub (hG m))
    rw [hrev] at hp
    change bochnerL2Norm volume (inwardPullback a n (f-G m)) ≤
      C*bochnerL2Norm volume (fun x => G m x-f x) at hp
    convert ht.trans (add_le_add (add_le_add hp le_rfl) le_rfl) using 1
    change (C+1)*bochnerL2Norm volume (G m-f)+bochnerL2Norm volume (inwardPullback a n (G m)-G m)=
      C*bochnerL2Norm volume (G m-f)+bochnerL2Norm volume (inwardPullback a n (G m)-G m)+bochnerL2Norm volume (G m-f)
    ring
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall fun n => hb.trans_le (bochnerL2Norm_nonneg _)
  · intro ε hε
    have hδ : (0:ℝ) < ε/(2*(C+1)) := div_pos hε (mul_pos (by norm_num) (by linarith))
    obtain ⟨m,hm⟩ := (happrox.eventually (gt_mem_nhds hδ)).exists
    have ht := inwardPullback_L2_error_tendsto_of_continuous a (hG m) (hGc m)
    filter_upwards [ht.eventually (gt_mem_nhds (half_pos hε))] with n hn
    have hm' : (C+1)*bochnerL2Norm volume (fun x => G m x-f x) < ε/2 := by
      have hh := (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) (by linarith : 0<C+1))).mp hm
      nlinarith
    exact (hbound m n).trans_lt (by linarith)

end Carleman
