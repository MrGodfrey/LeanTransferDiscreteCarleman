module

public import Carleman.Spatial.SmoothLaplacianProduct
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Constant-direction derivatives of genuine smooth scalar functions.
These apply to space-time directions on the same product space. -/
@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def smoothD (e : E) (f : E → ℝ) (x : E) : ℝ := fderiv ℝ f x e

theorem smoothD_contDiff {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (e : E) :
    ContDiff ℝ ∞ (smoothD e f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem smoothD_add {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (e x : E) : smoothD e (fun y => f y+g y) x = smoothD e f x+smoothD e g x := by
  change fderiv ℝ (f+g) x e = _
  rw [fderiv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

theorem smoothD_sub {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (e x : E) : smoothD e (fun y => f y-g y) x = smoothD e f x-smoothD e g x := by
  change fderiv ℝ (f-g) x e = _
  rw [fderiv_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

theorem smoothD_neg (f : E → ℝ) (e x : E) :
    smoothD e (fun y => -f y) x = -smoothD e f x := by
  change fderiv ℝ (-f) x e = _
  rw [fderiv_neg]
  rfl

theorem smoothD_mul {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (e x : E) : smoothD e (fun y => f y*g y) x =
      smoothD e f x*g x+f x*smoothD e g x := by
  change fderiv ℝ (f*g) x e = _
  rw [fderiv_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul,smoothD]
  ring

theorem smoothD_const_mul {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) (e x : E) :
    smoothD e (fun y => a*f y) x = a*smoothD e f x := by
  exact congrArg (fun A : E →L[ℝ] ℝ => A e) (fderiv_const_mul (hf.differentiable (by simp) x) a)

theorem smoothD_sq {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (e x : E) :
    smoothD e (fun y => (f y)^2) x = 2*f x*smoothD e f x := by
  simp only [pow_two,smoothD_mul hf hf]
  ring

theorem smoothD_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (e x : E) :
    smoothD e (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, smoothD e (f i) x := by
  change (fderiv ℝ (fun y => ∑ i ∈ s, f i y) x) e = _
  rw [fderiv_fun_sum (fun i hi => (hf i hi).differentiable (by simp) x)]
  simp only [sum_apply,smoothD]

theorem smoothD_comm {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (u v x : E) :
    smoothD u (smoothD v f) x = smoothD v (smoothD u f) x := by
  have hd := (hf.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ f)).differentiable (by simp)
  have he (e w : E) : smoothD e (smoothD w f) x = fderiv ℝ (fderiv ℝ f) x e w := by
    have h := (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    change fderiv ℝ (fun y => fderiv ℝ f y w) x e = _
    rw [h.fderiv]
    simp only [add_apply,ContinuousLinearMap.comp_apply,zero_apply,
      ContinuousLinearMap.flip_apply,map_zero,zero_add]
  rw [he,he]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq u v

end Carleman
