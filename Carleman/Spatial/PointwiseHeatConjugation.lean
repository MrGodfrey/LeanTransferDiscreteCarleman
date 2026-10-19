module

public import Carleman.Spatial.PointwiseHeatIdentity
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Exact conjugation of the real heat operator, and the pointwise Carleman
inequality with the actual time derivative and divergence retained. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff BigOperators
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem smoothD_exp {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (e x : E) :
    smoothD e (fun y => Real.exp (f y)) x = Real.exp (f x)*smoothD e f x := by
  have h := (hf.differentiable (by simp) x).hasFDerivAt.exp
  rw [smoothD,h.fderiv]
  rfl

theorem smoothD_exp_neg {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (e x : E) :
    smoothD e (fun y => Real.exp (-f y)) x = -(Real.exp (-f x)*smoothD e f x) := by
  rw [smoothD_exp hf.neg,smoothD_neg f]
  ring

theorem directionalLap_exp_neg (e : ι → E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    directionalLap e (fun y => Real.exp (-f y)) x =
      Real.exp (-f x)*(directionalEnergy e f x-directionalLap e f x) := by
  have he (v : E) : smoothD v (fun y => Real.exp (-f y)) =
      (fun y => -(Real.exp (-f y)*smoothD v f y)) :=
    funext fun y => smoothD_exp_neg hf v y
  have hsecond (v : E) : smoothD v (smoothD v (fun y => Real.exp (-f y))) x =
      Real.exp (-f x)*((smoothD v f x)^2-smoothD v (smoothD v f) x) := by
    rw [he,smoothD_neg,
      smoothD_mul hf.neg.exp (smoothD_contDiff hf v),smoothD_exp_neg hf]
    ring
  simp only [directionalLap,hsecond,directionalEnergy,Finset.mul_sum,
    ← Finset.sum_sub_distrib,mul_sub]

theorem directionalPair_exp_neg (e : ι → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (g : E → ℝ) (x : E) :
    directionalPair e (fun y => Real.exp (-f y)) g x =
      -Real.exp (-f x)*directionalPair e f g x := by
  simp only [directionalPair,smoothD_exp_neg hf,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

def heatConjugationK (e : ι → E) (t : E) (l p : E → ℝ) (x : E) : ℝ :=
  smoothD t l x+directionalEnergy e l x-directionalLap e l x-p x

def heatCarlemanA (e : ι → E) (l p : E → ℝ) (x : E) : ℝ :=
  directionalEnergy e l x-directionalLap e l x-p x

theorem heatConjugationK_eq (e : ι → E) (t : E) (l p : E → ℝ) (x : E) :
    heatConjugationK e t l p x = smoothD t l x+heatCarlemanA e l p x := by
  unfold heatConjugationK heatCarlemanA
  ring

theorem heatConjugationK_contDiff (e : ι → E) (t : E) {l p : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (heatConjugationK e t l p) :=
  (((smoothD_contDiff hl t).add (directionalEnergy_contDiff e hl)).sub
    (directionalLap_contDiff e hl)).sub hp

theorem pointwiseHeatB_original_formula (e : ι → E) (t : E) {l p : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hp : ContDiff ℝ ∞ p) (x : E) :
    pointwiseHeatB e t l (heatConjugationK e t l p) p x =
      2*heatCarlemanA e l p x*p x+
      2*(∑ i, smoothD (e i) (fun y => heatCarlemanA e l p y*smoothD (e i) l y) x)+
      2*(∑ i, smoothD (e i) (fun y => smoothD t l y*smoothD (e i) l y) x)+
      2*p x*smoothD t l x+smoothD t (smoothD t l) x+
        smoothD t (heatCarlemanA e l p) x := by
  have hA : ContDiff ℝ ∞ (heatCarlemanA e l p) :=
    ((directionalEnergy_contDiff e hl).sub (directionalLap_contDiff e hl)).sub hp
  have hk : heatConjugationK e t l p =
      (fun y => smoothD t l y+heatCarlemanA e l p y) :=
    funext fun y => heatConjugationK_eq e t l p y
  have hs i : (fun y => (smoothD t l y+heatCarlemanA e l p y)*smoothD (e i) l y) =
      (fun y => smoothD t l y*smoothD (e i) l y+
        heatCarlemanA e l p y*smoothD (e i) l y) := by
    funext y
    ring
  unfold pointwiseHeatB
  rw [hk,smoothD_add (smoothD_contDiff hl t) hA]
  simp only [hs,smoothD_add ((smoothD_contDiff hl t).mul (smoothD_contDiff hl _))
    (hA.mul (smoothD_contDiff hl _)),Finset.sum_add_distrib]
  ring

theorem pointwise_heat_conjugation (e : ι → E) (t : E) {l z : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hz : ContDiff ℝ ∞ z) (p : E → ℝ) (x : E) :
    Real.exp (l x)*(smoothD t (fun y => Real.exp (-l y)*z y) x-
      directionalLap e (fun y => Real.exp (-l y)*z y) x) =
      smoothD t z x-directionalLap e z x+2*directionalPair e l z x-
        (heatConjugationK e t l p x+p x)*z x := by
  rw [smoothD_mul hl.neg.exp hz,smoothD_exp_neg hl,directionalLap_mul e hl.neg.exp hz,
    directionalLap_exp_neg e hl,directionalPair_exp_neg e hl]
  have he := Real.exp_add (l x) (-l x)
  rw [add_neg_cancel,Real.exp_zero] at he
  unfold heatConjugationK
  linear_combination (smoothD t z x-directionalLap e z x+2*directionalPair e l z x-
    (smoothD t l x+directionalEnergy e l x-directionalLap e l x)*z x)*he.symm

theorem pointwise_heat_carleman_identity (e : ι → E) (t : E) {l p z : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hp : ContDiff ℝ ∞ p) (hz : ContDiff ℝ ∞ z) (x : E) :
    (Real.exp (l x)*(smoothD t (fun y => Real.exp (-l y)*z y) x-
      directionalLap e (fun y => Real.exp (-l y)*z y) x))^2+
      smoothD t (pointwiseHeatTimeFlux e (heatConjugationK e t l p) z) x+
      (∑ i, smoothD (e i) (pointwiseHeatFlux e t l (heatConjugationK e t l p) p z i) x) =
    (directionalLap e z x+heatConjugationK e t l p x*z x)^2+
      (smoothD t z x+2*directionalPair e l z x-p x*z x)^2+
      2*pointwiseHeatMatrixEnergy e l p z x-
      2*directionalPair e p z x*z x+
        pointwiseHeatB e t l (heatConjugationK e t l p) p x*(z x)^2 := by
  rw [pointwise_heat_conjugation e t hl hz p]
  exact pointwise_heat_identity e t hl (heatConjugationK_contDiff e t hl hp) hp hz x

theorem pointwise_heat_carleman_inequality (e : ι → E) (t : E) {l p z : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hp : ContDiff ℝ ∞ p) (hz : ContDiff ℝ ∞ z) (x : E) :
    (directionalLap e z x+heatConjugationK e t l p x*z x)^2+
      2*pointwiseHeatMatrixEnergy e l p z x-2*directionalPair e p z x*z x+
        pointwiseHeatB e t l (heatConjugationK e t l p) p x*(z x)^2 ≤
    (Real.exp (l x)*(smoothD t (fun y => Real.exp (-l y)*z y) x-
      directionalLap e (fun y => Real.exp (-l y)*z y) x))^2+
      smoothD t (pointwiseHeatTimeFlux e (heatConjugationK e t l p) z) x+
      (∑ i, smoothD (e i) (pointwiseHeatFlux e t l (heatConjugationK e t l p) p z i) x) := by
  rw [pointwise_heat_carleman_identity e t hl hp hz]
  nlinarith [sq_nonneg (smoothD t z x+2*directionalPair e l z x-p x*z x)]

end Carleman
