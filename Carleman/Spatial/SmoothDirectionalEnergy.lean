module

public import Carleman.Spatial.SmoothDirectionalCalculus

/-! Pointwise differential product identities, using actual derivatives and
finite spatial directions. No integration or boundary hypotheses enter here. -/
@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open scoped ContDiff BigOperators
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def directionalLap (e : ι → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, smoothD (e i) (smoothD (e i) f) x

def directionalPair (e : ι → E) (f g : E → ℝ) (x : E) : ℝ :=
  ∑ i, smoothD (e i) f x*smoothD (e i) g x

def directionalEnergy (e : ι → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, (smoothD (e i) f x)^2

def directionalHessianForm (e : ι → E) (f g : E → ℝ) (x : E) : ℝ :=
  ∑ i, ∑ j, smoothD (e i) (smoothD (e j) f) x*smoothD (e i) g x*smoothD (e j) g x

theorem directionalLap_contDiff (e : ι → E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (directionalLap e f) :=
  ContDiff.sum fun i _ => smoothD_contDiff (smoothD_contDiff hf (e i)) (e i)

theorem directionalPair_contDiff (e : ι → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (directionalPair e f g) :=
  ContDiff.sum fun i _ => (smoothD_contDiff hf (e i)).mul (smoothD_contDiff hg (e i))

theorem directionalEnergy_contDiff (e : ι → E) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (directionalEnergy e f) :=
  ContDiff.sum fun i _ => (smoothD_contDiff hf (e i)).pow 2

theorem smoothD_directionalPair (e : ι → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v x : E) :
    smoothD v (directionalPair e f g) x =
      ∑ i, (smoothD v (smoothD (e i) f) x*smoothD (e i) g x+
        smoothD (e i) f x*smoothD v (smoothD (e i) g) x) := by
  unfold directionalPair
  rw [smoothD_sum _ (fun i _ => (smoothD_contDiff hf (e i)).mul (smoothD_contDiff hg (e i)))]
  exact Finset.sum_congr rfl fun i _ =>
    smoothD_mul (smoothD_contDiff hf (e i)) (smoothD_contDiff hg (e i)) v x

theorem smoothD_directionalEnergy (e : ι → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (v x : E) :
    smoothD v (directionalEnergy e f) x =
      2*∑ i, smoothD (e i) f x*smoothD v (smoothD (e i) f) x := by
  unfold directionalEnergy
  rw [smoothD_sum _ (fun i _ => (smoothD_contDiff hf (e i)).pow 2),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smoothD_sq (smoothD_contDiff hf (e i))]
  ring

theorem directional_transport_cancellation (e : ι → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    2*(∑ i, smoothD (e i) (directionalPair e f g) x*smoothD (e i) g x) =
      2*directionalHessianForm e f g x+
        ∑ i, smoothD (e i) f x*smoothD (e i) (directionalEnergy e g) x := by
  have hswap :
      (∑ i, ∑ j, smoothD (e j) f x*smoothD (e i) (smoothD (e j) g) x*smoothD (e i) g x) =
      ∑ i, ∑ j, smoothD (e i) f x*smoothD (e j) g x*smoothD (e i) (smoothD (e j) g) x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [smoothD_comm hg (e j) (e i)]
    ring
  simp only [smoothD_directionalPair e hf hg,Finset.sum_mul,add_mul,
    Finset.sum_add_distrib] 
  have hmain :
      (∑ i, ∑ j, smoothD (e i) (smoothD (e j) f) x*smoothD (e j) g x*smoothD (e i) g x) =
      directionalHessianForm e f g x := by
    unfold directionalHessianForm
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hmain,hswap]
  simp only [smoothD_directionalEnergy e hg,Finset.mul_sum]
  ring_nf
  simp only [Finset.sum_mul]

theorem directionalPair_comm (e : ι → E) (f g : E → ℝ) (x : E) :
    directionalPair e f g x = directionalPair e g f x := by
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem directionalPair_mul_left (e : ι → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (h : E → ℝ) (x : E) :
    directionalPair e (fun y => f y*g y) h x =
      g x*directionalPair e f h x+f x*directionalPair e g h x := by
  simp only [directionalPair,smoothD_mul hf hg,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem directionalPair_sq_left (e : ι → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (g : E → ℝ) (x : E) :
    directionalPair e (fun y => (f y)^2) g x = 2*f x*directionalPair e f g x := by
  simp only [directionalPair,smoothD_sq hf,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem directionalPair_self (e : ι → E) (f : E → ℝ) (x : E) :
    directionalPair e f f x = directionalEnergy e f x := by
  simp only [directionalPair,directionalEnergy,pow_two]

theorem directional_div_product (e : ι → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    (∑ i, smoothD (e i) (fun y => f y*smoothD (e i) g y) x) =
      directionalPair e f g x+f x*directionalLap e g x := by
  simp only [smoothD_mul hf (smoothD_contDiff hg _),directionalPair,directionalLap,
    Finset.sum_add_distrib,Finset.mul_sum]

theorem smoothD_directionalEnergy_time (e : ι → E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (t x : E) :
    smoothD t (directionalEnergy e f) x = 2*directionalPair e (smoothD t f) f x := by
  rw [smoothD_directionalEnergy e hf]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [smoothD_comm hf t (e i)]
  exact mul_comm _ _

theorem directionalLap_mul (e : ι → E) {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    directionalLap e (fun y => f y*g y) x =
      g x*directionalLap e f x+2*directionalPair e f g x+f x*directionalLap e g x := by
  have he (v : E) : smoothD v (fun y => f y*g y) =
      (fun y => smoothD v f y*g y+f y*smoothD v g y) :=
    funext fun y => smoothD_mul hf hg v y
  have hsecond (v : E) : smoothD v (smoothD v (fun y => f y*g y)) x =
      g x*smoothD v (smoothD v f) x+2*smoothD v f x*smoothD v g x+
        f x*smoothD v (smoothD v g) x := by
    rw [he,smoothD_add ((smoothD_contDiff hf v).mul hg) (hf.mul (smoothD_contDiff hg v)),
      smoothD_mul (smoothD_contDiff hf v) hg,smoothD_mul hf (smoothD_contDiff hg v)]
    ring
  simp only [directionalLap,hsecond,directionalPair,Finset.sum_add_distrib,Finset.mul_sum]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by ring

end Carleman
