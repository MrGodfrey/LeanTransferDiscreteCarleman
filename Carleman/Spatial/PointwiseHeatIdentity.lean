module

public import Carleman.Spatial.SmoothDirectionalEnergy

/-! The real heat Carleman pointwise identity for genuine constant-direction
derivatives. The nonnegative second square is retained before taking the inequality. -/
@[expose] public noncomputable section
set_option maxHeartbeats 2400000
open scoped ContDiff BigOperators
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def pointwiseHeatFlux (e : ι → E) (t : E) (l k p z : E → ℝ) (i : ι) (x : E) : ℝ :=
  2*(smoothD t z x*smoothD (e i) z x)+
    4*(directionalPair e l z x*smoothD (e i) z x)-
    2*(directionalEnergy e z x*smoothD (e i) l x)-
    2*(p x*z x*smoothD (e i) z x)+
    2*(k x*(z x)^2*smoothD (e i) l x)

def pointwiseHeatTimeFlux (e : ι → E) (k z : E → ℝ) (x : E) : ℝ :=
  k x*(z x)^2-directionalEnergy e z x

def pointwiseHeatB (e : ι → E) (t : E) (l k p : E → ℝ) (x : E) : ℝ :=
  smoothD t k x+2*(∑ i, smoothD (e i) (fun y => k y*smoothD (e i) l y) x)+
    2*k x*p x

def pointwiseHeatMatrixEnergy (e : ι → E) (l p z : E → ℝ) (x : E) : ℝ :=
  2*directionalHessianForm e l z x-(directionalLap e l x+p x)*directionalEnergy e z x

theorem pointwiseHeatFlux_divergence (e : ι → E) (t : E) {l k p z : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hk : ContDiff ℝ ∞ k)
    (hp : ContDiff ℝ ∞ p) (hz : ContDiff ℝ ∞ z) (x : E) :
    (∑ i, smoothD (e i) (pointwiseHeatFlux e t l k p z i) x) =
      2*(directionalPair e (smoothD t z) z x+smoothD t z x*directionalLap e z x)+
      4*(directionalPair e (directionalPair e l z) z x+
        directionalPair e l z x*directionalLap e z x)-
      2*(directionalPair e (directionalEnergy e z) l x+
        directionalEnergy e z x*directionalLap e l x)-
      2*(directionalPair e (fun y => p y*z y) z x+p x*z x*directionalLap e z x)+
      2*(directionalPair e (fun y => k y*(z y)^2) l x+k x*(z x)^2*directionalLap e l x) := by
  have h1 i := (smoothD_contDiff hz t).mul (smoothD_contDiff hz (e i))
  have h2 i := (directionalPair_contDiff e hl hz).mul (smoothD_contDiff hz (e i))
  have h3 i := (directionalEnergy_contDiff e hz).mul (smoothD_contDiff hl (e i))
  have h4 i := (hp.mul hz).mul (smoothD_contDiff hz (e i))
  have h5 i := (hk.mul (hz.pow 2)).mul (smoothD_contDiff hl (e i))
  have hc {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
      ContDiff ℝ ∞ (fun y => a*f y) := contDiff_const.mul hf
  have he i : smoothD (e i) (pointwiseHeatFlux e t l k p z i) x =
      2*smoothD (e i) (fun y => smoothD t z y*smoothD (e i) z y) x+
      4*smoothD (e i) (fun y => directionalPair e l z y*smoothD (e i) z y) x-
      2*smoothD (e i) (fun y => directionalEnergy e z y*smoothD (e i) l y) x-
      2*smoothD (e i) (fun y => p y*z y*smoothD (e i) z y) x+
      2*smoothD (e i) (fun y => k y*(z y)^2*smoothD (e i) l y) x := by
    unfold pointwiseHeatFlux
    rw [smoothD_add (((hc (h1 i) 2).add (hc (h2 i) 4)).sub (hc (h3 i) 2) |>.sub (hc (h4 i) 2)) (hc (h5 i) 2),
      smoothD_sub (((hc (h1 i) 2).add (hc (h2 i) 4)).sub (hc (h3 i) 2)) (hc (h4 i) 2),
      smoothD_sub ((hc (h1 i) 2).add (hc (h2 i) 4)) (hc (h3 i) 2),
      smoothD_add (hc (h1 i) 2) (hc (h2 i) 4)]
    rw [smoothD_const_mul (h1 i),smoothD_const_mul (h2 i),smoothD_const_mul (h3 i),
      smoothD_const_mul (h4 i),smoothD_const_mul (h5 i)]
  simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [directional_div_product e (smoothD_contDiff hz t) hz,
    directional_div_product e (directionalPair_contDiff e hl hz) hz,
    directional_div_product e (directionalEnergy_contDiff e hz) hl,
    directional_div_product e (hp.mul hz) hz,
    directional_div_product e (hk.mul (hz.pow 2)) hl]

theorem pointwise_heat_identity (e : ι → E) (t : E) {l k p z : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hk : ContDiff ℝ ∞ k)
    (hp : ContDiff ℝ ∞ p) (hz : ContDiff ℝ ∞ z) (x : E) :
    (smoothD t z x-directionalLap e z x+2*directionalPair e l z x-(k x+p x)*z x)^2+
      smoothD t (pointwiseHeatTimeFlux e k z) x+
      (∑ i, smoothD (e i) (pointwiseHeatFlux e t l k p z i) x) =
    (directionalLap e z x+k x*z x)^2+
      (smoothD t z x+2*directionalPair e l z x-p x*z x)^2+
      2*pointwiseHeatMatrixEnergy e l p z x-
      2*directionalPair e p z x*z x+pointwiseHeatB e t l k p x*(z x)^2 := by
  have htime : smoothD t (pointwiseHeatTimeFlux e k z) x =
      smoothD t k x*(z x)^2+2*k x*z x*smoothD t z x-
        2*directionalPair e (smoothD t z) z x := by
    unfold pointwiseHeatTimeFlux
    rw [smoothD_sub (hk.mul (hz.pow 2)) (directionalEnergy_contDiff e hz),
      smoothD_mul hk (hz.pow 2),smoothD_sq hz,smoothD_directionalEnergy_time e hz]
    ring
  have htransport := directional_transport_cancellation e hl hz x
  change 2*directionalPair e (directionalPair e l z) z x =
    2*directionalHessianForm e l z x+directionalPair e l (directionalEnergy e z) x at htransport
  rw [directionalPair_comm e l (directionalEnergy e z)] at htransport
  rw [htime,pointwiseHeatFlux_divergence e t hl hk hp hz,
    directionalPair_mul_left e hp hz,directionalPair_self,
    directionalPair_mul_left e hk (hz.pow 2),directionalPair_sq_left e hz,
    directionalPair_comm e z l]
  simp only [pointwiseHeatMatrixEnergy,pointwiseHeatB,directional_div_product e hk hl]
  nlinarith [htransport]

end Carleman
