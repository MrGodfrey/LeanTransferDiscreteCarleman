module

public import Carleman.Spatial.HalfspaceHeatBoundary

/-! Regularity of the actual heat identity terms before integration. -/
@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem directionalHessianForm_contDiff (e : ι → E) {l z : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (directionalHessianForm e l z) := by
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (((smoothD_contDiff (smoothD_contDiff hl (e j)) (e i)).mul
      (smoothD_contDiff hz (e i))).mul (smoothD_contDiff hz (e j)))

theorem pointwiseHeatMatrixEnergy_contDiff (e : ι → E) {l p z : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hp : ContDiff ℝ ∞ p) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (pointwiseHeatMatrixEnergy e l p z) :=
  (contDiff_const.mul (directionalHessianForm_contDiff e hl hz)).sub
    (((directionalLap_contDiff e hl).add hp).mul (directionalEnergy_contDiff e hz))

theorem pointwiseHeatB_contDiff (e : ι → E) (t : E) {l k p : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hk : ContDiff ℝ ∞ k) (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (pointwiseHeatB e t l k p) := by
  have hs : ContDiff ℝ ∞ (fun x => ∑ i, smoothD (e i) (fun y => k y*smoothD (e i) l y) x) :=
    ContDiff.sum fun i _ => smoothD_contDiff (hk.mul (smoothD_contDiff hl (e i))) (e i)
  exact ((smoothD_contDiff hk t).add (contDiff_const.mul hs)).add
    ((contDiff_const.mul hk).mul hp)

def heatCarlemanBulk (e : ι → E) (t : E) (l k p z : E → ℝ) (x : E) : ℝ :=
  (directionalLap e z x+k x*z x)^2+2*pointwiseHeatMatrixEnergy e l p z x-
    2*directionalPair e p z x*z x+pointwiseHeatB e t l k p x*(z x)^2

theorem heatCarlemanBulk_contDiff (e : ι → E) (t : E) {l k p z : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hk : ContDiff ℝ ∞ k)
    (hp : ContDiff ℝ ∞ p) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (heatCarlemanBulk e t l k p z) :=
  (((((directionalLap_contDiff e hz).add (hk.mul hz)).pow 2).add
    (contDiff_const.mul (pointwiseHeatMatrixEnergy_contDiff e hl hp hz))).sub
    ((contDiff_const.mul (directionalPair_contDiff e hp hz)).mul hz)).add
    ((pointwiseHeatB_contDiff e t hl hk hp).mul (hz.pow 2))

theorem pointwiseHeatDivergence_contDiff (e : ι → E) (t : E) {l k p z : E → ℝ}
    (hl : ContDiff ℝ ∞ l) (hk : ContDiff ℝ ∞ k)
    (hp : ContDiff ℝ ∞ p) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (fun x => ∑ i, smoothD (e i) (pointwiseHeatFlux e t l k p z i) x) :=
  ContDiff.sum fun i _ => smoothD_contDiff (pointwiseHeatFlux_contDiff e t hl hk hp hz i) (e i)

end Carleman
