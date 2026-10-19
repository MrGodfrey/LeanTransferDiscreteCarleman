module

public import Carleman.Spatial.DirectionalYoung
public import Carleman.Spatial.PointwiseHeatConjugation

/-! Returning from the conjugated gradient to the original state's actual gradient. -/
@[expose] public noncomputable section
open scoped ContDiff BigOperators
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem heat_gradient_return (e : ι → E) {L u : E → ℝ}
    (hL : ContDiff ℝ ∞ L) (hu : ContDiff ℝ ∞ u) (x : E) :
    let z := fun y => Real.exp (L y)*u y
    (Real.exp (L x))^2*directionalEnergy e u x ≤
      2*directionalEnergy e z x+2*directionalEnergy e L x*(z x)^2 := by
  dsimp only
  let z := fun y => Real.exp (L y)*u y
  have he i : Real.exp (L x)*smoothD (e i) u x=smoothD (e i) z x-smoothD (e i) L x*z x := by
    dsimp only [z]
    rw [smoothD_mul hL.exp hu,smoothD_exp hL]
    ring
  have hi i : (Real.exp (L x))^2*(smoothD (e i) u x)^2 ≤
      2*(smoothD (e i) z x)^2+2*(smoothD (e i) L x)^2*(z x)^2 := by
    rw [← mul_pow,he]
    nlinarith [sq_nonneg (smoothD (e i) z x+smoothD (e i) L x*z x)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,directionalEnergy,z] using hh

end Carleman
