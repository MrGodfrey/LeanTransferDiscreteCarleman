module

public import Carleman.Spatial.ConvolutionL2
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Integration by parts on the genuine smooth convolutions of a weak
derivative chain. Compact support of the original state is not required. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution ContDiff
namespace Carleman
variable {d : ℕ}

theorem real_convolution_comm (f g : SpatialCoordinates d → ℝ) :
    f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
      g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  exact convolution_symm _ (by ext; rfl)

namespace SpatialTest
variable (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
  (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)

include hκ hunit in
theorem convolution_right_memLp_norm_le (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))) :
    MemLp (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) 2 volume ∧
      bochnerL2Norm volume (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value) ≤ ‖u‖ := by
  rw [real_convolution_comm]
  exact κ.convolution_memLp_norm_le hκ hunit u

include hκ hunit in
theorem weak_chain_convolution_sq_le {e : SpatialCoordinates d}
    {u v z : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (huv : IsWeakSpatialDerivative volume univ e u v)
    (hvz : IsWeakSpatialDerivative volume univ e v z) :
    (bochnerL2Norm volume (v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value))^2 ≤ ‖u‖*‖z‖ := by
  let F := u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  let G := v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  let K := z ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  have hF := κ.convolution_right_memLp_norm_le hκ hunit u
  have hG := κ.convolution_right_memLp_norm_le hκ hunit v
  have hK := κ.convolution_right_memLp_norm_le hκ hunit z
  have hdF : ∀ x, fderiv ℝ F x e = G x := huv.fderiv_convolution κ
  have hdG : ∀ x, fderiv ℝ G x e = K x := hvz.fderiv_convolution κ
  have hGG : Integrable (fun x => G x*G x) volume := by
    simpa only [pow_two] using hG.1.integrable_sq
  have hFK : Integrable (fun x => F x*K x) volume :=
    memLp_one_iff_integrable.mp (hF.1.mul hK.1)
  have hFG : Integrable (fun x => F x*G x) volume :=
    memLp_one_iff_integrable.mp (hF.1.mul hG.1)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := e)
    (f := F) (g := G) (μ := volume)
    (by simpa only [hdF] using hGG) (by simpa only [hdG] using hFK) hFG
    (fun x _ => (κ.smooth_convolution u).differentiable (by simp) x)
    (fun x _ => (κ.smooth_convolution v).differentiable (by simp) x)
  simp only [hdF, hdG] at hibp
  have he : (bochnerL2Norm volume G)^2 = -(∫ x, F x*K x) := by
    rw [← integral_sq_eq_bochnerL2Norm_sq hG.1]
    simpa only [pow_two] using (neg_eq_iff_eq_neg.mpr hibp).symm
  rw [he]
  calc
    -(∫ x, F x*K x) ≤ |∫ x, F x*K x| := neg_le_abs _
    _ ≤ bochnerL2Norm volume F*bochnerL2Norm volume K := abs_integral_mul_le hF.1 hK.1
    _ ≤ ‖u‖*‖z‖ := mul_le_mul hF.2 hK.2 (bochnerL2Norm_nonneg _) (norm_nonneg _)

end SpatialTest
end Carleman
