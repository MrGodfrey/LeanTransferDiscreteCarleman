module

public import Carleman.Spatial.AffineNodalBound

/-! True weighted integral estimates, retaining the original cell volume and
using only genuine positive scalar weights and continuous representatives. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Carleman
variable {d : ℕ}

theorem norm_sq_div_integral_le {F : Type*} [NormedAddCommGroup F]
    (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
    (w : SpatialCoordinates d → ℝ) (e : SpatialCoordinates d → F)
    (hw : ContinuousOn w (simplicialCell T.points))
    (he : ContinuousOn e (simplicialCell T.points))
    (hwpos : ∀ x ∈ simplicialCell T.points, 0 < w x)
    {b E B : ℝ} (hb : 0 < b) (hB : 0 ≤ B)
    (hcomp : ∀ x ∈ simplicialCell T.points, b ≤ E*w x)
    (hbound : ∀ x ∈ simplicialCell T.points, ‖e x‖ ≤ B*b) :
    (∫ x in simplicialCell T.points, ‖e x‖^2/w x) ≤
      E*b*B^2*volume.real (simplicialCell T.points) := by
  have hi := (he.norm.pow 2).div hw (fun x hx => (hwpos x hx).ne')
  calc
    _ ≤ ∫ _x in simplicialCell T.points, E*b*B^2 := by
      apply integral_mono_ae (hi.integrableOn_compact (simplicialCell_compact T.points)) (integrable_const _)
      filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
      apply (div_le_iff₀ (hwpos x hx)).mpr
      calc
        ‖e x‖^2 ≤ (B*b)^2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB hb.le)).mpr (hbound x hx)
        _ = (b*B^2)*b := by ring
        _ ≤ (b*B^2)*(E*w x) := mul_le_mul_of_nonneg_left (hcomp x hx) (by positivity)
        _ = _ := by ring
    _ = _ := by simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_comm]

theorem affineNodalBound_weighted_energy : ∃ C > (0:ℝ),
    ∀ (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
      (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) (q : ℝ) (w : SpatialCoordinates d → ℝ),
      ContinuousOn w (simplicialCell T.points) →
    ∀ b E : ℝ, 0 < b → 0 ≤ E →
      (∀ x ∈ simplicialCell T.points, b ≤ E*w x) →
      b*(q^2*(affineNodalBound T p : ℝ)+2*q*‖affineScalarDerivative p‖)^2*
        volume.real (simplicialCell T.points) ≤
      C*E*(q^4*(∫ x in simplicialCell T.points, w x*(p x)^2)+
        q^2*(∫ x in simplicialCell T.points, w x*‖derivativeOneFiber (fderiv ℝ p x)‖^2)) := by
  obtain ⟨C,hC,henergy⟩ := affineNodalBound_energy (d := d)
  refine ⟨C,hC,?_⟩
  intro T p q w hw b E hb hE hcomp
  have hcont : ContinuousOn (fun x => ‖derivativeOneFiber (fderiv ℝ p x)‖^2)
      (simplicialCell T.points) := by
    simp_rw [(affineScalar_hasFDerivAt p _).fderiv]
    exact continuous_const.continuousOn
  have hi : b*(∫ x in simplicialCell T.points, (p x)^2) ≤
      E*(∫ x in simplicialCell T.points, w x*(p x)^2) := by
    rw [← integral_const_mul,← integral_const_mul]
    apply integral_mono_ae
      ((continuous_const.mul (p.continuous_of_finiteDimensional.pow 2)).continuousOn.integrableOn_compact (simplicialCell_compact T.points))
      ((continuous_const.continuousOn.mul (hw.mul (p.continuous_of_finiteDimensional.pow 2).continuousOn)).integrableOn_compact (simplicialCell_compact T.points))
    filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
    change b*(p x)^2 ≤ E*(w x*(p x)^2)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hcomp x hx) (sq_nonneg (p x))
  have hj : b*(∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ p x)‖^2) ≤
      E*(∫ x in simplicialCell T.points, w x*‖derivativeOneFiber (fderiv ℝ p x)‖^2) := by
    rw [← integral_const_mul,← integral_const_mul]
    apply integral_mono_ae
      ((continuous_const.continuousOn.mul hcont).integrableOn_compact (simplicialCell_compact T.points))
      ((continuous_const.continuousOn.mul (hw.mul hcont)).integrableOn_compact (simplicialCell_compact T.points))
    filter_upwards [ae_restrict_mem (simplicialCell_measurable T.points)] with x hx
    change b*‖derivativeOneFiber (fderiv ℝ p x)‖^2 ≤ E*(w x*‖derivativeOneFiber (fderiv ℝ p x)‖^2)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hcomp x hx) (sq_nonneg _)
  calc
    _ = b*((q^2*(affineNodalBound T p : ℝ)+2*q*‖affineScalarDerivative p‖)^2*
        volume.real (simplicialCell T.points)) := by ring
    _ ≤ b*(C*(q^4*(∫ x in simplicialCell T.points, (p x)^2)+
        q^2*(∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ p x)‖^2))) :=
      mul_le_mul_of_nonneg_left (henergy T p q) hb.le
    _ = C*(q^4*(b*(∫ x in simplicialCell T.points, (p x)^2))+
        q^2*(b*(∫ x in simplicialCell T.points, ‖derivativeOneFiber (fderiv ℝ p x)‖^2))) := by ring
    _ ≤ C*(q^4*(E*(∫ x in simplicialCell T.points, w x*(p x)^2))+
        q^2*(E*(∫ x in simplicialCell T.points, w x*‖derivativeOneFiber (fderiv ℝ p x)‖^2))) := by
      gcongr
    _ = _ := by ring

theorem weighted_cell_error_transfer : ∃ C > (0:ℝ),
    ∀ (T : Affine.Simplex ℝ (SpatialCoordinates d) d)
      (p : SpatialCoordinates d →ᵃ[ℝ] ℝ) (q : ℝ), 0 ≤ q →
    ∀ (w e : SpatialCoordinates d → ℝ),
      ContinuousOn w (simplicialCell T.points) → ContinuousOn e (simplicialCell T.points) →
      (∀ x ∈ simplicialCell T.points, 0 < w x) →
    ∀ b E A : ℝ, 0 < b → 0 ≤ E → 0 ≤ A →
      (∀ x ∈ simplicialCell T.points, b ≤ E*w x) →
      (∀ x ∈ simplicialCell T.points, |e x| ≤ A*b*
        (q^2*(affineNodalBound T p : ℝ)+2*q*‖affineScalarDerivative p‖)) →
      (∫ x in simplicialCell T.points, (e x)^2/w x) ≤
      C*E^2*A^2*(q^4*(∫ x in simplicialCell T.points, w x*(p x)^2)+
        q^2*(∫ x in simplicialCell T.points, w x*‖derivativeOneFiber (fderiv ℝ p x)‖^2)) := by
  obtain ⟨C,hC,henergy⟩ := affineNodalBound_weighted_energy (d := d)
  refine ⟨C,hC,?_⟩
  intro T p q hq w e hw he hwpos b E A hb hE hA hcomp hbound
  let J := q^2*(affineNodalBound T p : ℝ)+2*q*‖affineScalarDerivative p‖
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have he' := norm_sq_div_integral_le T w e hw he hwpos hb (mul_nonneg hA hJ) hcomp
    (fun x hx => by simpa only [Real.norm_eq_abs,J,mul_assoc,mul_left_comm,mul_comm] using hbound x hx)
  simp only [Real.norm_eq_abs,sq_abs] at he'
  calc
    _ ≤ E*b*(A*J)^2*volume.real (simplicialCell T.points) := he'
    _ = E*A^2*(b*J^2*volume.real (simplicialCell T.points)) := by ring
    _ ≤ E*A^2*(C*E*(q^4*(∫ x in simplicialCell T.points, w x*(p x)^2)+
        q^2*(∫ x in simplicialCell T.points, w x*‖derivativeOneFiber (fderiv ℝ p x)‖^2))) :=
      mul_le_mul_of_nonneg_left (henergy T p q w hw b E hb hE hcomp) (by positivity)
    _ = _ := by ring

end Carleman
