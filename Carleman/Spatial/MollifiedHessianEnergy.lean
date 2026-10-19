module

public import Carleman.Spatial.LocalHessianConvolution
public import Carleman.Spatial.DirichletPoincare

/-! Local Hessian energy of a genuine mollification, controlled by the
original weak second derivatives. The tensor comparison constant depends
only on the fixed dimension, and zero extension is used only as L² data. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Convolution ContDiff
namespace Carleman
variable {d : ℕ} {S K : Set (SpatialCoordinates d)}

theorem mollified_hessian_energy_le (hK : MeasurableSet K)
    (u : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (v : Fin d → Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (z : Fin d → Fin d → Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hv : ∀ i, IsWeakSpatialDerivative volume S (EuclideanSpace.basisFun (Fin d) ℝ i) u (v i))
    (hz : ∀ i j, IsWeakSpatialDerivative volume S (EuclideanSpace.basisFun (Fin d) ℝ j) (v i) (z i j))
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    (hinside : ∀ x ∈ K, ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    let U := u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
    IntegrableOn (fun x => ‖iteratedFDeriv ℝ 2 U x‖^2) K ∧
      (∫ x in K, ‖iteratedFDeriv ℝ 2 U x‖^2) ≤
        (tensorCoordinateBound d 2)^2 * ∑ w : Fin 2 → Fin d, ‖z (w 0) (w 1)‖^2 := by
  intro U
  let Z := fun w : Fin 2 → Fin d => z (w 0) (w 1) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
  have hm (w : Fin 2 → Fin d) : MemLp (Z w) 2 volume ∧
      bochnerL2Norm volume (Z w) ≤ ‖z (w 0) (w 1)‖ :=
    κ.convolution_right_memLp_norm_le hκ hunit _
  have he (x : SpatialCoordinates d) (hx : x ∈ K) (w : Fin 2 → Fin d) :
      tensorCoordinates (iteratedFDeriv ℝ 2 U x) w = Z w x := by
    change iteratedFDeriv ℝ 2 U x (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i)) = _
    have hvec : (fun i => EuclideanSpace.basisFun (Fin d) ℝ (w i)) =
        ![EuclideanSpace.basisFun (Fin d) ℝ (w 0),EuclideanSpace.basisFun (Fin d) ℝ (w 1)] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec]
    exact (hv (w 0)).second_tensor_convolution_local (hz (w 0) (w 1)) κ x (hinside x hx)
  have hp : (fun x => ‖iteratedFDeriv ℝ 2 U x‖^2) ≤ᵐ[volume.restrict K]
      (fun x => (tensorCoordinateBound d 2)^2 * ∑ w : Fin 2 → Fin d, (Z w x)^2) := by
    filter_upwards [ae_restrict_mem hK] with x hx
    simpa only [he x hx] using tensor_norm_sq_le_coordinate_sum (iteratedFDeriv ℝ 2 U x)
  have hi : IntegrableOn (fun x => (tensorCoordinateBound d 2)^2 *
      ∑ w : Fin 2 → Fin d, (Z w x)^2) K :=
    (integrable_finsetSum _ (fun w _ => ((hm w).1.restrict K).integrable_sq)).const_mul _
  have hc : Continuous (fun x => ‖iteratedFDeriv ℝ 2 U x‖^2) :=
    ((κ.smooth_convolution u).continuous_iteratedFDeriv (by simp)).norm.pow 2
  have hleft : IntegrableOn (fun x => ‖iteratedFDeriv ℝ 2 U x‖^2) K :=
    hi.mono' hc.aestronglyMeasurable (by
      filter_upwards [hp] with x hx
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (‖iteratedFDeriv ℝ 2 U x‖))] using hx)
  refine ⟨hleft, (integral_mono_ae hleft hi hp).trans ?_⟩
  rw [integral_const_mul,integral_finsetSum _ (fun w _ => ((hm w).1.restrict K).integrable_sq)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro w _
  calc
    _ ≤ ∫ x, (Z w x)^2 := setIntegral_le_integral (hm w).1.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
    _ = (bochnerL2Norm volume (Z w))^2 := integral_sq_eq_bochnerL2Norm_sq (hm w).1
    _ ≤ ‖z (w 0) (w 1)‖^2 :=
      (sq_le_sq₀ (bochnerL2Norm_nonneg _) (norm_nonneg _)).mpr (hm w).2

theorem WeakSobolevJet.mollified_hessian_energy_le (hS : MeasurableSet S) (hK : MeasurableSet K)
    (u : WeakSobolevJet d 2 (volume.restrict S) S)
    (κ : SpatialTest (univ : Set (SpatialCoordinates d)))
    (hκ : ∀ x, 0 ≤ κ.value x) (hunit : ∫ x, κ.value x = 1)
    (hinside : ∀ x ∈ K, ∀ y ∈ tsupport κ.value, x-y ∈ S) :
    let U := zeroExtendLp hS (WeakSobolevJet.value u) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] κ.value
    IntegrableOn (fun x => ‖iteratedFDeriv ℝ 2 U x‖^2) K ∧
      (∫ x in K, ‖iteratedFDeriv ℝ 2 U x‖^2) ≤
        (tensorCoordinateBound d 2)^2*(d:ℝ)^2*‖WeakSobolevJet.field 2 u‖^2 := by
  let v := fun i => zeroExtendLp hS (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))
  let z := fun i j => zeroExtendLp hS (derivativeComponent (Sym.cons j (Sym.cons i Sym.nil)) (WeakSobolevJet.field 2 u))
  have hb := Carleman.mollified_hessian_energy_le hK (zeroExtendLp hS (WeakSobolevJet.value u)) v z
    (fun i => (WeakSobolevJet.field_weak_derivative u (0 : Fin 2) Sym.nil i).zeroExtend hS)
    (fun i j => (WeakSobolevJet.field_weak_derivative u (1 : Fin 2) (Sym.cons i Sym.nil) j).zeroExtend hS)
    κ hκ hunit hinside
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hn (i j : Fin d) : ‖z i j‖ ≤ ‖WeakSobolevJet.field 2 u‖ := by
    dsimp only [z]
    rw [zeroExtendLp_norm]
    exact derivativeComponent_norm_le _ _
  calc
    _ ≤ (tensorCoordinateBound d 2)^2 * ∑ _w : Fin 2 → Fin d, ‖WeakSobolevJet.field 2 u‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun w _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hn (w 0) (w 1))
    _ = _ := by simp; ring

end Carleman
