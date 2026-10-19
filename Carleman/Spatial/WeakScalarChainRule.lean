module

public import Carleman.Spatial.L2BoundedMultiplierLimit
public import Carleman.Spatial.WeakDerivativeStrongLimit
public import Carleman.Spatial.StrongMollifierLimit
public import Mathlib.Analysis.Calculus.MeanValue

/-! The actual scalar C¹ chain rule for full-space weak L² derivatives.
The proof uses the original mollifications and genuine strong L² limits. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology Convolution NNReal
namespace Carleman

theorem l2_lipschitz_comp_error_tendsto {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {η : ℝ → ℝ} {M : ℝ≥0} (hη : LipschitzWith M η) (h0 : η 0=0)
    {f : Ω → ℝ} {F : ℕ → Ω → ℝ} (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (ht : Tendsto (fun n => bochnerL2Norm ν (fun x => F n x-f x)) atTop (𝓝 0)) :
    Tendsto (fun n => bochnerL2Norm ν (fun x => η (F n x)-η (f x))) atTop (𝓝 0) := by
  have hb (n : ℕ) : bochnerL2Norm ν (fun x => η (F n x)-η (f x)) ≤
      (M:ℝ)*bochnerL2Norm ν (fun x => F n x-f x) := by
    have hleft := (hη.comp_memLp h0 (hF n)).sub (hη.comp_memLp h0 hf)
    have hright := (hF n).sub hf
    change bochnerL2Norm ν ((η ∘ F n)-(η ∘ f)) ≤ (M:ℝ)*bochnerL2Norm ν (F n-f)
    rw [bochnerL2Norm_eq _ hleft,bochnerL2Norm_eq _ hright]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hleft.coeFn_toLp,hright.coeFn_toLp] with x hx hy
    rw [hx,hy]
    exact hη.norm_sub_le _ _
  apply squeeze_zero (fun n => bochnerL2Norm_nonneg _) hb
  simpa only [mul_zero] using ht.const_mul (M:ℝ)

theorem IsWeakSpatialDerivative.scalar_chain_rule {d : ℕ} {e : SpatialCoordinates d}
    {u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d))}
    (hw : IsWeakSpatialDerivative volume univ e u v)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) {M : ℝ≥0} (hL : LipschitzWith M η) (h0 : η 0=0)
    (U V : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hU : U =ᵐ[volume] (fun x => η (u x)))
    (hV : V =ᵐ[volume] (fun x => deriv η (u x)*v x)) :
    IsWeakSpatialDerivative volume univ e U V := by
  let F := fun n => u ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (spatialMollifier d n).value
  let G := fun n => v ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] (spatialMollifier d n).value
  have hFs (n : ℕ) : ContDiff ℝ 1 (F n) := ((spatialMollifier d n).smooth_convolution u).of_le (by simp)
  have hFm (n : ℕ) : MemLp (F n) 2 volume :=
    ((spatialMollifier d n).convolution_right_memLp_norm_le
      (spatialMollifier_nonneg n) (spatialMollifier_integral n) u).1
  have hGm (n : ℕ) : MemLp (G n) 2 volume :=
    ((spatialMollifier d n).convolution_right_memLp_norm_le
      (spatialMollifier_nonneg n) (spatialMollifier_integral n) v).1
  have hdc : Continuous (deriv η) := hη.continuous_deriv (by simp)
  have hbd (t : ℝ) : |deriv η t| ≤ (M:ℝ) := norm_deriv_le_of_lipschitz hL
  have hA (n : ℕ) : AEStronglyMeasurable (fun x => deriv η (F n x)) volume :=
    (hdc.comp (hFs n).continuous).aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun x => deriv η (u x)) volume :=
    hdc.comp_aestronglyMeasurable (Lp.memLp u).aestronglyMeasurable
  have hUf : MemLp (fun x => η (u x)) 2 volume := hL.comp_memLp h0 (Lp.memLp u)
  have hVf : MemLp (fun x => deriv η (u x)*v x) 2 volume :=
    memLp_mul_of_ae_bound hb (Lp.memLp v) M.property (Eventually.of_forall fun x => hbd _)
  have hUn (n : ℕ) : MemLp (fun x => η (F n x)) 2 volume := hL.comp_memLp h0 (hFm n)
  have hVn (n : ℕ) : MemLp (fun x => deriv η (F n x)*G n x) 2 volume :=
    memLp_mul_of_ae_bound (hA n) (hGm n) M.property (Eventually.of_forall fun x => hbd _)
  have hchain (n : ℕ) (x : SpatialCoordinates d) :
      fderiv ℝ (fun y => η (F n y)) x e=deriv η (F n x)*G n x := by
    have h := ((hη.differentiable (by simp)) (F n x)).hasDerivAt.comp_hasFDerivAt x
      (((hFs n).differentiable (by simp)) x).hasFDerivAt
    change fderiv ℝ (η ∘ F n) x e= _
    rw [h.fderiv,smul_apply,smul_eq_mul]
    rw [hw.fderiv_convolution]
  have hweak (n : ℕ) : IsWeakSpatialDerivative volume univ e
      ((hUn n).toLp (fun x => η (F n x))) ((hVn n).toLp (fun x => deriv η (F n x)*G n x)) := by
    apply weakSpatialDerivative_of_contDiff (hη.comp (hFs n)) e _ _ (hUn n).coeFn_toLp
    filter_upwards [(hVn n).coeFn_toLp] with x hx
    exact hx.trans (hchain n x).symm
  have hcomp := l2_lipschitz_comp_error_tendsto hL h0 (Lp.memLp u) hFm (spatialMollifier_L2_error_tendsto u)
  have hgrad := l2_bounded_multiplier_strong_tendsto hA hb (Lp.memLp v) hGm M.property
    (fun n => Eventually.of_forall fun x => hbd _) (Eventually.of_forall fun x => hbd _)
    ((spatialMollifier_converges u).mono fun x hx => hdc.continuousAt.tendsto.comp hx)
    (spatialMollifier_L2_error_tendsto v)
  have hresult := IsWeakSpatialDerivative.of_strong_function_limits hUf hVf hUn hVn hweak hcomp hgrad
  have heU : hUf.toLp (fun x => η (u x))=U := Lp.ext (hUf.coeFn_toLp.trans hU.symm)
  have heV : hVf.toLp (fun x => deriv η (u x)*v x)=V := Lp.ext (hVf.coeFn_toLp.trans hV.symm)
  rwa [heU,heV] at hresult

end Carleman
