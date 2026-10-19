module

public import Carleman.Spatial.WeakConvolution
public import Carleman.Spatial.StrongL2NormLimit
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Genuine distributional identities pass to actual L² limits. Smooth
functions supply these identities by integration by parts against every test. -/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Carleman

theorem memLp_toLp_tendsto_of_L2_error {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {f : Ω → ℝ} {F : ℕ → Ω → ℝ} (hf : MemLp f 2 ν) (hF : ∀ n, MemLp (F n) 2 ν)
    (ht : Tendsto (fun n => bochnerL2Norm ν (fun x => F n x-f x)) atTop (𝓝 0)) :
    Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (hf.toLp f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he (n : ℕ) : ‖(hF n).toLp (F n)-hf.toLp f‖ =
      bochnerL2Norm ν (fun x => F n x-f x) := by
    rw [← MemLp.toLp_sub]
    exact (bochnerL2Norm_eq _ ((hF n).sub hf)).symm
  simpa only [he] using ht

theorem IsWeakSpatialDerivative.of_strong_function_limits {d : ℕ}
    {ν : Measure (SpatialCoordinates d)} [IsFiniteMeasureOnCompacts ν]
    {S : Set (SpatialCoordinates d)} {e : SpatialCoordinates d}
    {f g : SpatialCoordinates d → ℝ} {F G : ℕ → SpatialCoordinates d → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hF : ∀ n, MemLp (F n) 2 ν) (hG : ∀ n, MemLp (G n) 2 ν)
    (hw : ∀ n, IsWeakSpatialDerivative ν S e ((hF n).toLp (F n)) ((hG n).toLp (G n)))
    (htf : Tendsto (fun n => bochnerL2Norm ν (fun x => F n x-f x)) atTop (𝓝 0))
    (htg : Tendsto (fun n => bochnerL2Norm ν (fun x => G n x-g x)) atTop (𝓝 0)) :
    IsWeakSpatialDerivative ν S e (hf.toLp f) (hg.toLp g) := by
  intro φ
  have htf' := memLp_toLp_tendsto_of_L2_error hf hF htf
  have htg' := memLp_toLp_tendsto_of_L2_error hg hG htg
  have hc : IsClosed {p : Lp ℝ 2 ν × Lp ℝ 2 ν |
      inner ℝ p.1 (φ.derivativeLp ν e) = -inner ℝ p.2 (φ.toLp ν)} :=
    isClosed_eq (continuous_fst.inner continuous_const) ((continuous_snd.inner continuous_const).neg)
  exact hc.mem_of_tendsto (htf'.prodMk_nhds htg') (Eventually.of_forall fun n => hw n φ)

theorem weakSpatialDerivative_of_contDiff {d : ℕ} {f : SpatialCoordinates d → ℝ}
    (hf : ContDiff ℝ 1 f) (e : SpatialCoordinates d)
    (u v : Lp ℝ 2 (volume : Measure (SpatialCoordinates d)))
    (hu : u =ᵐ[volume] f) (hv : v =ᵐ[volume] (fun x => fderiv ℝ f x e)) :
    IsWeakSpatialDerivative volume univ e u v := by
  apply IsWeakSpatialDerivative.iff_integral.mpr
  intro φ
  have hd : Continuous (fun x => fderiv ℝ f x e) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφd : Continuous (fun x => fderiv ℝ φ.value x e) :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    ((hd.mul φ.smooth.continuous).integrable_of_hasCompactSupport φ.compact.mul_left)
    ((hf.continuous.mul hφd).integrable_of_hasCompactSupport (φ.compact.fderiv_apply ℝ e).mul_left)
    ((hf.continuous.mul φ.smooth.continuous).integrable_of_hasCompactSupport φ.compact.mul_left)
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => φ.smooth.differentiable (by simp) x)
  have hl : (∫ x, fderiv ℝ φ.value x e*u x) = ∫ x, f x*fderiv ℝ φ.value x e :=
    integral_congr_ae (hu.mono fun x hx => by dsimp only at hx ⊢; rw [hx,mul_comm])
  have hr : (∫ x, φ.value x*v x) = ∫ x, fderiv ℝ f x e*φ.value x :=
    integral_congr_ae (hv.mono fun x hx => by dsimp only at hx ⊢; rw [hx,mul_comm])
  rw [hl,hr]
  exact hi

end Carleman
