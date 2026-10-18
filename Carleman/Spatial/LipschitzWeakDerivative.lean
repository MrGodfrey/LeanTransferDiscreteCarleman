module

public import Carleman.Spatial.SobolevJet
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! A Lipschitz representative and its actual a.e. line derivative satisfy
the original distributional identity against every spatial test function. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

/-- This does not assume the integration-by-parts identity: it follows from
mathlib's difference-quotient theorem for globally Lipschitz functions. -/
theorem weakSpatialDerivative_of_lipschitz {f : SpatialCoordinates d → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (e : SpatialCoordinates d)
    (u v : Lp ℝ 2 (volume.restrict S))
    (hu : u =ᵐ[volume.restrict S] f)
    (hv : v =ᵐ[volume.restrict S] (fun x => lineDeriv ℝ f x e)) :
    IsWeakSpatialDerivative (volume.restrict S) S e u v := by
  rw [IsWeakSpatialDerivative.iff_integral]
  intro φ
  obtain ⟨D,hφ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.compact φ.smooth (by simp)
  have hi := hf.integral_lineDeriv_mul_eq (μ := volume) hφ φ.compact e
  have hd (x : SpatialCoordinates d) : lineDeriv ℝ φ.value x (-e) = -(fderiv ℝ φ.value x e) := by
    rw [((φ.smooth.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv,map_neg]
  simp_rw [hd,neg_mul] at hi
  rw [integral_neg] at hi
  have huI : (∫ x, fderiv ℝ φ.value x e*u x ∂(volume.restrict S)) =
      ∫ x, fderiv ℝ φ.value x e*f x := by
    calc
      _ = ∫ x in S, fderiv ℝ φ.value x e*f x := integral_congr_ae (hu.mono fun _ hx => by rw [hx])
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have hn : x ∉ tsupport φ.value := fun hh => hx (φ.support hh)
        rw [fderiv_of_notMem_tsupport ℝ hn,zero_apply,zero_mul])
  have hvI : (∫ x, φ.value x*v x ∂(volume.restrict S)) =
      ∫ x, lineDeriv ℝ f x e*φ.value x := by
    calc
      _ = ∫ x in S, lineDeriv ℝ f x e*φ.value x := integral_congr_ae (hv.mono fun _ hx => by rw [hx,mul_comm])
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (φ.support hh)),mul_zero])
  rw [huI,hvI]
  linarith

end Carleman
