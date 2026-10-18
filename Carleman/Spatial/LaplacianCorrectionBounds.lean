module

public import Carleman.Spatial.DirichletOperatorProduct
public import Carleman.Weights.IntrinsicConjugation

/-! Uniform relative coefficient bounds for the actual weak Laplacian
product correction, before all weight parameters and states. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)}

theorem derivativeComponent_weighted_norm_le {k : ℕ}
    {ν : Measure (SpatialCoordinates d)} (σ : BoundedMultiplier ν)
    (α : Sym (Fin d) k) (u : Lp (DerivativeFiber d k) 2 ν) :
    σ.seminorm (derivativeComponent α u) ≤ σ.seminorm u := by
  change ‖σ.map (derivativeComponent α u)‖ ≤ ‖σ.map u‖
  rw [← derivativeComponent_multiplier]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [derivativeComponent_ae α (σ.map u)] with x hx
  rw [hx]
  exact PiLp.norm_apply_le _ _

theorem WeakSobolevJet.heat_parameterNorm (q : ℝ)
    (σ : BoundedMultiplier (volume.restrict S))
    (u : WeakSobolevJet d 1 (volume.restrict S) S) :
    parameterNorm q σ u = q*σ.seminorm (value u)+σ.seminorm (field 1 u) := by
  unfold parameterNorm
  rw [Fin.sum_univ_two]
  norm_num only [Fin.val_zero,Fin.val_one,Nat.sub_zero,Nat.sub_self,pow_one,pow_zero,one_mul]
  rw [weighted_zero_eq]

theorem smoothLaplacianCorrection_norm_le (hS : IsOpen S)
    (σ : BoundedMultiplier (volume.restrict S)) (hσ : BoundedSmoothOn σ.value S)
    {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hb : ∀ i : Fin d, ∀ x ∈ S,
      |wordDerivative [i] σ.value x| ≤ C*q*|σ.value x| ∧
      |wordDerivative [i,i] σ.value x| ≤ C*q^2*|σ.value x|)
    (u : WeakSobolevJet d 1 (volume.restrict S) S) :
    ‖smoothLaplacianCorrection hS σ hσ u‖ ≤
      (2*(d:ℝ)*C)*q*WeakSobolevJet.parameterNorm q σ u := by
  have hν : ∀ᵐ x ∂volume.restrict S, x ∈ S := ae_restrict_mem hS.measurableSet
  have hfirst (i : Fin d) :
      ‖(intrinsicWordMultiplier hS hν hσ [i]).map
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))‖ ≤
      C*q*σ.seminorm (WeakSobolevJet.field 1 u) := by
    exact ((intrinsicWordMultiplier hS hν hσ [i]).seminorm_le_of_weight_le σ (C*q)
      (hν.mono fun x hx => (hb i x hx).1) _).trans
      (mul_le_mul_of_nonneg_left (derivativeComponent_weighted_norm_le σ _ _) (mul_nonneg hC hq))
  have hsecond (i : Fin d) :
      ‖(intrinsicWordMultiplier hS hν hσ [i,i]).map (WeakSobolevJet.value u)‖ ≤
      C*q^2*σ.seminorm (WeakSobolevJet.value u) :=
    (intrinsicWordMultiplier hS hν hσ [i,i]).seminorm_le_of_weight_le σ (C*q^2)
      (hν.mono fun x hx => (hb i x hx).2) _
  have ht (i : Fin d) :
      ‖(2:ℝ) • (intrinsicWordMultiplier hS hν hσ [i]).map
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))+
        (intrinsicWordMultiplier hS hν hσ [i,i]).map (WeakSobolevJet.value u)‖ ≤
      2*C*q*WeakSobolevJet.parameterNorm q σ u := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2),
      WeakSobolevJet.heat_parameterNorm]
    have ha := hfirst i
    have hb' := hsecond i
    have hz : 0 ≤ C*q^2*σ.seminorm (WeakSobolevJet.value u) :=
      mul_nonneg (mul_nonneg hC (sq_nonneg q)) (apply_nonneg _ _)
    nlinarith only [ha,hb',hz]
  calc
    _ ≤ ∑ i : Fin d, ‖(2:ℝ) • (intrinsicWordMultiplier hS hν hσ [i]).map
        (derivativeComponent (Sym.cons i Sym.nil) (WeakSobolevJet.field 1 u))+
        (intrinsicWordMultiplier hS hν hσ [i,i]).map (WeakSobolevJet.value u)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, 2*C*q*WeakSobolevJet.parameterNorm q σ u :=
      Finset.sum_le_sum fun i _ => ht i
    _ = _ := by simp; ring

theorem allowed_laplacian_correction_uniform (hS : IsOpen S) (hb : Bornology.IsBounded S)
    (ρ : SpatialProfile (volume.restrict S)) (hρ : SmoothOnClosure ρ.value S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : TimeWeight) (τ t η : ℝ) (hη : |η|=1)
      (u : WeakSobolevJet d 1 (volume.restrict S) S),
      ‖smoothLaplacianCorrection hS ((ρ.scaled η).multiplier w τ t)
        (allowed_multiplier_boundedSmooth hS hb ρ hρ w τ t η hη) u‖ ≤
        C*w.q t*WeakSobolevJet.parameterNorm (w.q t) ((ρ.scaled η).multiplier w τ t) u := by
  obtain ⟨B,hB,hcoeff⟩ := (hρ.boundedSmoothOn hb).allowedWeight_word_uniform hS 2
  refine ⟨2*(d:ℝ)*B+1,by positivity,?_⟩
  intro w τ t η hη u
  let σ := (ρ.scaled η).multiplier w τ t
  have he : σ.value = (fun x => w.q t^τ*Real.exp (w.q t*(η*ρ.value x))) := by
    funext x
    change w.q t^τ*Real.exp ((η*ρ.value x)*w.q t) = _
    rw [mul_comm (η*ρ.value x)]
  have hc (i : Fin d) (x : SpatialCoordinates d) (hx : x ∈ S) :
      |wordDerivative [i] σ.value x| ≤ B*w.q t*|σ.value x| ∧
      |wordDerivative [i,i] σ.value x| ≤ B*w.q t^2*|σ.value x| := by
    rw [he,abs_of_pos (mul_pos (Real.rpow_pos_of_pos (w.pos t) _) (Real.exp_pos _))]
    constructor
    · simpa using hcoeff (w.q t) (w.lower t) τ η hη [i] (by simp) x hx
    · simpa using hcoeff (w.q t) (w.lower t) τ η hη [i,i] (by simp) x hx
  exact (smoothLaplacianCorrection_norm_le hS σ
    (allowed_multiplier_boundedSmooth hS hb ρ hρ w τ t η hη) (w.nonneg t) hB.le hc u).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 2*(d:ℝ)*B ≤ 2*(d:ℝ)*B+1) (w.nonneg t))
      (WeakSobolevJet.parameterNorm_nonneg (w.nonneg t) _ _))

end Carleman
