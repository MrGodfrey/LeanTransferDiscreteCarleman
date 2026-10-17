module

public import Carleman.Spatial.ParameterConjugation
public import Carleman.Spatial.AllowedWeight

/-! Uniform two-sided spatial conjugation for the original exponential weights.
All states are genuine weak Sobolev jets. A2 supplies the weighted state;
no final graph estimate or parameter interpolation is assumed here. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Carleman
variable {d n : ℕ} {ν : Measure (SpatialCoordinates d)}
  [IsFiniteMeasureOnCompacts ν] [IsLocallyFiniteMeasure ν]
  {S U K : Set (SpatialCoordinates d)} (hS : IsOpen S) (hU : IsOpen U)
  (hK : IsCompact K) (hKU : K ⊆ U) (hSU : S ⊆ U)
  (hνS : ∀ᵐ x ∂ν, x ∈ S) (hνK : ∀ᵐ x ∂ν, x ∈ K)

include hS hU hK hKU hSU hνS hνK
/-- Actual smooth multiplication plus its proved derivative estimates controls
all spatial orders. This helper retains its exact coefficient premise. -/
theorem smooth_parameterNorm_bound {f : SpatialCoordinates d → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (w outer base : BoundedMultiplier ν) (hw : w.value=f)
    {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hb : ∀ l : List (Fin d), l.length ≤ n → ∀ x ∈ K,
      |outer.value x*wordDerivative l f x| ≤ C*q^l.length*|base.value x|)
    (u v : WeakSobolevJet d n ν S)
    (hv : WeakSobolevJet.value v = w.map (WeakSobolevJet.value u)) :
    WeakSobolevJet.parameterNorm q outer v ≤
      WeakSobolevJet.leibnizConstant d n*C*WeakSobolevJet.parameterNorm q base u := by
  apply WeakSobolevJet.parameterNorm_leibniz_bound
    (smoothWordMultiplier hU hK hKU hνK hf) outer base hq hC
  · intro l hl
    exact hνK.mono fun x hx => hb l hl x hx
  · exact fun l hl => weak_leibniz_smooth hU hK hKU hνK hf hS hSU hνS w hw u v hv l hl

/-- Both directions, uniformly before q, tau, either sign and all weak states.
The coefficient bounds are derived from the fixed smooth profile. -/
theorem allowedWeight_parameterNorm_uniform {ρ : SpatialCoordinates d → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ U) :
    ∃ D : ℝ, 0 < D ∧ ∀ q : ℝ, 1 ≤ q → ∀ τ eta : ℝ, |eta|=1 →
      ∀ w : BoundedMultiplier ν,
        w.value = (fun x => q^τ*Real.exp (q*(eta*ρ x))) →
      ∀ u v : WeakSobolevJet d n ν S,
        WeakSobolevJet.value v = w.map (WeakSobolevJet.value u) →
        WeakSobolevJet.parameterNorm q BoundedMultiplier.one v ≤
          D*WeakSobolevJet.parameterNorm q w u ∧
        WeakSobolevJet.parameterNorm q w u ≤
          D*WeakSobolevJet.parameterNorm q BoundedMultiplier.one v := by
  obtain ⟨C, hC, hb⟩ := allowedWeight_word_derivatives_uniform hU hK hKU hρ n
  refine ⟨WeakSobolevJet.leibnizConstant d n*C,
    mul_pos WeakSobolevJet.leibnizConstant_pos hC, ?_⟩
  intro q hq τ eta heta w hw u v hv
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hf : ContDiffOn ℝ ∞ (fun x => q^τ*Real.exp (q*(eta*ρ x))) U := by
    simpa only [smul_eq_mul] using (((hρ.const_smul eta).const_smul q).exp).const_smul (q^τ)
  have hi : ContDiffOn ℝ ∞ (fun x => q^(-τ)*Real.exp (q*((-eta)*ρ x))) U := by
    simpa only [smul_eq_mul] using (((hρ.const_smul (-eta)).const_smul q).exp).const_smul (q^(-τ))
  let ξ := smoothWordMultiplier hU hK hKU hνK hi []
  have hξ : ξ.value = (fun x => q^(-τ)*Real.exp (q*((-eta)*ρ x))) := by
    change wordDerivative [] _ = _
    exact wordDerivative_nil _
  have hinv (x : SpatialCoordinates d) : w.value x * ξ.value x = 1 := by
    rw [hw, hξ, Real.rpow_neg hq0.le]
    dsimp only
    have he : q*(-eta*ρ x) = -(q*(eta*ρ x)) := by ring
    rw [he, Real.exp_neg]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hq0 τ)]
  have hξv : WeakSobolevJet.value u = ξ.map (WeakSobolevJet.value v) := by
    rw [hv]
    exact (ξ.map_inverse w (Filter.Eventually.of_forall fun x => by rw [mul_comm]; exact hinv x) _).symm
  constructor
  · apply smooth_parameterNorm_bound hS hU hK hKU hSU hνS hνK hf w
      BoundedMultiplier.one w hw hq0.le hC.le _ u v hv
    intro l hl x hx
    simp only [BoundedMultiplier.one, one_mul, hw]
    rw [abs_of_pos (mul_pos (Real.rpow_pos_of_pos hq0 _) (Real.exp_pos _))]
    exact hb q hq τ eta heta l hl x hx
  · apply smooth_parameterNorm_bound hS hU hK hKU hSU hνS hνK hi ξ w
      BoundedMultiplier.one hξ hq0.le hC.le _ v u hξv
    intro l hl x hx
    have hh := hb q hq (-τ) (-eta) (by simpa using heta) l hl x hx
    have hwpos : 0 < w.value x := by rw [hw]; positivity
    rw [abs_mul, abs_of_pos hwpos]
    have hh' := mul_le_mul_of_nonneg_left hh hwpos.le
    change w.value x*|wordDerivative l _ x| ≤ C*q^l.length*|1|
    rw [abs_one, mul_one]
    calc
      _ ≤ w.value x*(C*q^l.length*ξ.value x) := by simpa only [hξ] using hh'
      _ = C*q^l.length := by rw [mul_left_comm, hinv, mul_one]

/-- The same two-sided comparison for the actual square-sum N norm. -/
theorem allowedWeight_weightedNorm_uniform {ρ : SpatialCoordinates d → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ U) :
    ∃ D : ℝ, 0 < D ∧ ∀ q : ℝ, 1 ≤ q → ∀ τ eta : ℝ, |eta|=1 →
      ∀ w : BoundedMultiplier ν,
        w.value = (fun x => q^τ*Real.exp (q*(eta*ρ x))) →
      ∀ u v : WeakSobolevJet d n ν S,
        WeakSobolevJet.value v = w.map (WeakSobolevJet.value u) →
        WeakSobolevJet.weightedNorm q BoundedMultiplier.one v ≤
          D*WeakSobolevJet.weightedNorm q w u ∧
        WeakSobolevJet.weightedNorm q w u ≤
          D*WeakSobolevJet.weightedNorm q BoundedMultiplier.one v := by
  obtain ⟨D, hD, hb⟩ := allowedWeight_parameterNorm_uniform (n := n) hS hU hK hKU hSU hνS hνK hρ
  refine ⟨D*(n+1), by positivity, ?_⟩
  intro q hq τ eta heta w hw u v hv
  obtain ⟨h1, h2⟩ := hb q hq τ eta heta w hw u v hv
  have hq0 := zero_le_one.trans hq
  constructor
  · exact (WeakSobolevJet.weightedNorm_le_parameterNorm hq0 _ _).trans
      (h1.trans (by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left
          (WeakSobolevJet.parameterNorm_le_weightedNorm hq0 w u) hD.le))
  · exact (WeakSobolevJet.weightedNorm_le_parameterNorm hq0 _ _).trans
      (h2.trans (by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left
          (WeakSobolevJet.parameterNorm_le_weightedNorm hq0 BoundedMultiplier.one v) hD.le))
end Carleman
