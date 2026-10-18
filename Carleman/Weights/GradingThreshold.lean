module

public import Carleman.Weights.SpatialComparison

/-! A positive mesh threshold strictly inside the prescribed grading bound. -/
@[expose] public noncomputable section
namespace Carleman

theorem exists_weight_grading_threshold {γ Γ L : ℝ} (hγ : 0 < γ) (hΓ : γ < Γ) (hL : 0 < L) :
    ∃ δ > (0:ℝ), δ ≤ 1 ∧ γ*Real.exp (2*L*δ) ≤ (γ+Γ)/2 ∧ (γ+Γ)/2 < Γ := by
  let R := (γ+Γ)/(2*γ)
  have hR : 1 < R := by
    dsimp only [R]
    apply (lt_div_iff₀ (by positivity : 0 < 2*γ)).mpr
    linarith
  have hl : 0 < Real.log R := Real.log_pos hR
  let δ := min 1 (Real.log R/(2*L))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hl (by positivity))
  refine ⟨δ,hδ,min_le_left _ _,?_,by linarith⟩
  have hd : 2*L*δ ≤ Real.log R := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*L)).mp (min_le_right 1 (Real.log R/(2*L)))
    dsimp only [δ]
    nlinarith
  have he : Real.exp (2*L*δ) ≤ R := by
    calc
      _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr hd
      _ = R := Real.exp_log (zero_lt_one.trans hR)
  calc
    _ ≤ γ*R := mul_le_mul_of_nonneg_left he hγ.le
    _ = (γ+Γ)/2 := by dsimp only [R]; field_simp

end Carleman
