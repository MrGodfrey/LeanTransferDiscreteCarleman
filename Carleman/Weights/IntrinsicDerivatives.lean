module

public import Carleman.Weights.IntrinsicSmoothClosure

/-! Uniform relative bounds for actual interior derivatives of the allowed
weights. Neither derivatives on the boundary nor an exterior extension occur. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace Carleman
variable {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
  {ρ : SpatialCoordinates d → ℝ} (hρ : BoundedSmoothOn ρ S)

include hS hρ
theorem BoundedSmoothOn.allowedWeight_actual_uniform (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 1 ≤ q → ∀ τ eta : ℝ, |eta| = 1 →
      ∀ j, j ≤ n → ∀ x ∈ S,
        ‖iteratedFDeriv ℝ j (fun y => q^τ * Real.exp (q*(eta*ρ y))) x‖ ≤
          C*q^j*(q^τ*Real.exp (q*(eta*ρ x))) := by
  obtain ⟨M, hM, hb⟩ := hρ.2 n
  refine ⟨(n.factorial : ℝ)*M^n, by positivity, ?_⟩
  intro q hq τ eta heta j hj x hx
  have hbound : ∀ i, 1 ≤ i → i ≤ j →
      ‖iteratedFDerivWithin ℝ i (eta • ρ) S x‖ ≤ M := by
    intro i _ hi
    rw [iteratedFDerivWithin_const_smul_apply
      ((hρ.1.of_le (by simp : (i : ℕ∞ω) ≤ ∞)) x hx) hS.uniqueDiffOn hx,
      norm_smul, Real.norm_eq_abs, heta, one_mul,
      iteratedFDerivWithin_eq_of_mem_nhds (hS.mem_nhds hx)]
    exact hb i (hi.trans hj) x hx
  have he := norm_iteratedFDerivWithin_allowedWeight
    ((hρ.1.of_le (by simp : (j : ℕ∞ω) ≤ ∞)).const_smul eta)
    hS.uniqueDiffOn hx hq hM hbound τ
  simp only [smul_eq_mul] at he
  rw [iteratedFDerivWithin_eq_of_mem_nhds (hS.mem_nhds hx)] at he
  have hfac : (j.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hj
  have hpow := pow_le_pow_right₀ hM hj
  exact he.trans (by gcongr)

theorem BoundedSmoothOn.allowedWeight_word_uniform (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 1 ≤ q → ∀ τ eta : ℝ, |eta| = 1 →
      ∀ l : List (Fin d), l.length ≤ n → ∀ x ∈ S,
        |wordDerivative l (fun y => q^τ * Real.exp (q*(eta*ρ y))) x| ≤
          C*q^l.length*(q^τ*Real.exp (q*(eta*ρ x))) := by
  obtain ⟨C, hC, hb⟩ := hρ.allowedWeight_actual_uniform hS n
  exact ⟨C, hC, fun q hq τ eta heta l hl x hx =>
    (abs_coordinateDerivative_le (wordVector l).get _ x).trans (hb q hq τ eta heta _ hl x hx)⟩

/-- For fixed parameters the coefficients are bounded multipliers. This bound
may depend on q and tau; the relative derivative constant above does not. -/
theorem BoundedSmoothOn.allowedWeight {q : ℝ} (hq : 1 ≤ q)
    (τ eta : ℝ) (heta : |eta| = 1) :
    BoundedSmoothOn (fun x => q^τ*Real.exp (q*(eta*ρ x))) S := by
  refine ⟨?_, fun n => ?_⟩
  · simpa only [smul_eq_mul] using
      (((hρ.1.const_smul eta).const_smul q).exp).const_smul (q^τ)
  · obtain ⟨C, hC, hb⟩ := hρ.allowedWeight_actual_uniform hS n
    obtain ⟨M, hM, hMbound⟩ := hρ.2 0
    refine ⟨max 1 (C*q^n*(q^τ*Real.exp (q*M))), le_max_left _ _, ?_⟩
    intro j hj x hx
    have hρx : |ρ x| ≤ M := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hMbound 0 le_rfl x hx
    have hetaρ : eta*ρ x ≤ M :=
      (le_abs_self _).trans (by simpa [abs_mul, heta] using hρx)
    apply (hb q hq τ eta heta j hj x hx).trans
    apply le_trans _ (le_max_right _ _)
    gcongr

end Carleman
