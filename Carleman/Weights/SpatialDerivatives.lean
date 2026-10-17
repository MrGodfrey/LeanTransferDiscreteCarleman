module

public import Carleman.Spatial.AllowedWeight
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Spatial derivatives of the actual exponential weights

The derivative is mathlib's iterated Fréchet derivative within the spatial
set. The input bounds are on the fixed profile rho, never on sigma itself.
All constants are independent of time, qmax, tau and the time grid.
-/
@[expose] public noncomputable section
open Set
open scoped BigOperators ContDiff
namespace Carleman
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every derivative of exp at a real point has operator norm exp at that point. -/
theorem norm_iteratedFDeriv_exp (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n Real.exp x‖ = Real.exp x := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have he := congrFun (iteratedDeriv_exp_const_mul n 1) x
  simp only [one_mul, one_pow] at he
  rw [he, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]

/-- Bound from finitely many derivatives of the fixed spatial profile.
This is valid for either sign of rho, by replacing rho with -rho. -/
theorem norm_iteratedFDerivWithin_exp_profile {ρ : E → ℝ} {S : Set E}
    {n : ℕ} (hρ : ContDiffOn ℝ n ρ S) (hS : UniqueDiffOn ℝ S)
    {x : E} (hx : x ∈ S) {q M : ℝ} (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hb : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i ρ S x‖ ≤ M) :
    ‖iteratedFDerivWithin ℝ n (fun y => Real.exp (q * ρ y)) S x‖ ≤
      ((n.factorial : ℝ) * M ^ n) * q ^ n * Real.exp (q * ρ x) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (q • ρ) S x‖ ≤ (q*M)^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_const_smul_apply (hρ.of_le (by exact_mod_cast hin) x hx) hS hx,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
    exact (mul_le_mul_of_nonneg_left (hb i hi hin) hq0).trans
      (le_self_pow₀ (one_le_mul_of_one_le_of_one_le hq hM) (by omega))
  have he := norm_iteratedFDerivWithin_comp_le
    (Real.contDiff_exp.contDiffOn)
    (hρ.const_smul q) le_rfl uniqueDiffOn_univ hS
    (Set.mapsTo_univ _ _) hx
    (C := Real.exp (q*ρ x)) (D := q*M)
    (fun i _ => by simp only [iteratedFDerivWithin_univ, smul_eq_mul,
      norm_iteratedFDeriv_exp]; exact le_rfl) hD
  simp only [Function.comp_def, smul_eq_mul] at he
  calc
    _ ≤ (n.factorial : ℝ) * Real.exp (q * ρ x) * (q*M)^n := he
    _ = _ := by rw [mul_pow]; ring

/-- The q^tau prefactor is constant in space; no bound on tau is needed here. -/
theorem norm_iteratedFDerivWithin_allowedWeight {ρ : E → ℝ} {S : Set E}
    {n : ℕ} (hρ : ContDiffOn ℝ n ρ S) (hS : UniqueDiffOn ℝ S)
    {x : E} (hx : x ∈ S) {q M : ℝ} (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hb : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i ρ S x‖ ≤ M) (τ : ℝ) :
    ‖iteratedFDerivWithin ℝ n (fun y => q^τ * Real.exp (q * ρ y)) S x‖ ≤
      ((n.factorial : ℝ) * M^n) * q^n * (q^τ * Real.exp (q * ρ x)) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hc : ContDiffOn ℝ n (fun y => Real.exp (q * ρ y)) S :=
    (hρ.const_smul q).exp
  change ‖iteratedFDerivWithin ℝ n (q^τ • (fun y => Real.exp (q * ρ y))) S x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply (hc x hx) hS hx, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hq0 _)]
  have hh := mul_le_mul_of_nonneg_left
    (norm_iteratedFDerivWithin_exp_profile hρ hS hx hq hM hb) (Real.rpow_nonneg hq0 τ)
  convert hh using 1; ring

/-- Compactness supplies a single bound for the finite family of rho derivatives.
The set may be a closed spatial domain; only its genuine UniqueDiffOn property
is used, and no derivative bound for the varying exponential is assumed. -/
theorem exists_profile_derivative_bound {ρ : E → ℝ} {S : Set E} {n : ℕ}
    (hρ : ContDiffOn ℝ n ρ S) (hS : UniqueDiffOn ℝ S) (hcompact : IsCompact S) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i, i ≤ n → ∀ x ∈ S,
      ‖iteratedFDerivWithin ℝ i ρ S x‖ ≤ M := by
  have hb : ∀ i : Fin (n+1), ∃ C : ℝ, ∀ x ∈ S,
      ‖iteratedFDerivWithin ℝ i.val ρ S x‖ ≤ C := by
    intro i
    exact hcompact.exists_bound_of_continuousOn
      (hρ.continuousOn_iteratedFDerivWithin (by exact_mod_cast Nat.le_of_lt_succ i.isLt) hS)
  choose C hC using hb
  refine ⟨1 + ∑ i, max 0 (C i), ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => le_max_left _ _)
  · intro i hi x hx
    have hs := Finset.single_le_sum (s := Finset.univ) (f := fun k => max 0 (C k))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ (⟨i, by omega⟩ : Fin (n+1)))
    have hc := hC ⟨i, by omega⟩ x hx
    exact hc.trans ((le_max_right _ _).trans (hs.trans (by linarith)))

/-- Uniform in all orders up to n and in both signs of the exponential.
The sign is represented by eta=1 or eta=-1; tau is unrestricted. -/
theorem allowedWeight_spatial_derivatives_uniform {ρ : E → ℝ} {S : Set E} {n : ℕ}
    (hρ : ContDiffOn ℝ n ρ S) (hS : UniqueDiffOn ℝ S) (hcompact : IsCompact S) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 1 ≤ q → ∀ τ : ℝ, ∀ eta : ℝ, |eta| = 1 →
      ∀ j : ℕ, j ≤ n → ∀ x ∈ S,
        ‖iteratedFDerivWithin ℝ j (fun y => q^τ * Real.exp (q * (eta*ρ y))) S x‖ ≤
          C * q^j * (q^τ * Real.exp (q * (eta*ρ x))) := by
  obtain ⟨M, hM, hb⟩ := exists_profile_derivative_bound hρ hS hcompact
  refine ⟨(n.factorial : ℝ) * M^n, by positivity, ?_⟩
  intro q hq τ eta heta j hj x hx
  have hrj : ContDiffOn ℝ j ρ S := hρ.of_le (by exact_mod_cast hj)
  have hb' : ∀ i, 1 ≤ i → i ≤ j →
      ‖iteratedFDerivWithin ℝ i (eta • ρ) S x‖ ≤ M := by
    intro i _ hij
    rw [iteratedFDerivWithin_const_smul_apply
      (hρ.of_le (by exact_mod_cast hij.trans hj) x hx) hS hx,
      norm_smul, Real.norm_eq_abs, heta, one_mul]
    exact hb i (hij.trans hj) x hx
  have hh := norm_iteratedFDerivWithin_allowedWeight (hrj.const_smul eta) hS hx hq hM hb' τ
  simp only [smul_eq_mul] at hh
  have hfac : (j.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hj
  have hp : M^j ≤ M^n := pow_le_pow_right₀ hM hj
  exact hh.trans (by gcongr)
end Carleman

@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman.SpatialProfile
variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] {ν : Measure E} {S : Set E}

/-- Realize a fixed continuous profile on a compact domain in the actual
weighted-L² multiplier interface. Restriction of volume to the domain supplies
hν; no global measurability or boundedness outside the domain is required. -/
def ofContinuousOn (ρ : E → ℝ) (hc : ContinuousOn ρ S) (hS : IsCompact S)
    (hν : ∀ᵐ x ∂ν, x ∈ S) : SpatialProfile ν where
  value := ρ
  measurable := by
    have hm := hc.aestronglyMeasurable (μ := ν) hS.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hν] at hm
  bound := max 0 (hS.exists_bound_of_continuousOn hc).choose
  bound_nonneg := le_max_left _ _
  bounded := by
    filter_upwards [hν] with x hx
    have hb : |ρ x| ≤ (hS.exists_bound_of_continuousOn hc).choose := by
      simpa only [Real.norm_eq_abs] using (hS.exists_bound_of_continuousOn hc).choose_spec x hx
    exact hb.trans (le_max_right _ _)

theorem ofContinuousOn_value (ρ : E → ℝ) (hc : ContinuousOn ρ S) (hS : IsCompact S)
    (hν : ∀ᵐ x ∂ν, x ∈ S) (x : E) : (ofContinuousOn ρ hc hS hν).value x = ρ x := rfl

/-- The smooth-profile realization uses precisely the same exponential as the
spatial derivative theorem, not a separately chosen weight function. -/
theorem ofContinuousOn_multiplier (ρ : E → ℝ) (hc : ContinuousOn ρ S) (hS : IsCompact S)
    (hν : ∀ᵐ x ∂ν, x ∈ S) (w : TimeWeight) (τ t : ℝ) (x : E) :
    ((ofContinuousOn ρ hc hS hν).multiplier w τ t).value x =
      w.q t ^ τ * Real.exp (w.q t * ρ x) := by
  simp only [multiplier, ofContinuousOn, mul_comm (ρ x) (w.q t)]
end Carleman.SpatialProfile
