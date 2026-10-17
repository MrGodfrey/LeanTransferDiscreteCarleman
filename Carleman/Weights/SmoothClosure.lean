module

public import Carleman.Weights.CoordinateDerivatives

/-! Smoothness on an open neighborhood of a compact set supplies actual
derivative bounds. This explicitly uses the smooth-neighborhood representation
of C∞(closure Ω); it does not infer that representation from an arbitrary
ContDiffOn assertion on a closed set. No boundary geometry is used here. -/
@[expose] public noncomputable section
open Set
open scoped ContDiff BigOperators
namespace Carleman

def wordVector {d : ℕ} (l : List (Fin d)) : List.Vector (Fin d) l.length := ⟨l, rfl⟩

def wordDerivative {d : ℕ} (l : List (Fin d)) (f : SpatialCoordinates d → ℝ) :
    SpatialCoordinates d → ℝ := coordinateDerivative (wordVector l).get f

theorem wordDerivative_nil {d : ℕ} (f : SpatialCoordinates d → ℝ) : wordDerivative [] f = f := by
  funext x
  exact coordinateDerivative_zero _ f x

theorem wordVector_cons_get {d : ℕ} (l : List (Fin d)) (i : Fin d) :
    (wordVector (i::l)).get = Fin.cons i (wordVector l).get := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · rfl

theorem wordDerivative_cons {d : ℕ} (l : List (Fin d)) (i : Fin d)
    {f : SpatialCoordinates d → ℝ} {x : SpatialCoordinates d} (hf : ContDiffAt ℝ ∞ f x) :
    wordDerivative (i::l) f x = fderiv ℝ (wordDerivative l f) x (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  unfold wordDerivative
  rw [wordVector_cons_get]
  exact coordinateDerivative_cons _ _ (hf.of_le (by simp))

theorem wordDerivative_smooth {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiffOn ℝ ∞ f S) (l : List (Fin d)) :
    ContDiffOn ℝ ∞ (wordDerivative l f) S := by
  intro x hx
  exact ((coordinateTensorEval (wordVector l).get).contDiff.contDiffAt.comp x
    ((hf.contDiffAt (hS.mem_nhds hx)).iteratedFDeriv_right (m := ∞) (by simp))).contDiffWithinAt

/-- Compactness bounds the actual full derivatives of the fixed profile. -/
theorem exists_profile_actual_bound {d : ℕ} {U K : Set (SpatialCoordinates d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {ρ : SpatialCoordinates d → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U) (n : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ j, j ≤ n → ∀ x ∈ K, ‖iteratedFDeriv ℝ j ρ x‖ ≤ M := by
  have hc (j : Fin (n+1)) : ContinuousOn (iteratedFDeriv ℝ j.val ρ) K := by
    intro x hx
    exact ((hρ.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
  choose C hC using fun j : Fin (n+1) => hK.exists_bound_of_continuousOn (hc j)
  refine ⟨1 + ∑ j, max 0 (C j), ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => le_max_left _ _)
  · intro j hj x hx
    have hb := Finset.single_le_sum (s := Finset.univ) (f := fun k => max 0 (C k))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ (⟨j, by omega⟩ : Fin (n+1)))
    exact (hC ⟨j, by omega⟩ x hx).trans ((le_max_right _ _).trans (hb.trans (by linarith)))

/-- All actual coordinate-word derivatives of both allowed weights, uniformly
in q, tau and sign. The constant depends only on the fixed profile and order. -/
theorem allowedWeight_word_derivatives_uniform {d : ℕ} {U K : Set (SpatialCoordinates d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {ρ : SpatialCoordinates d → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 1 ≤ q → ∀ τ eta : ℝ, |eta| = 1 →
      ∀ l : List (Fin d), l.length ≤ n → ∀ x ∈ K,
        |wordDerivative l (fun y => q^τ * Real.exp (q*(eta*ρ y))) x| ≤
          C*q^l.length*(q^τ*Real.exp (q*(eta*ρ x))) := by
  obtain ⟨M, hM, hb⟩ := exists_profile_actual_bound hU hK hKU hρ n
  refine ⟨(n.factorial : ℝ)*M^n, by positivity, ?_⟩
  intro q hq τ eta heta l hl x hx
  have hρl : ContDiffOn ℝ l.length ρ U := hρ.of_le (by simp)
  have hbound : ∀ i, 1 ≤ i → i ≤ l.length →
      ‖iteratedFDerivWithin ℝ i (eta • ρ) U x‖ ≤ M := by
    intro i _ hi
    rw [iteratedFDerivWithin_const_smul_apply
      ((hρ.of_le (by simp : (i : ℕ∞ω) ≤ ∞)) x (hKU hx)) hU.uniqueDiffOn (hKU hx),
      norm_smul, Real.norm_eq_abs, heta, one_mul,
      iteratedFDerivWithin_eq_of_mem_nhds (hU.mem_nhds (hKU hx))]
    exact hb i (hi.trans hl) x hx
  have he := norm_iteratedFDerivWithin_allowedWeight (hρl.const_smul eta) hU.uniqueDiffOn
    (hKU hx) hq hM hbound τ
  simp only [smul_eq_mul] at he
  rw [iteratedFDerivWithin_eq_of_mem_nhds (hU.mem_nhds (hKU hx))] at he
  have hfac : (l.length.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hl
  have hpow := pow_le_pow_right₀ hM hl
  exact (abs_coordinateDerivative_le (wordVector l).get _ x).trans (he.trans (by gcongr))

end Carleman
