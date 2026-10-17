module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! A finite maximum principle for nonnegative log-convex sequences. -/
@[expose] public section
namespace Carleman

theorem discrete_convex_maximum (x : ℕ → ℝ) (n : ℕ)
    (h : ∀ k, 0 < k → k < n → 2*x k ≤ x (k-1)+x (k+1)) :
    ∀ k, k ≤ n → x k ≤ max (x 0) (x n) := by
  induction n with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    simp [this]
  | succ n ih =>
    have hp := ih (fun k hk hn => h k hk (by omega))
    have hend : x n ≤ max (x 0) (x (n+1)) := by
      by_cases hn : n = 0
      · subst n; exact le_max_left _ _
      by_contra hh
      have hlarge := lt_of_not_ge hh
      have h0 : x 0 < x n := lt_of_le_of_lt (le_max_left _ _) hlarge
      have hnext : x (n+1) < x n := lt_of_le_of_lt (le_max_right _ _) hlarge
      have hprev := hp (n-1) (by omega)
      rw [max_eq_right h0.le] at hprev
      have hc := h n (by omega) (by omega)
      linarith
    intro k hk
    by_cases he : k = n+1
    · subst k; exact le_max_right _ _
    exact (hp k (by omega)).trans (max_le (le_max_left _ _) hend)

theorem discrete_logConvex_maximum (x : ℕ → ℝ) (n : ℕ)
    (hx : ∀ k, 0 ≤ x k)
    (h : ∀ k, 0 < k → k < n → (x k)^2 ≤ x (k-1)*x (k+1)) :
    ∀ k, k ≤ n → x k ≤ max (x 0) (x n) := by
  apply discrete_convex_maximum x n
  intro k hk hn
  have hh := h k hk hn
  have hp := hx (k-1)
  have hq := hx (k+1)
  have hm := hx k
  nlinarith [sq_nonneg (x (k-1)-x (k+1))]

end Carleman
