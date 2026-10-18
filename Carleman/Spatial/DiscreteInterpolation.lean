module

public import Carleman.Spatial.DiscreteMaximum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! A finite interpolation maximum principle. It is applied below only to
norms of actual weak derivative components after the analytic neighbor bound. -/
@[expose] public noncomputable section
namespace Carleman

theorem discrete_interpolation_maximum (n : ℕ) {δ K : ℝ} (hδ : 0 < δ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℕ → ℝ, (∀ j, 0 ≤ x j) →
      (∀ j, 0 < j → j < n → ∀ t : ℝ, 0 < t → t ≤ δ →
        x j ≤ K*(x (j-1)/t+t*x (j+1))) →
      ∀ j, j ≤ n → x j ≤ C*(x 0+x n) := by
  let L := max 1 (max (4*K) (1/δ))
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hLK : 4*K ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLδ : 1/δ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  let W := fun j : ℕ => L ^ ((j : ℝ)*(2*(n : ℝ)-(j : ℝ)))
  let C := L ^ ((n : ℝ)^2)
  have hWp (j : ℕ) : 0 < W j := Real.rpow_pos_of_pos hL _
  have hC : 1 ≤ C := Real.one_le_rpow hL1 (sq_nonneg _)
  refine ⟨C,hC,?_⟩
  intro x hx hb j hj
  let y := fun k => x k/W k
  have hy (k : ℕ) : 0 ≤ y k := div_nonneg (hx k) (hWp k).le
  have hconv : ∀ k, 0 < k → k < n → 2*y k ≤ y (k-1)+y (k+1) := by
    intro k hk hkn
    have hcast : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
    have hcastnext : ((k+1 : ℕ) : ℝ) = (k : ℝ)+1 := by simp
    have hkn' : (k : ℝ)+1 ≤ n := by exact_mod_cast hkn
    have hinc : W k ≤ W (k+1) := by
      apply Real.rpow_le_rpow_of_exponent_le hL1
      rw [hcastnext]
      nlinarith
    have hidentity : W k*W k = L^2*(W (k-1)*W (k+1)) := by
      dsimp [W]
      rw [hcast,hcastnext,← Real.rpow_add hL,← Real.rpow_add hL,
        ← Real.rpow_natCast L 2,← Real.rpow_add hL]
      congr 1
      norm_num
      ring
    let t := W k/(L*W (k+1))
    have htp : 0 < t := div_pos (hWp k) (mul_pos hL (hWp _))
    have htle : t ≤ δ := by
      have ht1 : t ≤ 1/L := by
        dsimp [t]
        apply (div_le_div_iff₀ (mul_pos hL (hWp _)) hL).mpr
        nlinarith [mul_le_mul_of_nonneg_left hinc hL.le]
      exact ht1.trans ((div_le_iff₀ hL).mpr (by nlinarith [(div_le_iff₀ hδ).mp hLδ]))
    have he := hb k hk hkn t htp htle
    have halg : (K*(x (k-1)/t+t*x (k+1)))/W k =
        K/L*(y (k-1)+y (k+1)) := by
      dsimp [t,y]
      field_simp [(hWp k).ne',(hWp (k+1)).ne',(hWp (k-1)).ne',hL.ne']
      have hid : W k^2 = L^2*(W (k-1)*W (k+1)) := by nlinarith [hidentity]
      rw [hid]
      ring
    have hdiv := (div_le_div_of_nonneg_right he (hWp k).le)
    rw [halg] at hdiv
    have hquarter : K/L ≤ 1/4 := (div_le_iff₀ hL).mpr (by linarith)
    have hs := mul_le_mul_of_nonneg_right hquarter (add_nonneg (hy (k-1)) (hy (k+1)))
    change y k ≤ _ at hdiv
    linarith [hy (k-1),hy (k+1)]
  have he := discrete_convex_maximum y n hconv j hj
  have hW0 : W 0 = 1 := by simp [W]
  have hWn : W n = C := by dsimp [W,C]; congr 1; ring
  have hy0 : y 0 = x 0 := by simp [y,hW0]
  have hyn : y n ≤ x n := by
    change x n/W n ≤ x n
    rw [hWn]
    exact div_le_self (hx n) hC
  have hmax : max (y 0) (y n) ≤ x 0+x n :=
    max_le (by rw [hy0]; exact le_add_of_nonneg_right (hx n))
      (hyn.trans (le_add_of_nonneg_left (hx 0)))
  have hjC : W j ≤ C := by
    apply Real.rpow_le_rpow_of_exponent_le hL1
    nlinarith [sq_nonneg ((n : ℝ)-(j : ℝ))]
  have hxy := (div_le_iff₀ (hWp j)).mp (he.trans hmax)
  exact hxy.trans (by nlinarith [mul_le_mul_of_nonneg_left hjC (add_nonneg (hx 0) (hx n))])
end Carleman
