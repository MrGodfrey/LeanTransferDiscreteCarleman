module

public import Carleman.Transfer.Weights

/-! The exact budget exponents and minima from Corollary 2.2.
A zero denominator is omitted, never interpreted as a zero ratio. -/
@[expose] public noncomputable section
namespace Carleman
namespace CarlemanExponents
variable (a : CarlemanExponents)

def nuEnergy : ℝ := max a.dStar (max (4*a.m+a.dStar-a.c₀) 0)
def nuL2 : ℝ := max a.bStar (max (4*a.m+a.bStar-a.c₀) 0)

def omittedRatio (cap p ν : ℝ) : ℝ := if ν = 0 then cap else p/ν

def alphaX : ℝ := min 1 (min (omittedRatio 1 (2*a.m) a.nuEnergy)
  (omittedRatio 1 (4*a.m) a.nuL2))
def alphaT : ℝ := min (1/2) (min (omittedRatio (1/2) 1 a.nuEnergy)
  (omittedRatio (1/2) 2 a.nuL2))

theorem nuEnergy_nonneg : 0 ≤ a.nuEnergy := a.dStar_nonneg.trans (le_max_left _ _)
theorem nuL2_pos : 0 < a.nuL2 := a.c₀_pos.trans_le (a.c₀_le_bStar.trans (le_max_left _ _))

theorem omittedRatio_pos {cap p ν : ℝ} (hc : 0 < cap) (hp : 0 < p) (hν : 0 ≤ ν) :
    0 < omittedRatio cap p ν := by
  unfold omittedRatio
  split_ifs with h
  · exact hc
  · exact div_pos hp (lt_of_le_of_ne hν (Ne.symm h))

theorem mul_le_of_le_omittedRatio {cap p ν r : ℝ} (hp : 0 ≤ p) (hν : 0 ≤ ν)
    (hr : r ≤ omittedRatio cap p ν) : r*ν ≤ p := by
  by_cases h : ν = 0
  · simp only [h,mul_zero]; exact hp
  · rw [omittedRatio,ite_eq_right h] at hr
    exact (le_div_iff₀ (lt_of_le_of_ne hν (Ne.symm h))).mp hr

theorem scale_bounds :
    0 < a.alphaX ∧ a.alphaX ≤ 1 ∧ 0 < a.alphaT ∧ a.alphaT ≤ 1/2 ∧
    a.alphaX*a.nuEnergy ≤ 2*a.m ∧ a.alphaX*a.nuL2 ≤ 4*a.m ∧
    a.alphaT*a.nuEnergy ≤ 1 ∧ a.alphaT*a.nuL2 ≤ 2 := by
  have hm : (0:ℝ) < a.m := Nat.cast_pos.mpr a.m_pos
  have hE := a.nuEnergy_nonneg
  have h0 := a.nuL2_pos.le
  refine ⟨lt_min (by norm_num) (lt_min (omittedRatio_pos (by norm_num) (by positivity) hE)
    (omittedRatio_pos (by norm_num) (by positivity) h0)),min_le_left _ _,
    lt_min (by norm_num) (lt_min (omittedRatio_pos (by norm_num) (by norm_num) hE)
    (omittedRatio_pos (by norm_num) (by norm_num) h0)),min_le_left _ _,?_,?_,?_,?_⟩
  · exact mul_le_of_le_omittedRatio (by positivity) hE ((min_le_right _ _).trans (min_le_left _ _))
  · exact mul_le_of_le_omittedRatio (by positivity) h0 ((min_le_right _ _).trans (min_le_right _ _))
  · exact mul_le_of_le_omittedRatio (by norm_num) hE ((min_le_right _ _).trans (min_le_left _ _))
  · exact mul_le_of_le_omittedRatio (by norm_num) h0 ((min_le_right _ _).trans (min_le_right _ _))

/-- The heat exponents (m,c0,c1,o)=(1,3,1,3). -/
def heat : CarlemanExponents where
  m := 1
  m_pos := by norm_num
  c₀ := 3
  c₀_pos := by norm_num
  c := fun _ => 1
  c_nonneg := fun _ => by norm_num
  o := 3
  o_nonneg := by norm_num

theorem heat_scale_exponents : heat.dStar = 1 ∧ heat.bStar = 4 ∧
    heat.nuEnergy = 2 ∧ heat.nuL2 = 5 ∧ heat.alphaX = 4/5 ∧ heat.alphaT = 2/5 := by
  have hd : heat.dStar = 1 := by
    change max 0 (Finset.univ.sup' _ (fun j : Fin 1 => (1:ℝ)-2*((1-(j.val+1):ℕ):ℝ))) = 1
    have hf : (fun j : Fin 1 => (1:ℝ)-2*((1-(j.val+1):ℕ):ℝ)) = fun _ => 1 := by
      funext j
      fin_cases j
      norm_num
    rw [hf]
    change max 0 ((Finset.univ : Finset (Fin 1)).sup' Finset.univ_nonempty (fun _ => (1:ℝ))) = 1
    rw [Finset.sup'_const]
    norm_num
  have hb : heat.bStar = 4 := by norm_num [heat,bStar]
  have hm : heat.m = 1 := rfl
  have hc : heat.c₀ = 3 := rfl
  norm_num [hd,hb,hm,hc,nuEnergy,nuL2,alphaX,alphaT,omittedRatio]

end CarlemanExponents
end Carleman
