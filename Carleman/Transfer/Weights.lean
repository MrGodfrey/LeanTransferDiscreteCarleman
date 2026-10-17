module

public import Carleman.Continuous.WeightedNorm

/-! Exact Section 5 exponents and errors; time and node weights share one q. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman

structure CarlemanExponents where
  m : ℕ
  m_pos : 0 < m
  c₀ : ℝ
  c₀_pos : 0 < c₀
  c : Fin m → ℝ
  c_nonneg : ∀ j, 0 ≤ c j
  o : ℝ
  o_nonneg : 0 ≤ o

namespace CarlemanExponents
variable (a : CarlemanExponents)

/-- j is stored as j-1, so the actual spatial order is j.val+1. -/
def energyPower (j : Fin a.m) : ℝ := max 0 (a.c j - 2 * (a.m - (j.val + 1) : ℕ))

def dStar : ℝ := max 0 (Finset.univ.sup'
  ⟨⟨0, a.m_pos⟩, Finset.mem_univ _⟩ (fun j : Fin a.m => a.c j - 2 * (a.m - (j.val + 1) : ℕ)))

def bStar : ℝ := max a.c₀ (max a.o (4 * a.m))

theorem energyPower_nonneg (j : Fin a.m) : 0 ≤ a.energyPower j := le_max_left _ _

theorem energyPower_le_dStar (j : Fin a.m) : a.energyPower j ≤ a.dStar := by
  apply max_le (le_max_left _ _)
  exact (Finset.le_sup' (fun j : Fin a.m => a.c j - 2 * (a.m - (j.val + 1) : ℕ))
    (Finset.mem_univ j)).trans (le_max_right _ _)

theorem dStar_nonneg : 0 ≤ a.dStar := le_max_left _ _
theorem c₀_le_bStar : a.c₀ ≤ a.bStar := le_max_left _ _
theorem o_le_bStar : a.o ≤ a.bStar := (le_max_left _ _).trans (le_max_right _ _)
theorem four_m_le_bStar : (4 * a.m : ℝ) ≤ a.bStar := (le_max_right _ _).trans (le_max_right _ _)
theorem bStar_nonneg : 0 ≤ a.bStar := a.c₀_pos.le.trans a.c₀_le_bStar

/-- All energy powers and all three L² weights in the proof are covered. -/
theorem weight_coverage {τ : ℝ} (h : max (a.dStar / 2) (a.bStar / 2) ≤ τ) :
    (∀ j, a.energyPower j / 2 ≤ τ) ∧ a.c₀ / 2 ≤ τ ∧ a.o / 2 ≤ τ ∧ (2 * a.m : ℝ) ≤ τ := by
  have hd := (le_max_left _ _).trans h
  have hb := (le_max_right _ _).trans h
  refine ⟨fun j => ?_, ?_, ?_, ?_⟩
  · linarith [a.energyPower_le_dStar j]
  · linarith [a.c₀_le_bStar]
  · linarith [a.o_le_bStar]
  · linarith [a.four_m_le_bStar]

end CarlemanExponents

structure ErrorScales where
  aE : ℝ
  a₀ : ℝ
  ηA : ℝ
  aE_nonneg : 0 ≤ aE
  a₀_nonneg : 0 ≤ a₀
  ηA_nonneg : 0 ≤ ηA

namespace ErrorScales
variable (e : ErrorScales) (g : TimeGrid)
def energy : ℝ := e.aE + e.ηA + Real.sqrt g.dt
def l2 : ℝ := e.a₀ + e.aE ^ 2 + e.ηA + g.dt

def loadDefect (a : CarlemanExponents) (Q : ℝ) : ℝ :=
  e.energy g ^ 2 * Q ^ a.dStar + e.l2 g ^ 2 * Q ^ a.bStar

def stateDefect (a : CarlemanExponents) (Q : ℝ) : ℝ :=
  e.energy g ^ 2 * max 1 (Q ^ (4 * a.m + a.dStar - a.c₀)) +
  e.l2 g ^ 2 * max 1 (Q ^ (4 * a.m + a.bStar - a.c₀))
end ErrorScales

namespace TimeGrid
/-- The representative nodes t_n=n δt of Section 2.4. -/
def nodeTime (g : TimeGrid) (i : g.Index) : ℝ := (i.val : ℝ) * g.dt
end TimeGrid

/-- q is its periodic real-time extension. The bounds hold for that extension. -/
structure TimeWeight where
  q : ℝ → ℝ
  max : ℝ
  lower : ∀ t, 1 ≤ q t
  upper : ∀ t, q t ≤ max

namespace TimeWeight
variable (w : TimeWeight)
def nodes (g : TimeGrid) : g.Sequence ℝ := fun i => w.q (g.nodeTime i)
theorem nonneg (t : ℝ) : 0 ≤ w.q t := zero_le_one.trans (w.lower t)
theorem pos (t : ℝ) : 0 < w.q t := zero_lt_one.trans_le (w.lower t)
theorem max_ge_one : 1 ≤ w.max := (w.lower 0).trans (w.upper 0)
end TimeWeight
end Carleman

@[expose] public noncomputable section
namespace Carleman

def frozenShift (a : CarlemanExponents) (w : TimeWeight) (g : TimeGrid) (L : ℝ) :
    g.Sequence ℝ := fun i => (L * w.nodes g i) ^ (2 * a.m)

theorem frozenShift_sq (a : CarlemanExponents) (w : TimeWeight) (g : TimeGrid)
    (L : ℝ) (i : g.Index) :
    frozenShift a w g L i ^ 2 = L ^ (4 * a.m) * (w.nodes g i) ^ (4 * a.m : ℝ) := by
  unfold frozenShift
  rw [← pow_mul]
  have he : 2 * a.m * 2 = 4 * a.m := by omega
  rw [he, mul_pow]
  congr 1
  norm_cast

/-- L is fixed before the grid; the bound has no dependence on T or δt. -/
theorem frozenShift_sq_le (a : CarlemanExponents) (w : TimeWeight) (g : TimeGrid)
    (L K : ℝ) (h : L ^ (4 * a.m) ≤ K) (i : g.Index) :
    frozenShift a w g L i ^ 2 ≤ K * (w.nodes g i) ^ (4 * a.m : ℝ) := by
  rw [frozenShift_sq]
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (w.nonneg _) _)
end Carleman

@[expose] public noncomputable section
namespace Carleman

theorem frozenShift_pos (a : CarlemanExponents) (w : TimeWeight) (g : TimeGrid)
    {L : ℝ} (hL : 1 ≤ L) (i : g.Index) : 0 < frozenShift a w g L i :=
  pow_pos (mul_pos (zero_lt_one.trans_le hL) (w.pos _)) _

namespace TimeGrid

theorem nodeTime_nonneg (g : TimeGrid) (i : g.Index) : 0 ≤ g.nodeTime i :=
  mul_nonneg (Nat.cast_nonneg _) g.dt_pos.le

theorem nodeTime_lt_period (g : TimeGrid) (i : g.Index) : g.nodeTime i < g.period :=
  mul_lt_mul_of_pos_right (Nat.cast_lt.mpr i.isLt) g.dt_pos

end TimeGrid
end Carleman
