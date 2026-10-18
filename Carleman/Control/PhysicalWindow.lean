module

public import Carleman.Control.PhysicalRamp
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Finset.Card

/-! Actual node-counting estimates on the physical grid. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical

def leftNodes (g : TimeGrid) (b : ℝ) : Finset (Fin g.steps) :=
  Finset.univ.filter (fun i => (i.val:ℝ)*g.dt ≤ b)

def rightNodes (g : TimeGrid) (b : ℝ) : Finset (Fin g.steps) :=
  Finset.univ.filter (fun i => g.period-(i.val:ℝ)*g.dt ≤ b)

theorem leftNodes_measure (g : TimeGrid) (b : ℝ) (hb : 0 ≤ b) :
    g.dt*(leftNodes g b).card ≤ b+g.dt := by
  have hin : (leftNodes g b).image Fin.val ⊆ Finset.range (⌊b/g.dt⌋₊+1) := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have hh : (i.val:ℝ)*g.dt ≤ b := (Finset.mem_filter.mp hi).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ((le_div_iff₀ g.dt_pos).mpr hh)))
  have hc : (leftNodes g b).card ≤ ⌊b/g.dt⌋₊+1 := by
    have hh := Finset.card_le_card hin
    simpa only [Finset.card_image_of_injective _ Fin.val_injective,Finset.card_range] using hh
  have hreal : ((leftNodes g b).card:ℝ) ≤ (⌊b/g.dt⌋₊:ℝ)+1 := by exact_mod_cast hc
  have hf := Nat.floor_le (div_nonneg hb g.dt_pos.le)
  have hh := mul_le_mul_of_nonneg_left (show ((leftNodes g b).card:ℝ) ≤ b/g.dt+1 by
    linarith only [hreal,hf]) g.dt_pos.le
  calc
    _ ≤ g.dt*(b/g.dt+1) := hh
    _ = b+g.dt := by field_simp [ne_of_gt g.dt_pos]

theorem rightNodes_measure (g : TimeGrid) (b : ℝ) (hb : 0 ≤ b) :
    g.dt*(rightNodes g b).card ≤ b+g.dt := by
  have hin : (rightNodes g b).image Fin.rev ⊆ leftNodes g b := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have hh : g.period-(i.val:ℝ)*g.dt ≤ b := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have he : ((i.rev).val:ℝ)+(i.val:ℝ)+1 = g.steps := by
      exact_mod_cast (show i.rev.val+i.val+1 = g.steps by simp only [Fin.rev]; omega)
    dsimp only [TimeGrid.period] at hh
    nlinarith [g.dt_pos]
  have hc : (rightNodes g b).card ≤ (leftNodes g b).card := by
    simpa only [Finset.card_image_of_injective _ Fin.rev_injective] using Finset.card_le_card hin
  exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) g.dt_pos.le).trans (leftNodes_measure g b hb)

def middleNodes (g : TimeGrid) : Finset (Fin g.steps) :=
  Finset.univ.filter (fun i => g.period/3 ≤ (i.val:ℝ)*g.dt ∧ (i.val:ℝ)*g.dt ≤ 2*g.period/3)

theorem middleNodes_measure (g : TimeGrid) (hdt : g.dt ≤ g.period/12) :
    g.period/6 ≤ g.dt*(middleNodes g).card := by
  have hin : Finset.univ ⊆ (middleNodes g ∪ leftNodes g (g.period/3)) ∪ rightNodes g (g.period/3) := by
    intro i _
    by_cases hm : g.period/3 ≤ (i.val:ℝ)*g.dt ∧ (i.val:ℝ)*g.dt ≤ 2*g.period/3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩))
    · by_cases hl : (i.val:ℝ)*g.dt ≤ g.period/3
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩))
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        have hh : 2*g.period/3 < (i.val:ℝ)*g.dt := by
          by_contra hn
          exact hm ⟨(lt_of_not_ge hl).le,le_of_not_gt hn⟩
        linarith only [hh]
  have hc : g.steps ≤ (middleNodes g).card+(leftNodes g (g.period/3)).card+(rightNodes g (g.period/3)).card := by
    have hh := (Finset.card_le_card hin).trans (Finset.card_union_le _ _)
    have hleft := Finset.card_union_le (middleNodes g) (leftNodes g (g.period/3))
    simpa only [Finset.card_univ,Fintype.card_fin] using hh.trans (Nat.add_le_add_right hleft _)
  have hh := mul_le_mul_of_nonneg_left (show (g.steps:ℝ) ≤
    (middleNodes g).card+(leftNodes g (g.period/3)).card+(rightNodes g (g.period/3)).card by exact_mod_cast hc) g.dt_pos.le
  have hl := leftNodes_measure g (g.period/3) (div_nonneg g.period_pos.le (by norm_num))
  have hr := rightNodes_measure g (g.period/3) (div_nonneg g.period_pos.le (by norm_num))
  have hT : g.dt*(g.steps:ℝ) = g.period := by rw [TimeGrid.period,mul_comm]
  nlinarith only [hh,hl,hr,hT,hdt]

def transitionNodes (g : TimeGrid) (a : ℝ) : Finset (Fin g.steps) :=
  Finset.univ.filter (fun i => cutoffNodes g a i.succ ≠ cutoffNodes g a i.castSucc)

theorem transitionNodes_measure (g : TimeGrid) (a : ℝ) (ha : 0 < a) (hdt : g.dt ≤ a/4) :
    g.dt*(transitionNodes g a).card ≤ 5*a := by
  have hin : transitionNodes g a ⊆ leftNodes g (2*a+g.dt) ∪ rightNodes g (2*a+g.dt) := by
    intro i hi
    have hh := cutoffNodes_transition_location g a ha i (Finset.mem_filter.mp hi).2
    rcases hh with hl | hr
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)
  have hc := (Finset.card_le_card hin).trans (Finset.card_union_le _ _)
  have hh := mul_le_mul_of_nonneg_left (show ((transitionNodes g a).card:ℝ) ≤
    (leftNodes g (2*a+g.dt)).card+(rightNodes g (2*a+g.dt)).card by exact_mod_cast hc) g.dt_pos.le
  have hl := leftNodes_measure g (2*a+g.dt) (by linarith [g.dt_pos])
  have hr := rightNodes_measure g (2*a+g.dt) (by linarith [g.dt_pos])
  nlinarith only [hh,hl,hr,hdt]

end Carleman.Physical
