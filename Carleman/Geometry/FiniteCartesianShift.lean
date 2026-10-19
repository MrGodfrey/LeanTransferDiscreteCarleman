module

public import Carleman.Geometry.CartesianInteriorNodes
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! Exact finite-grid translation of a function that vanishes on the
translated coordinate faces. Cyclic reindexing adds no boundary term. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {d n : ℕ}

theorem finRotate_val_step (i : Fin n) :
    (finRotate n i).val=if i.val+1 < n then i.val+1 else 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases hi : i=Fin.last n
    · subst i
      simp
    · rw [ite_eq_right hi,ite_eq_left (by have := Fin.val_lt_last hi; omega)]

theorem cartesian_sum_face_zero_shift (N : Fin d → ℕ) (J : Finset (Fin d))
    (F : (Fin d → ℤ) → ℝ)
    (hF : ∀ j ∈ J, ∀ x : Fin d → ℤ, x j=0 ∨ x j=(N j:ℤ) → F x=0) :
    (∑ z : ∀ j, Fin (N j), F (fun j => ((z j).val:ℤ)+if j ∈ J then 1 else 0))=
      ∑ z : ∀ j, Fin (N j), F (fun j => ((z j).val:ℤ)) := by
  classical
  let e : (∀ j, Fin (N j)) ≃ (∀ j, Fin (N j)) :=
    Equiv.piCongrRight (fun j => if j ∈ J then finRotate (N j) else Equiv.refl _)
  calc
    _ = ∑ z : ∀ j, Fin (N j), F (fun j => (((e z) j).val:ℤ)) := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : ∃ j ∈ J, (z j).val+1=N j
      · obtain ⟨j,hj,hwrap⟩ := hz
        have ha : ((z j).val:ℤ)+(if j ∈ J then 1 else 0)=(N j:ℤ) := by
          rw [ite_eq_left hj]
          exact_mod_cast hwrap
        have hb : (((e z) j).val:ℤ)=0 := by
          change (((if j ∈ J then finRotate (N j) else Equiv.refl _) (z j)).val:ℤ)=0
          rw [ite_eq_left hj,finRotate_val_step,ite_eq_right (by omega)]
          rfl
        rw [hF j hj _ (Or.inr ha),hF j hj _ (Or.inl hb)]
      · congr 1
        funext j
        change ((z j).val:ℤ)+(if j ∈ J then 1 else 0)=
          (((if j ∈ J then finRotate (N j) else Equiv.refl _) (z j)).val:ℤ)
        by_cases hj : j ∈ J
        · have hn : (z j).val+1 < N j := by
            have := (z j).isLt
            have hne : (z j).val+1 ≠ N j := fun he => hz ⟨j,hj,he⟩
            omega
          rw [ite_eq_left hj,ite_eq_left hj,finRotate_val_step,ite_eq_left hn]
          norm_cast
        · rw [ite_eq_right hj,ite_eq_right hj]
          simp
    _ = _ := Equiv.sum_comp e (fun z : ∀ j, Fin (N j) => F (fun j => ((z j).val:ℤ)))

end Carleman
