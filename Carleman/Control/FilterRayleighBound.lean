module

public import Carleman.Control.FilterReverse

/-! An energy estimate controls the paper's actual Rayleigh supremum,
including its prescribed value zero for the zero terminal space. -/
@[expose] public noncomputable section
namespace Carleman.Physical
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem filterRayleigh_le_of_energy_bound (A : X →L[ℝ] X) (F : Submodule ℝ X)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ F, inner ℝ (A x) x ≤ C*‖x‖^2) :
    filterRayleigh A F ≤ C := by
  classical
  by_cases hF : F=⊥
  · rw [hF,filterRayleigh_bot]
    exact hC
  rw [filterRayleigh,ite_eq_right hF]
  apply csSup_le
  · obtain ⟨x,hx,hx0⟩ := F.ne_bot_iff.mp hF
    exact ⟨rayleigh A.toLinearMap x,x,hx,hx0,rfl⟩
  · rintro r ⟨x,hx,hx0,rfl⟩
    exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mpr (hb x hx)

end Carleman.Physical
