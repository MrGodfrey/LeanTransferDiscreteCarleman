module

public import Carleman.Spatial.FullSpaceInterpolation
public import Carleman.Spatial.ComponentNorms
public import Carleman.Spatial.DiscreteMaximum

/-! Parameter interpolation for the original symmetric derivative collections
on full space. Finite component maxima are an internal proof device only;
the final conclusion uses the actual Euclidean L² fields. -/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal
namespace Carleman.WeakSobolevJet
variable {d n : ℕ}
  (u : WeakSobolevJet d n (volume : Measure (SpatialCoordinates d)) univ)

def componentMaximum (k : ℕ) : ℝ≥0 :=
  if hk : k ≤ n then Finset.univ.sup (fun α : Sym (Fin d) k =>
    ‖derivativeComponent α (field ⟨k, by omega⟩ u)‖₊) else 0

theorem component_le_maximum (k : ℕ) (hk : k ≤ n) (α : Sym (Fin d) k) :
    ‖derivativeComponent α (field ⟨k, by omega⟩ u)‖ ≤ (componentMaximum u k : ℝ) := by
  unfold componentMaximum
  rw [dite_eq_left hk]
  exact_mod_cast Finset.le_sup (f := fun α : Sym (Fin d) k =>
    ‖derivativeComponent α (field ⟨k, by omega⟩ u)‖₊) (Finset.mem_univ α)

theorem componentMaximum_le_field (k : ℕ) (hk : k ≤ n) :
    (componentMaximum u k : ℝ) ≤ ‖field ⟨k, by omega⟩ u‖ := by
  unfold componentMaximum
  rw [dite_eq_left hk]
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro α _
  apply NNReal.coe_le_coe.mp
  change ‖derivativeComponent α (field ⟨k, by omega⟩ u)‖ ≤ ‖field ⟨k, by omega⟩ u‖
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [derivativeField_norm_sq]
  exact Finset.single_le_sum (f := fun β : Sym (Fin d) k =>
    ‖derivativeComponent β (field ⟨k, by omega⟩ u)‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ α)

theorem componentMaximum_zero : (componentMaximum u 0 : ℝ) = ‖value u‖ := by
  simp [componentMaximum, show ∀ α : Sym (Fin d) 0, α = Sym.nil from fun α => Subsingleton.elim _ _,
    value]
  rfl

theorem component_neighbor_sq_le (k : ℕ) (hk : k+2 ≤ n)
    (α : Sym (Fin d) k) (i : Fin d) :
    ‖derivativeComponent (Sym.cons i α) (field ⟨k+1, by omega⟩ u)‖^2 ≤
      ‖derivativeComponent α (field ⟨k, by omega⟩ u)‖*
        ‖derivativeComponent (Sym.cons i (Sym.cons i α)) (field ⟨k+2, by omega⟩ u)‖ := by
  exact weak_spatial_chain_norm_sq_le
    (field_weak_derivative u ⟨k, by omega⟩ α i)
    (field_weak_derivative u ⟨k+1, by omega⟩ (Sym.cons i α) i)

theorem componentMaximum_logConvex (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (componentMaximum u k : ℝ)^2 ≤
      (componentMaximum u (k-1) : ℝ)*(componentMaximum u (k+1) : ℝ) := by
  by_cases hz : componentMaximum u k = 0
  · simp only [hz, NNReal.coe_zero, zero_pow (by omega : 2 ≠ 0)]
    exact mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  have hp : (0 : ℝ≥0) < componentMaximum u k := lt_of_le_of_ne zero_le (Ne.symm hz)
  have hkm : k ≤ n := hkn.le
  unfold componentMaximum at hp
  rw [dite_eq_left hkm] at hp
  obtain ⟨α, _, hα⟩ := (Finset.le_sup_iff hp).mp le_rfl
  have hm : (componentMaximum u k : ℝ) ≤
      ‖derivativeComponent α (field ⟨k, by omega⟩ u)‖ := by
    unfold componentMaximum
    rw [dite_eq_left hkm]
    exact_mod_cast hα
  have he := le_antisymm hm (component_le_maximum u k hkm α)
  rw [he]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨i, α, rfl⟩ := Sym.exists_eq_cons_of_succ α
  have hh := component_neighbor_sq_le u j (by omega) α i
  exact hh.trans (mul_le_mul
    (component_le_maximum u j (by omega) α)
    (component_le_maximum u (j+2) (by omega) (Sym.cons i (Sym.cons i α)))
    (norm_nonneg _) (NNReal.coe_nonneg _))

theorem scaled_componentMaximum_le (r : ℝ) (hr : 0 ≤ r) (k : ℕ) (hk : k ≤ n) :
    r^(n-k)*(componentMaximum u k : ℝ) ≤
      max (r^n*‖value u‖) (componentMaximum u n : ℝ) := by
  let x := fun j => r^(n-j)*(componentMaximum u j : ℝ)
  have hx : ∀ j, 0 ≤ x j := fun j => mul_nonneg (pow_nonneg hr _) (NNReal.coe_nonneg _)
  have hc : ∀ j, 0 < j → j < n → (x j)^2 ≤ x (j-1)*x (j+1) := by
    intro j hj hjn
    have he : (n-(j-1))+(n-(j+1)) = 2*(n-j) := by omega
    dsimp [x]
    calc
      _ = r^(2*(n-j))*(componentMaximum u j : ℝ)^2 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm (n-j) 2]
      _ ≤ r^(2*(n-j))*((componentMaximum u (j-1) : ℝ)*(componentMaximum u (j+1) : ℝ)) :=
        mul_le_mul_of_nonneg_left (componentMaximum_logConvex u j hj hjn) (pow_nonneg hr _)
      _ = _ := by rw [← he, pow_add]; ring
  have hh := discrete_logConvex_maximum x n hx hc k hk
  simpa only [x, Nat.sub_zero, Nat.sub_self, pow_zero, one_mul, componentMaximum_zero u] using hh

/-- The constant is fixed before r and the full weak Sobolev state. This is
the full-space parameter estimate, not an extension theorem for a domain. -/
theorem fullSpace_parameter_interpolation (r : ℝ) (hr : 0 ≤ r) :
    (∑ k : Fin (n+1), r^(n-k.val)*‖field k u‖) ≤
      (∑ k : Fin (n+1), Real.sqrt (Fintype.card (Sym (Fin d) k.val)))*
        (‖u‖ + r^n*‖value u‖) := by
  have hend : (componentMaximum u n : ℝ) ≤ ‖u‖ :=
    (componentMaximum_le_field u n le_rfl).trans (norm_field_le _ u)
  have hB : 0 ≤ ‖u‖ + r^n*‖value u‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg hr _) (norm_nonneg _))
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  apply derivativeField_scaled_bound _ (pow_nonneg hr _) hB
  intro α
  have hh := (mul_le_mul_of_nonneg_left (component_le_maximum u k.val (by omega) α)
    (pow_nonneg hr (n-k.val))).trans (scaled_componentMaximum_le u r hr k.val (by omega))
  apply hh.trans
  exact max_le (le_add_of_nonneg_left (norm_nonneg _))
    (hend.trans (le_add_of_nonneg_right (mul_nonneg (pow_nonneg hr _) (norm_nonneg _))))

theorem fullSpace_parameter_interpolation_uniform (d n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ u : WeakSobolevJet d n (volume : Measure (SpatialCoordinates d)) univ,
      (∑ k : Fin (n+1), r^(n-k.val)*‖field k u‖) ≤ C*(‖u‖ + r^n*‖value u‖) := by
  let C := ∑ k : Fin (n+1), Real.sqrt (Fintype.card (Sym (Fin d) k.val))
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  refine ⟨1+C, by linarith, ?_⟩
  intro r hr u
  exact (fullSpace_parameter_interpolation u r hr).trans
    (mul_le_mul_of_nonneg_right (by linarith : C ≤ 1+C)
      (add_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg hr _) (norm_nonneg _))))

end Carleman.WeakSobolevJet
