module

public import Carleman.Spatial.RefinedChainInverse
public import Carleman.Geometry.CartesianInteriorNodes

/-! The actual tensor product of the one-dimensional nodal interpolation
bases, on all zero-boundary coarse nodal data. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def linearRefinementBasis (m a k : ℕ) : ℝ :=
  uniformLinearProlongation m (fun n => if n=a then 1 else 0) k

def tensorLinearProlongation (m K : Fin d → ℕ) (u : CartesianInteriorIndex K → ℝ)
    (z : Fin d → ℕ) : ℝ :=
  ∑ a, u a * ∏ r, linearRefinementBasis (m r) ((a r).val+1) (z r)

theorem linearRefinementBasis_node (m : ℕ) (hm : 0 < m) (a j : ℕ) :
    linearRefinementBasis m a (m*j) = if j=a then 1 else 0 :=
  uniformLinearProlongation_node m hm _ j

theorem uniformLinearProlongation_sum {ι : Type*} (s : Finset ι) (m : ℕ)
    (v : ι → ℕ → ℝ) (k : ℕ) :
    uniformLinearProlongation m (fun n => ∑ a ∈ s, v a n) k =
      ∑ a ∈ s, uniformLinearProlongation m (v a) k := by
  simp only [uniformLinearProlongation,linearRefinementValue,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]

theorem uniformLinearProlongation_const_mul (m : ℕ) (c : ℝ) (v : ℕ → ℝ) (k : ℕ) :
    uniformLinearProlongation m (fun n => c*v n) k = c*uniformLinearProlongation m v k := by
  unfold uniformLinearProlongation linearRefinementValue
  ring

theorem tensorLinearProlongation_zero_face (m K : Fin d → ℕ) (hm : ∀ r, 0 < m r)
    (u : CartesianInteriorIndex K → ℝ) (z : Fin d → ℕ) (r : Fin d)
    (hz : z r=0 ∨ z r=m r*K r) : tensorLinearProlongation m K u z=0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  have ha := (a r).isLt
  have he : linearRefinementBasis (m r) ((a r).val+1) (z r)=0 := by
    rcases hz with hz|hz
    · rw [hz,← Nat.mul_zero (m r),linearRefinementBasis_node _ (hm r)]
      simp
    · rw [hz,linearRefinementBasis_node _ (hm r)]
      simp only [ite_eq_right_iff]
      intro hh
      omega
  rw [Finset.prod_eq_zero (Finset.mem_univ r) he,mul_zero]

theorem tensorLinearProlongation_node (m K : Fin d → ℕ) (hm : ∀ r, 0 < m r)
    (u : CartesianInteriorIndex K → ℝ) (b : CartesianInteriorIndex K) :
    tensorLinearProlongation m K u (fun r => m r*((b r).val+1))=u b := by
  classical
  unfold tensorLinearProlongation
  rw [Finset.sum_eq_single b]
  · simp only [linearRefinementBasis_node _ (hm _),ite_true,Finset.prod_const_one,mul_one]
  · intro a _ hab
    have hn : ∃ r, a r ≠ b r := Function.ne_iff.mp hab
    obtain ⟨r,hr⟩ := hn
    have hv : (b r).val+1 ≠ (a r).val+1 := by
      intro he
      exact hr (Fin.ext (by omega))
    have he : linearRefinementBasis (m r) ((a r).val+1) (m r*((b r).val+1))=0 := by
      rw [linearRefinementBasis_node _ (hm r),ite_eq_right hv]
    rw [Finset.prod_eq_zero (Finset.mem_univ r) he,mul_zero]
  · simp

theorem tensorLinearProlongation_slice (m K : Fin d → ℕ) (hm : ∀ r, 0 < m r)
    (u : CartesianInteriorIndex K → ℝ) (z : Fin d → ℕ) (r : Fin d) (k : ℕ) :
    tensorLinearProlongation m K u (Function.update z r k) =
      uniformLinearProlongation (m r)
        (fun n => tensorLinearProlongation m K u (Function.update z r (m r*n))) k := by
  classical
  have hexpand (n : ℕ) : tensorLinearProlongation m K u (Function.update z r n) =
      ∑ a, (u a * ∏ j ∈ Finset.univ.erase r,
        linearRefinementBasis (m j) ((a j).val+1) (z j)) *
        linearRefinementBasis (m r) ((a r).val+1) n := by
    unfold tensorLinearProlongation
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ r)]
    simp only [Function.update_self]
    have hp : (∏ j ∈ Finset.univ.erase r,
        linearRefinementBasis (m j) ((a j).val+1) (Function.update z r n j)) =
        ∏ j ∈ Finset.univ.erase r, linearRefinementBasis (m j) ((a j).val+1) (z j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rw [hp]
    ring
  simp_rw [hexpand,linearRefinementBasis_node _ (hm r)]
  rw [uniformLinearProlongation_sum]
  simp_rw [uniformLinearProlongation_const_mul]
  rfl

end Carleman
