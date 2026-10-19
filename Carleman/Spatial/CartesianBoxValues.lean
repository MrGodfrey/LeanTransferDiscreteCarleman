module

public import Carleman.Spatial.CartesianFiniteDifference

/-! Identifying a genuine zero-boundary rectangular nodal function with the
existing physical lattice data, including both boundary faces. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

theorem cartesianLatticeData_of_box_values (o δ : Fin d → ℝ) (hδ : ∀ r, 0 < δ r)
    (N : Fin d → ℕ) (V : (Fin d → ℕ) → ℝ)
    (hV : ∀ z r, z r=0 ∨ z r=N r → V z=0)
    (z : Fin d → ℕ) (hz : ∀ r, z r ≤ N r) :
    cartesianLatticeData o δ N (fun a => V (fun r => (a r).val+1)) (fun r => (z r:ℤ))=V z := by
  classical
  by_cases hf : ∃ r, z r=0 ∨ z r=N r
  · obtain ⟨r,hr⟩ := hf
    rw [hV z r hr]
    exact cartesianLatticeData_zero_face o δ hδ N _ _ r (by exact_mod_cast hr)
  · have hi (r : Fin d) : 0 < z r ∧ z r < N r := by
      have h := hz r
      have hn : ¬ (z r=0 ∨ z r=N r) := fun hh => hf ⟨r,hh⟩
      omega
    let a : CartesianInteriorIndex N := fun r => ⟨z r-1,by have := hi r; omega⟩
    have he : cartesianInteriorLatticeIndex N a=(fun r => (z r:ℤ)) := by
      funext r
      have := hi r
      change ((z r-1:ℕ):ℤ)+1=(z r:ℤ)
      omega
    rw [← he,cartesianLatticeData_at_interior o δ hδ N]
    congr 1
    funext r
    change z r-1+1=z r
    have := hi r
    omega

theorem cartesian_sum_box_values (N : Fin d → ℕ) (V : (Fin d → ℕ) → ℝ)
    (hV : ∀ z r, z r=0 → V z=0) :
    (∑ z : ∀ j, Fin (N j), V (fun j => (z j).val)) =
      ∑ a : CartesianInteriorIndex N, V (fun r => (a r).val+1) := by
  have he := cartesian_sum_zero_faces_to_interior N
    (fun z => V (fun r => (z r).toNat)) (by
      intro z hz
      obtain ⟨r,hr⟩ := hz
      simpa only [Int.toNat_natCast] using hV (fun j => (z j).val) r hr)
  have ht (n : ℕ) : ((n:ℤ)+1).toNat=n+1 := by omega
  simpa only [Int.toNat_natCast,cartesianInteriorLatticeIndex,ht] using he

theorem cartesianLatticeSuccessor_nat (z : Fin d → ℕ) (r : Fin d) :
    cartesianLatticeSuccessor (fun j => (z j:ℤ)) r =
      fun j => ((Function.update z r (z r+1) j):ℤ) := by
  funext j
  by_cases hj : j=r
  · subst j; simp [cartesianLatticeSuccessor]
  · simp [cartesianLatticeSuccessor,hj]

end Carleman
