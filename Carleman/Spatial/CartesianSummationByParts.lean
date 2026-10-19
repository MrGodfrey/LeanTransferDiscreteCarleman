module

public import Carleman.Spatial.CartesianLatticeDifferences

/-! Exact zero-boundary finite summation by parts on the actual integer grid. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianLatticePredecessor (z : Fin d → ℤ) (r : Fin d) : Fin d → ℤ :=
  fun j => z j-if j=r then 1 else 0

theorem cartesianLatticePredecessor_successor (z : Fin d → ℤ) (r : Fin d) :
    cartesianLatticePredecessor (cartesianLatticeSuccessor z r) r=z := by
  funext j
  simp only [cartesianLatticePredecessor,cartesianLatticeSuccessor,add_sub_cancel_right]

theorem cartesian_sum_axis_shift (N : Fin d → ℕ) (r : Fin d)
    (F : (Fin d → ℤ) → ℝ)
    (hF : ∀ z, z r=0 ∨ z r=(N r:ℤ) → F z=0) :
    (∑ z : ∀ j, Fin (N j), F (cartesianLatticeSuccessor (fun j => ((z j).val:ℤ)) r))=
      ∑ z : ∀ j, Fin (N j), F (fun j => ((z j).val:ℤ)) := by
  classical
  have he := cartesian_sum_face_zero_shift N {r} F (by
    intro j hj z hz
    have hjr := Finset.mem_singleton.mp hj
    subst j
    exact hF z hz)
  change (∑ z : ∀ j, Fin (N j), F (fun j => ((z j).val:ℤ)+if j=r then 1 else 0))=_
  simpa only [Finset.mem_singleton] using he

theorem cartesian_sum_axis_by_parts (N : Fin d → ℕ) (r : Fin d)
    (F G : (Fin d → ℤ) → ℝ)
    (hG : ∀ z, z r=0 ∨ z r=(N r:ℤ) → G z=0) :
    (∑ z : ∀ j, Fin (N j),
      (F (cartesianLatticeSuccessor (fun j => ((z j).val:ℤ)) r)-F (fun j => ((z j).val:ℤ)))*
      (G (cartesianLatticeSuccessor (fun j => ((z j).val:ℤ)) r)-G (fun j => ((z j).val:ℤ))))=
    ∑ z : ∀ j, Fin (N j),
      (2*F (fun j => ((z j).val:ℤ))-F (cartesianLatticeSuccessor (fun j => ((z j).val:ℤ)) r)-
        F (cartesianLatticePredecessor (fun j => ((z j).val:ℤ)) r))*G (fun j => ((z j).val:ℤ)) := by
  have hsame := cartesian_sum_axis_shift N r (fun z => F z*G z)
    (by intro z hz; rw [hG z hz,mul_zero])
  have hcross := cartesian_sum_axis_shift N r (fun z => F (cartesianLatticePredecessor z r)*G z)
    (by intro z hz; rw [hG z hz,mul_zero])
  simp only [cartesianLatticePredecessor_successor] at hcross
  simp only [sub_mul,mul_sub,mul_assoc,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [hsame,hcross]
  ring

end Carleman
