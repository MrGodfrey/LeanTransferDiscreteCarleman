module

public import Carleman.Geometry.CartesianInteriorNodes

/-! Removing the lower coordinate faces from an actual finite rectangular sum.
All omitted terms are zero; no positivity assumption on the grid sizes is needed. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman
variable {d : ℕ}

def cartesianInteriorToBox (N : Fin d → ℕ) (a : CartesianInteriorIndex N) :
    ∀ j, Fin (N j) := fun j => ⟨(a j).val+1,by have := (a j).isLt; omega⟩

theorem cartesianInteriorToBox_injective (N : Fin d → ℕ) :
    Function.Injective (cartesianInteriorToBox N) := by
  intro a b hab
  funext j
  apply Fin.ext
  have he := congrArg (fun z : ∀ j, Fin (N j) => (z j).val) hab
  change (a j).val+1=(b j).val+1 at he
  omega

theorem cartesian_sum_zero_faces_to_interior (N : Fin d → ℕ)
    (F : (Fin d → ℤ) → ℝ)
    (hF : ∀ z : ∀ j, Fin (N j), (∃ j, (z j).val=0) → F (fun j => ((z j).val:ℤ))=0) :
    (∑ z : ∀ j, Fin (N j), F (fun j => ((z j).val:ℤ)))=
      ∑ a : CartesianInteriorIndex N, F (cartesianInteriorLatticeIndex N a) := by
  classical
  symm
  apply Fintype.sum_of_injective (cartesianInteriorToBox N) (cartesianInteriorToBox_injective N)
  · intro z hz
    apply hF z
    by_contra hn
    push Not at hn
    let a : CartesianInteriorIndex N := fun j => ⟨(z j).val-1,by have := (z j).isLt; have := hn j; omega⟩
    apply hz
    refine ⟨a,?_⟩
    funext j
    apply Fin.ext
    change (z j).val-1+1=(z j).val
    have := hn j
    omega
  · intro a
    congr 1

end Carleman
