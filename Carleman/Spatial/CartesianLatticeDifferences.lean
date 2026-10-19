module

public import Carleman.Spatial.CartesianKuhnCellStiffness
public import Carleman.Geometry.FiniteCartesianShift

/-! The original finite nodal data, extended by zero, on the actual integer
grid. Kuhn step quotients are exactly the coordinate forward differences. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Carleman
variable {d : ℕ}

def cartesianLatticeData (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (f : CartesianInteriorIndex N → ℝ) (z : Fin d → ℤ) : ℝ :=
  cartesianInteriorData o δ N f (cartesianGridPoint o δ z)

theorem cartesianLatticeData_zero_face (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (z : Fin d → ℤ)
    (j : Fin d) (hz : z j=0 ∨ z j=(N j:ℤ)) : cartesianLatticeData o δ N f z=0 := by
  apply cartesianInteriorData_zero_compl o δ hδ N f
  intro hx
  have hj := hx j
  change o j < o j+(z j:ℝ)*δ j ∧ o j+(z j:ℝ)*δ j < o j+(N j:ℝ)*δ j at hj
  rcases hz with hz | hz
  · simp only [hz,Int.cast_zero,zero_mul,add_zero,lt_self_iff_false,false_and] at hj
  · have hu := hj.2
    simp only [hz,Int.cast_natCast,lt_self_iff_false] at hu

def cartesianLatticeSuccessor (z : Fin d → ℤ) (r : Fin d) : Fin d → ℤ :=
  fun j => z j+if j=r then 1 else 0

def cartesianAxisDifference (o δ : Fin d → ℝ) (N : Fin d → ℕ)
    (f : CartesianInteriorIndex N → ℝ) (z : Fin d → ℤ) (r : Fin d) : ℝ :=
  (cartesianLatticeData o δ N f (cartesianLatticeSuccessor z r)-cartesianLatticeData o δ N f z)/δ r

theorem cartesianAxisDifference_zero_transverse (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (z : Fin d → ℤ)
    (j r : Fin d) (hjr : j ≠ r) (hz : z j=0 ∨ z j=(N j:ℤ)) :
    cartesianAxisDifference o δ N f z r=0 := by
  have hs : cartesianLatticeSuccessor z r j=z j := by simp only [cartesianLatticeSuccessor,ite_eq_right hjr,add_zero]
  rw [cartesianAxisDifference,cartesianLatticeData_zero_face o δ hδ N f z j hz,
    cartesianLatticeData_zero_face o δ hδ N f _ j (by rwa [hs]),sub_self,zero_div]

theorem kuhnVertexIndex_succ_eq_axis (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (k : Fin d) :
    kuhnVertexIndex z π k.succ=cartesianLatticeSuccessor (kuhnVertexIndex z π k.castSucc) (π k) := by
  funext j
  by_cases hj : j=π k
  · subst j
    simp [kuhnVertexIndex,cartesianLatticeSuccessor]
  · have hne : π.symm j ≠ k := fun h => hj (by rw [← h,π.apply_symm_apply])
    have hi : (π.symm j).val < k.val+1 ↔ (π.symm j).val < k.val := by
      have hn : (π.symm j).val ≠ k.val := fun h => hne (Fin.ext h)
      omega
    simp only [kuhnVertexIndex,cartesianLatticeSuccessor,Fin.val_succ,Fin.val_castSucc,hi,ite_eq_right hj,add_zero]

theorem cartesianKuhnCellDifference_eq_axis (o δ : Fin d → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : Fin d → ℕ) (f : CartesianInteriorIndex N → ℝ) (i : CartesianCellIndex N) (k : Fin d) :
    cartesianKuhnCellDifference o δ hδ N f i k=
      cartesianAxisDifference o δ N f
        (kuhnVertexIndex (cartesianCellLatticeIndex N i).1 i.2 k.castSucc) (i.2 k) := by
  unfold cartesianKuhnCellDifference cartesianAxisDifference cartesianLatticeData
  simp only [cartesianFiniteSimplex,cartesianKuhnSimplex_points_eq_gridPoint,kuhnVertexIndex_succ_eq_axis]

end Carleman
