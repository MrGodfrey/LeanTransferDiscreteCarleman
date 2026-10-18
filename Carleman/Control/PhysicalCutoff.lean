module

public import Carleman.Control.PhysicalEquations
public import Carleman.Periodic.SummationByParts

/-! The actual physical adjoint restricted to a periodic cutoff sequence.
Both endpoint values vanish before cyclic indexing is used. -/
@[expose] public noncomputable section
namespace Carleman.Physical
variable {X : Type*}

theorem periodic_next_of_endpoints (g : TimeGrid) (v : Fin (g.steps+1) → X)
    (hv : v 0 = v (Fin.last g.steps)) (i : Fin g.steps) :
    v (g.next i).castSucc = v i.succ := by
  have hn : (g.next i).val = (i.val+1)%g.steps := by
    rw [g.next_eq_add_one]
    simp [Fin.val_add,Nat.add_mod]
  by_cases hi : i.val+1 < g.steps
  · have he : (g.next i).castSucc = i.succ := by
      apply Fin.ext
      simpa only [Fin.val_castSucc,Fin.val_succ,Nat.mod_eq_of_lt hi] using hn
    rw [he]
  · have he : i.val+1 = g.steps := by omega
    have hlast : i.succ = Fin.last g.steps := Fin.ext he
    have hzero : (g.next i).castSucc = 0 := by
      apply Fin.ext
      simpa only [Fin.val_castSucc,Fin.val_zero,he,Nat.mod_self] using hn
    rw [hzero,hlast,hv]

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def cutoffState (g : TimeGrid) (χ : Fin (g.steps+1) → ℝ) (p : Fin (g.steps+1) → X) :
    g.Sequence X := fun i => χ i.castSucc • p i.castSucc

def cutoffRemainder (g : TimeGrid) (χ : Fin (g.steps+1) → ℝ) (p : Fin (g.steps+1) → X) :
    g.Sequence X := fun i => ((χ i.succ-χ i.castSucc)/g.dt) • p i.succ

theorem cutoff_next (g : TimeGrid) (χ : Fin (g.steps+1) → ℝ) (p : Fin (g.steps+1) → X)
    (hχ0 : χ 0 = 0) (hχN : χ (Fin.last g.steps) = 0) (i : Fin g.steps) :
    cutoffState g χ p (g.next i) = χ i.succ • p i.succ := by
  exact periodic_next_of_endpoints g (fun n => χ n • p n)
    (by rw [hχ0,hχN,zero_smul,zero_smul]) i

theorem cutoff_difference (g : TimeGrid) (χ : Fin (g.steps+1) → ℝ) (p : Fin (g.steps+1) → X)
    (hχ0 : χ 0 = 0) (hχN : χ (Fin.last g.steps) = 0) (i : Fin g.steps) :
    g.dMinus (cutoffState g χ p) i =
      χ i.castSucc • (g.dt⁻¹ • (p i.castSucc-p i.succ))-cutoffRemainder g χ p i := by
  rw [TimeGrid.dMinus,cutoff_next g χ p hχ0 hχN]
  change g.dt⁻¹ • (χ i.castSucc • p i.castSucc-χ i.succ • p i.succ) = _
  simp only [cutoffRemainder,div_eq_mul_inv,smul_sub,smul_smul,sub_mul,
    mul_comm (χ i.castSucc),mul_comm (χ i.succ),sub_smul]
  abel

theorem cutoff_residual [CompleteSpace X] (g : TimeGrid) (A : X →L[ℝ] X)
    (V : Fin g.steps → X →L[ℝ] X) (hSym : ∀ i, (A+V i).IsSymmetric)
    (χ : Fin (g.steps+1) → ℝ) (p : Fin (g.steps+1) → X)
    (hχ0 : χ 0 = 0) (hχN : χ (Fin.last g.steps) = 0)
    (hp : AdjointEquation g.dt (fun i => A+V i) p) (i : Fin g.steps) :
    g.dMinus (cutoffState g χ p) i+A (cutoffState g χ p i) =
      -V i (cutoffState g χ p i)-cutoffRemainder g χ p i := by
  have hh := hp i
  rw [(hSym i).clm_adjoint_eq] at hh
  change g.dt⁻¹ • (p i.castSucc-p i.succ)+(A (p i.castSucc)+V i (p i.castSucc)) = 0 at hh
  have he : g.dt⁻¹ • (p i.castSucc-p i.succ) = -(A (p i.castSucc)+V i (p i.castSucc)) :=
    eq_neg_of_add_eq_zero_left hh
  rw [cutoff_difference g χ p hχ0 hχN,he]
  simp only [cutoffState,map_smul,smul_neg,smul_add]
  abel

end Carleman.Physical
