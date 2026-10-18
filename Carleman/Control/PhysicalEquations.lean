module

public import Carleman.Control.PhysicalEnergy
public import Carleman.Periodic.TimeGrid
public import Mathlib.Tactic.Abel

/-! Exact connection to the original divided-by-dt forward and actual
Hilbert adjoint equations, on physical rather than periodic nodes. -/
@[expose] public noncomputable section
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {N : ℕ}

theorem step_equation_iff {dt : ℝ} (hdt : dt ≠ 0) (L : X →ₗ[ℝ] X) (x y f : X) :
    step dt L x = y+dt • f ↔ dt⁻¹ • (x-y)+L x = f := by
  have he : dt • (dt⁻¹ • (x-y)+L x) = step dt L x-y := by
    simp only [smul_add,smul_smul,mul_inv_cancel₀ hdt,one_smul,step_apply]
    abel
  constructor
  · intro hh
    apply smul_right_injective X hdt
    change dt • (dt⁻¹ • (x-y)+L x) = dt • f
    rw [he,hh]
    abel
  · intro hh
    have h := congrArg (fun v : X => dt • v) hh
    rw [he] at h
    exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

def ForwardEquation (dt : ℝ) (L : Fin N → X →L[ℝ] X) (B : U →L[ℝ] X)
    (u : Fin N → U) (y : Fin (N+1) → X) : Prop :=
  ∀ i, dt⁻¹ • (y i.succ-y i.castSucc)+L i (y i.succ) = B (u i)

def AdjointEquation [CompleteSpace X] (dt : ℝ) (L : Fin N → X →L[ℝ] X)
    (p : Fin (N+1) → X) : Prop :=
  ∀ i, dt⁻¹ • (p i.castSucc-p i.succ)+(L i).adjoint (p i.castSucc) = 0

theorem forward_equation_iff {dt : ℝ} (hdt : dt ≠ 0) (L : Fin N → X →L[ℝ] X)
    (B : U →L[ℝ] X) (u : Fin N → U) (y : Fin (N+1) → X) :
    ForwardEquation dt L B u y ↔ Forward dt (fun i => (L i).toLinearMap) (fun i => B (u i)) y := by
  exact forall_congr' fun i => (step_equation_iff hdt (L i).toLinearMap (y i.succ) (y i.castSucc) (B (u i))).symm

theorem adjoint_equation_iff [CompleteSpace X] {dt : ℝ} (hdt : dt ≠ 0)
    (L : Fin N → X →L[ℝ] X) (hL : ∀ i, (L i).IsSymmetric) (p : Fin (N+1) → X) :
    AdjointEquation dt L p ↔ Adjoint dt (fun i => (L i).toLinearMap) p := by
  unfold AdjointEquation Adjoint
  apply forall_congr'
  intro i
  rw [(hL i).clm_adjoint_eq]
  simpa only [smul_zero,add_zero,ContinuousLinearMap.coe_coe] using
    (step_equation_iff hdt (L i).toLinearMap (p i.castSucc) (p i.succ) 0).symm

end Carleman.Physical
