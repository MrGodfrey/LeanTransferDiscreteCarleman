module

public import Carleman.Control.PhysicalLemma
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual terminal-to-initial and terminal-to-observation maps of the
physical adjoint scheme. Auxiliary foundations for the HUM construction. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  {N : ℕ} (dt M : ℝ) (hdt : 0 ≤ dt) (hsmall : dt*M ≤ 1/2)
  (L : Fin N → X →ₗ[ℝ] X) (hL : ∀ i x, -M*‖x‖^2 ≤ inner ℝ (L i x) x)

def physicalStepEquiv (i : Fin N) : X ≃ₗ[ℝ] X :=
  LinearEquiv.ofBijective (step dt (L i)) (step_bijective dt M hdt hsmall (L i) (hL i))

def adjointNode (n : Fin (N+1)) : X →ₗ[ℝ] X :=
  Fin.reverseInduction LinearMap.id
    (fun i f => (physicalStepEquiv dt M hdt hsmall L hL i).symm.toLinearMap.comp f) n

theorem adjointNode_last : adjointNode dt M hdt hsmall L hL (Fin.last N) = LinearMap.id :=
  Fin.reverseInduction_last

theorem adjointNode_step (i : Fin N) (x : X) :
    step dt (L i) (adjointNode dt M hdt hsmall L hL i.castSucc x) =
      adjointNode dt M hdt hsmall L hL i.succ x := by
  change physicalStepEquiv dt M hdt hsmall L hL i
    (adjointNode dt M hdt hsmall L hL i.castSucc x) = _
  simp only [adjointNode,Fin.reverseInduction_castSucc,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem adjointNode_injective (n : Fin (N+1)) :
    Function.Injective (adjointNode dt M hdt hsmall L hL n) := by
  induction n using Fin.reverseInduction with
  | last => rw [adjointNode_last]; exact Function.injective_id
  | cast i ih =>
    rw [adjointNode,Fin.reverseInduction_castSucc]
    exact (physicalStepEquiv dt M hdt hsmall L hL i).symm.injective.comp ih

def initialMap : X →L[ℝ] X := (adjointNode dt M hdt hsmall L hL 0).toContinuousLinearMap

theorem initialMap_injective : Function.Injective (initialMap dt M hdt hsmall L hL) :=
  adjointNode_injective dt M hdt hsmall L hL 0

theorem initialMap_bound (hM : 0 ≤ M) (x : X) :
    ‖initialMap dt M hdt hsmall L hL x‖ ≤ Real.exp (2*M*((N:ℝ)*dt))*‖x‖ := by
  have hp : Adjoint dt L (fun n => adjointNode dt M hdt hsmall L hL n x) :=
    fun i => adjointNode_step dt M hdt hsmall L hL i x
  have hh := adjoint_energy dt M hdt hM hsmall L hL
    (fun n => adjointNode dt M hdt hsmall L hL n x) hp 0 (Fin.last N) (Fin.zero_le _)
  change ‖adjointNode dt M hdt hsmall L hL 0 x‖ ≤ _
  simpa only [Fin.val_last,Fin.val_zero,Nat.cast_zero,zero_mul,sub_zero,adjointNode_last,LinearMap.id_apply] using hh

variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (B : U →L[ℝ] X)

def observationLinear : X →ₗ[ℝ] PiLp 2 (fun _ : Fin N => U) where
  toFun x := WithLp.toLp 2 (fun i => Real.sqrt dt • B.adjoint (adjointNode dt M hdt hsmall L hL i.castSucc x))
  map_add' x y := by
    ext i
    simp only [PiLp.add_apply,map_add,smul_add]
  map_smul' c x := by
    ext i
    simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]
    exact smul_comm _ _ _

def observationMap : X →L[ℝ] PiLp 2 (fun _ : Fin N => U) :=
  (observationLinear dt M hdt hsmall L hL B).toContinuousLinearMap

theorem observationMap_norm_sq (x : X) :
    ‖observationMap dt M hdt hsmall L hL B x‖^2 =
      dt*∑ i : Fin N, ‖B.adjoint (adjointNode dt M hdt hsmall L hL i.castSucc x)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : Fin N, ‖Real.sqrt dt • B.adjoint (adjointNode dt M hdt hsmall L hL i.castSucc x)‖^2) = _
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg dt),mul_pow,Real.sq_sqrt hdt]
  exact (Finset.mul_sum ..).symm

end Carleman.Physical
