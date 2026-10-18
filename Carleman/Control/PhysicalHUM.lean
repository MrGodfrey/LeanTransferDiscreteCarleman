module

public import Carleman.Control.PenalizedHUM

/-! The actual physical control obtained from relaxed observation.
The observation estimate is an explicit hypothesis: this conditional bridge
does not yet establish the original Theorem 7.2 or unconditional Theorem 7.3. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] {N : ℕ}

def controlVector (dt : ℝ) (u : Fin N → U) : PiLp 2 (fun _ : Fin N => U) :=
  WithLp.toLp 2 (fun i => Real.sqrt dt • u i)

theorem controlVector_norm (dt : ℝ) (hdt : 0 ≤ dt) (u : Fin N → U) :
    ‖controlVector dt u‖ = controlNorm dt u := by
  have he : ‖controlVector dt u‖^2 = dt*∑ i, ‖u i‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ i : Fin N, ‖Real.sqrt dt • u i‖^2) = _
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg dt),mul_pow,Real.sq_sqrt hdt]
    exact (Finset.mul_sum ..).symm
  rw [controlNorm,← he,Real.sqrt_sq (norm_nonneg _)]

theorem controlVector_unscale (dt : ℝ) (hdt : 0 < dt) (v : PiLp 2 (fun _ : Fin N => U)) :
    controlVector dt (fun i => (Real.sqrt dt)⁻¹ • v i) = v := by
  ext i
  change Real.sqrt dt • ((Real.sqrt dt)⁻¹ • v i) = v i
  rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hdt)),one_smul]

variable [CompleteSpace U] (dt M : ℝ) (hdt : 0 ≤ dt) (hsmall : dt*M ≤ 1/2)
  (L : Fin N → X →ₗ[ℝ] X) (hL : ∀ i x, -M*‖x‖^2 ≤ inner ℝ (L i x) x)
  (B : U →L[ℝ] X)

theorem control_observation_pairing (u : Fin N → U) (z : X) :
    inner ℝ (controlVector dt u) (observationMap dt M hdt hsmall L hL B z) =
      dt*∑ i, inner ℝ (u i) (B.adjoint (adjointNode dt M hdt hsmall L hL i.castSucc z)) := by
  rw [PiLp.inner_apply]
  change (∑ i : Fin N, inner ℝ (Real.sqrt dt • u i)
    (Real.sqrt dt • B.adjoint (adjointNode dt M hdt hsmall L hL i.castSucc z))) = _
  simp only [real_inner_smul_left,real_inner_smul_right,← mul_assoc,← pow_two,Real.sq_sqrt hdt]
  exact (Finset.mul_sum ..).symm

theorem terminal_representation (hSym : ∀ i, (L i).IsSymmetric)
    (u : Fin N → U) (y : Fin (N+1) → X) (hy : Forward dt L (fun i => B (u i)) y) :
    y (Fin.last N) = (initialMap dt M hdt hsmall L hL).adjoint (y 0)+
      (observationMap dt M hdt hsmall L hL B).adjoint (controlVector dt u) := by
  apply ext_inner_right ℝ
  intro z
  have hh := control_duality dt L hSym B u y
    (fun n => adjointNode dt M hdt hsmall L hL n z) hy
    (fun i => adjointNode_step dt M hdt hsmall L hL i z)
  rw [adjointNode_last,LinearMap.id_apply] at hh
  rw [inner_add_left,ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,
    control_observation_pairing]
  change inner ℝ (y (Fin.last N)) z = inner ℝ (y 0)
    (adjointNode dt M hdt hsmall L hL 0 z)+_
  linarith only [hh]

include M hdt hsmall hL in
theorem physical_hum_control (hpos : 0 < dt) (hSym : ∀ i, (L i).IsSymmetric)
    (ε C : ℝ) (hε : 0 < ε) (hC : 0 ≤ C)
    (hobs : ∀ p : Fin (N+1) → X, Adjoint dt L p →
      ‖p 0‖^2 ≤ C*(dt*(∑ i : Fin N, ‖B.adjoint (p i.castSucc)‖^2)+ε^2*‖p (Fin.last N)‖^2))
    (y0 : X) :
    ∃ u : Fin N → U, ∃ y : Fin (N+1) → X,
      y 0 = y0 ∧ Forward dt L (fun i => B (u i)) y ∧
      controlNorm dt u ≤ Real.sqrt C*‖y0‖ ∧ ‖y (Fin.last N)‖ ≤ ε*Real.sqrt C*‖y0‖ := by
  let R := initialMap dt M hdt hsmall L hL
  let O := observationMap dt M hdt hsmall L hL B
  have ho (z : X) : ‖R z‖^2 ≤ C*(‖O z‖^2+ε^2*‖z‖^2) := by
    have hh := hobs (fun n => adjointNode dt M hdt hsmall L hL n z)
      (fun i => adjointNode_step dt M hdt hsmall L hL i z)
    dsimp only [R,O]
    rw [observationMap_norm_sq]
    change ‖adjointNode dt M hdt hsmall L hL 0 z‖^2 ≤ _
    simpa only [adjointNode_last,LinearMap.id_apply] using hh
  obtain ⟨v,hv,hterm⟩ := penalized_hum_control R O ε C hε hC ho y0
  let u : Fin N → U := fun i => (Real.sqrt dt)⁻¹ • v i
  have hu : controlVector dt u = v := controlVector_unscale dt hpos v
  obtain ⟨y,hy,_⟩ := existsUnique_forward dt L M hdt hsmall hL y0 (fun i => B (u i))
  refine ⟨u,y,hy.1,hy.2,?_,?_⟩
  · rw [← controlVector_norm dt hdt,hu]
    exact hv
  · rw [terminal_representation dt M hdt hsmall L hL B hSym u y hy.2,hy.1,hu]
    exact hterm

end Carleman.Physical
