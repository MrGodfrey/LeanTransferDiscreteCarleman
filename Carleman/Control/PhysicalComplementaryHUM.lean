module

public import Carleman.Control.ComplementaryObservation
public import Carleman.Control.PhysicalHUM

/-! Complementary HUM produces an actual control for the full physical time scheme. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U] {N : ℕ}

theorem physical_complementary_hum_control (dt M : ℝ) (hpos : 0 < dt) (hsmall : dt*M ≤ 1/2)
    (L : Fin N → X →ₗ[ℝ] X) (hL : ∀ i x, -M*‖x‖^2 ≤ inner ℝ (L i x) x)
    (B : U →L[ℝ] X) (hSym : ∀ i, (L i).IsSymmetric)
    (F : Submodule ℝ X) (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C)
    (hobs : ∀ p : Fin (N+1) → X, Adjoint dt L p →
      ‖p 0‖^2 ≤ C*(dt*(∑ i : Fin N, ‖B.adjoint (p i.castSucc)‖^2)+
        η^2*‖Fᗮ.starProjection (p (Fin.last N))‖^2)) (y0 : X) :
    ∃ u : Fin N → U, ∃ y : Fin (N+1) → X,
      y 0 = y0 ∧ Forward dt L (fun i => B (u i)) y ∧
      controlNorm dt u ≤ Real.sqrt C*‖y0‖ ∧ F.starProjection (y (Fin.last N)) = 0 ∧
      ‖y (Fin.last N)‖ ≤ η*Real.sqrt C*‖y0‖ := by
  let R := initialMap dt M hpos.le hsmall L hL
  let O := observationMap dt M hpos.le hsmall L hL B
  have ho (z : X) : ‖R z‖^2 ≤ C*(‖O z‖^2+η^2*‖Fᗮ.starProjection z‖^2) := by
    have hh := hobs (fun n => adjointNode dt M hpos.le hsmall L hL n z)
      (fun i => adjointNode_step dt M hpos.le hsmall L hL i z)
    dsimp only [R,O]
    rw [observationMap_norm_sq]
    change ‖adjointNode dt M hpos.le hsmall L hL 0 z‖^2 ≤ _
    simpa only [adjointNode_last,LinearMap.id_apply] using hh
  obtain ⟨v,hv,hproj,hterm⟩ := complementary_hum_control R O F η C hη hC
    (initialMap_injective dt M hpos.le hsmall L hL) ho y0
  let u : Fin N → U := fun i => (Real.sqrt dt)⁻¹ • v i
  have hu : controlVector dt u = v := controlVector_unscale dt hpos v
  obtain ⟨y,hy,_⟩ := existsUnique_forward dt L M hpos.le hsmall hL y0 (fun i => B (u i))
  have hterminal : y (Fin.last N) = R.adjoint y0+O.adjoint v := by
    rw [terminal_representation dt M hpos.le hsmall L hL B hSym u y hy.2,hy.1,hu]
  refine ⟨u,y,hy.1,hy.2,?_,?_,?_⟩
  · rw [← controlVector_norm dt hpos.le,hu]
    exact hv
  · rw [hterminal]
    exact hproj
  · rw [hterminal]
    exact hterm

end Carleman.Physical
