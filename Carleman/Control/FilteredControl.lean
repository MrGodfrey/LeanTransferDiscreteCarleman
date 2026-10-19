module

public import Carleman.Control.FilteredObservation
public import Carleman.Control.PhysicalComplementaryHUM

/-! Filtering acts only on the terminal datum; the constructed control solves the unchanged full equation. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace Carleman.Physical
variable {X U : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

theorem filtered_control_of_relaxed (g : TimeGrid) (M θ d S C0 : ℝ)
    (hM : 0 ≤ M) (hsmall : g.dt*M ≤ 1/2) (hC : 1 ≤ C0)
    (A : X →L[ℝ] X) (hAs : A.IsSymmetric) (hA : ∀ x, 0 ≤ inner ℝ (A x) x)
    (V : Fin g.steps → X →L[ℝ] X) (hVs : ∀ i, (V i).IsSymmetric) (hV : ∀ i, ‖V i‖ ≤ M)
    (B : U →L[ℝ] X)
    (hobs : ∀ p : Fin (g.steps+1) → X, AdjointEquation g.dt (fun i => A+V i) p →
      ‖p 0‖^2 ≤ C0*((g.dt*∑ i : Fin g.steps, ‖B.adjoint (p i.castSucc)‖^2)+
        Real.exp (-2*d*S)*‖p (Fin.last g.steps)‖^2))
    (F : Submodule ℝ X) (hΛ : g.period*filterRayleigh A F ≤ θ*d*S)
    (hgap : M*g.period+M^2*g.period^2/2+Real.log (4*C0)/2 ≤ (1-θ)*d*S) (y0 : X) :
    ∃ u : Fin g.steps → U, ∃ y : Fin (g.steps+1) → X,
      y 0 = y0 ∧ ForwardEquation g.dt (fun i => A+V i) B u y ∧
      controlNorm g.dt u ≤ Real.sqrt (2*C0)*‖y0‖ ∧ F.starProjection (y (Fin.last g.steps)) = 0 ∧
      ‖y (Fin.last g.steps)‖ ≤
        complementaryPenalty (Real.exp (-d*S)) (Real.exp (2*M*g.period))
          (filterConstant g.period M (filterRayleigh A F))*Real.sqrt (2*C0)*‖y0‖ := by
  let L := fun i => A+V i
  have hs (i : Fin g.steps) : (L i).IsSymmetric := hAs.add (hVs i)
  have hl (i : Fin g.steps) (x : X) : -M*‖x‖^2 ≤ inner ℝ (L i x) x :=
    stiffness_potential_lower A.toLinearMap (V i).toLinearMap M hA
      (fun z => ((V i).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hV i) (norm_nonneg z))) x
  let R := initialMap g.dt M g.dt_pos.le hsmall (fun i => (L i).toLinearMap) hl
  let O := observationMap g.dt M g.dt_pos.le hsmall (fun i => (L i).toLinearMap) hl B
  let ε := Real.exp (-d*S)
  let K := filterConstant g.period M (filterRayleigh A F)
  let Lbound := Real.exp (2*M*g.period)
  let η := complementaryPenalty ε Lbound K
  have hRapply (z : X) : R z =
      adjointNode g.dt M g.dt_pos.le hsmall (fun i => (L i).toLinearMap) hl 0 z := rfl
  have he : ε^2 = Real.exp (-2*d*S) := by
    change (Real.exp (-d*S))^2 = _
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have htraj (z : X) : AdjointEquation g.dt L
      (fun n => adjointNode g.dt M g.dt_pos.le hsmall (fun i => (L i).toLinearMap) hl n z) :=
    (adjoint_equation_iff g.dt_pos.ne' L hs _).mpr
      (fun i => adjointNode_step g.dt M g.dt_pos.le hsmall (fun i => (L i).toLinearMap) hl i z)
  have hnorm (z : X) : ‖R z‖ ≤ Lbound*‖z‖ :=
    initialMap_bound g.dt M g.dt_pos.le hsmall (fun i => (L i).toLinearMap) hl hM z
  have hrev (z : X) (hz : z ∈ F) : ‖z‖ ≤ K*‖R z‖ := by
    have hh := filter_reverse g M hM hsmall A hAs hA V hVs hV F _ (htraj z)
      (by simpa only [adjointNode_last,LinearMap.id_apply] using hz)
    simpa only [adjointNode_last,LinearMap.id_apply,← hRapply] using hh
  have ho (z : X) : ‖R z‖^2 ≤ C0*(‖O z‖^2+ε^2*‖z‖^2) := by
    have hh := hobs _ (htraj z)
    dsimp only [O]
    rw [observationMap_norm_sq,he]
    simpa only [adjointNode_last,LinearMap.id_apply,← hRapply] using hh
  have hbudget : 4*C0*ε^2*K^2 ≤ 1 := by
    rw [he]
    exact filter_condition_budget g.period M (filterRayleigh A F) θ d S C0 hC hΛ hgap
  have hc := complementary_observation_of_relaxed R O F ε C0 Lbound K
    (zero_le_one.trans hC) (Real.exp_pos _).le (filterConstant_pos _ _ _).le hnorm hrev ho hbudget
  obtain ⟨v,hv,hproj,hterm⟩ := complementary_hum_control R O F η (2*C0)
    (complementaryPenalty_pos ε Lbound K (Real.exp_pos _)) (by linarith)
    (initialMap_injective g.dt M g.dt_pos.le hsmall (fun i => (L i).toLinearMap) hl) hc y0
  let u : Fin g.steps → U := fun i => (Real.sqrt g.dt)⁻¹ • v i
  have hu : controlVector g.dt u = v := controlVector_unscale g.dt g.dt_pos v
  obtain ⟨y,hy,_⟩ := existsUnique_forward g.dt (fun i => (L i).toLinearMap) M
    g.dt_pos.le hsmall hl y0 (fun i => B (u i))
  have hterminal : y (Fin.last g.steps) = R.adjoint y0+O.adjoint v := by
    rw [terminal_representation g.dt M g.dt_pos.le hsmall (fun i => (L i).toLinearMap) hl B
      hs u y hy.2,hy.1,hu]
  refine ⟨u,y,hy.1,(forward_equation_iff g.dt_pos.ne' L B u y).mpr hy.2,?_,?_,?_⟩
  · rw [← controlVector_norm g.dt g.dt_pos.le,hu]
    exact hv
  · rw [hterminal]
    exact hproj
  · rw [hterminal]
    exact hterm

end Carleman.Physical
