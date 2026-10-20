module

public import Carleman.Control.FiniteHalfspaceP1PhysicalControl
public import Carleman.Control.PhysicalRefinement
public import Carleman.Control.P1WeakControlLimit
public import Carleman.Control.RegionalWeakControlLimit

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 12000000
open MeasureTheory Set Filter
open scoped Topology
namespace Carleman.Physical
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

def FiniteHalfspaceP1Refinement {κidx : Type*} [Fintype κidx]
    (L : κidx → SpatialCoordinates (d+1) →L[ℝ] ℝ) (offset : κidx → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, offset i<L i x})
    (ω : Set (SpatialCoordinates (d+1))) (shape cmesh Bmesh γ : ℝ) : Prop :=
    let S := {x | ∀ i, offset i<L i x}
    letI : IsFiniteMeasure (volume.restrict S) :=
      ⟨by simpa using hbounded.measure_lt_top (μ := volume)⟩
    ∃ κ d0 : ℝ, 0 < κ ∧ 0 < d0 ∧ ∀ T M : ℝ, 0 < T → 0 ≤ M →
      ∃ C : ℝ, 0 < C ∧
      ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (mesh : ∀ n, SimplicialPartition S (ι n)),
        (∀ n, (mesh n).FaceMatching) → (∀ n, (mesh n).BoundaryFitted) →
      ∀ (centers : ∀ n, ι n → SpatialCoordinates (d+1)) (r ℓ : ∀ n, ι n → ℝ),
        (∀ n i, 0 < r n i) → (∀ n i, Metric.ball (centers n i) (r n i) ⊆ (mesh n).cell i) →
        (∀ n i, (mesh n).cellDiameter i ≤ shape*r n i) → (∀ n i, 0 < ℓ n i) →
        (∀ n i, cmesh*(mesh n).cellDiameter i ≤ ℓ n i) →
        (∀ n i, ℓ n i ≤ Bmesh*(mesh n).cellDiameter i) →
        (∀ n i j, (mesh n).VertexNeighbors i j → ℓ n j ≤ γ*ℓ n i) →
        Tendsto (fun n => (mesh n).maxDiameter) atTop (𝓝 0) →
      ∀ (g : ℕ → TimeGrid) (hT : ∀ n, (g n).period=T),
        Tendsto (fun n => (g n).dt) atTop (𝓝 0) →
      ∀ b : BoundedMultiplier ((volume.restrict (Ioc 0 T)).prod (volume.restrict S)),
        b.bound ≤ M → ∀ y0 : Lp ℝ 2 (volume.restrict S),
      let X := fun n => (mesh n).conformingSpace (dirichletSubspace S);
      let hX := fun n => (mesh n).conformingSpace_le (dirichletSubspace S);
      let bg := fun n => fixedTimeCellPotential T (g n) (hT n) b;
      ∃ J : ℕ,
      ∃ u : ∀ n, Fin (g (n+J)).steps → Lp ℝ 2 ((volume.restrict S).restrict ω),
      ∃ y : ∀ n, Fin ((g (n+J)).steps+1) → X (n+J),
        (∀ n, (g (n+J)).dt*M ≤ 1/2) ∧
        (∀ n, y n 0=(X (n+J)).orthogonalProjectionOnto y0 ∧
          ForwardEquation (g (n+J)).dt
            (fun i => galerkinStiffness (boundedDirichletOriginalForm (finite_halfspace_isOpen L offset) (Nat.zero_lt_succ d) hbounded) (X (n+J)) (hX (n+J))+
              conformingPotential (X (n+J)) (bg (n+J) i))
            (conformingRegionControl (X (n+J)) ω) (u n) (y n) ∧
          controlNorm (g (n+J)).dt (u n) ≤ Real.sqrt C*‖(X (n+J)).orthogonalProjectionOnto y0‖ ∧
          ‖y n (Fin.last (g (n+J)).steps)‖ ≤
            Real.sqrt C*Real.exp (-d0*physicalMeshScale κ (mesh (n+J)).maxDiameter (g (n+J)).dt)*
              ‖(X (n+J)).orthogonalProjectionOnto y0‖ ∧
          ‖fixedTimeCellReconstruction T (g (n+J)) (hT (n+J))
            (fun i => (restrictRegionCLM (ν := volume.restrict S) ω).adjoint (u n i))‖ ≤ Real.sqrt C*‖y0‖ ∧
          (∀ᵐ t ∂volume.restrict (Ioc 0 T), fixedTimeCellReconstruction T (g (n+J)) (hT (n+J))
            (fun i => (restrictRegionCLM (ν := volume.restrict S) ω).adjoint (u n i)) t ∈ supportedRegionSpace ω)) ∧
        Tendsto (fun n => (y n 0 : Lp ℝ 2 (volume.restrict S))) atTop (𝓝 y0) ∧
        Tendsto (fun n => ‖y n (Fin.last (g (n+J)).steps)‖) atTop (𝓝 0) ∧
        Tendsto (fun n => (y n (Fin.last (g (n+J)).steps) : Lp ℝ 2 (volume.restrict S))) atTop (𝓝 0)

theorem finite_halfspace_p1_controls_independent_refinement {κidx : Type*} [Fintype κidx] (hdim : d+1 ≤ 3)
    (L : κidx → SpatialCoordinates (d+1) →L[ℝ] ℝ) (offset : κidx → ℝ)
    (hbounded : Bornology.IsBounded {x | ∀ i, offset i<L i x})
    {ω : Set (SpatialCoordinates (d+1))} (hω : IsOpen ω) (hne : ω.Nonempty)
    (hωS : ω ⊆ {x | ∀ i, offset i<L i x})
    (shape cmesh Bmesh γ : ℝ) (hshape : 0 < shape) (hcmesh : 0 < cmesh) (hBmesh : 0 < Bmesh)
    (hγ : 1 ≤ γ) (hΓ : γ < p1GradingLimit (d+1)) :
    FiniteHalfspaceP1Refinement L offset hbounded ω shape cmesh Bmesh γ := by
  unfold FiniteHalfspaceP1Refinement
  intro S
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa using hbounded.measure_lt_top (μ := volume)⟩
  let a := boundedDirichletOriginalForm (finite_halfspace_isOpen L offset) (Nat.zero_lt_succ d)
    hbounded
  obtain ⟨qc,κ,h0,Δ0,Cb,d0,hqc,hκ,hh0,hh01,hΔ0,hΔ01,hCb,hd0,hcontrol⟩ :=
    finite_halfspace_p1_physical_observation_control hdim L offset hbounded hω hne hωS shape cmesh Bmesh γ
      hshape hcmesh hBmesh hγ hΓ
  refine ⟨κ,d0,hκ,hd0,?_⟩
  intro T M hTpos hM
  obtain ⟨C,hC,hdata⟩ := hcontrol T M hTpos hM
  refine ⟨C,hC,?_⟩
  intro ι _ mesh hmesh hboundary centers r ℓ hr hball hsh hℓ hlow hupp hg hlim g hT htlim b hb y0 X hX bg
  have hqb : 0 < physicalBaseAmplitude Cb qc T M := by
    have hx := (physicalBaseAmplitude_bounds Cb qc T M hCb.le (by linarith) hTpos hM).1
    exact (mul_pos hCb (by linarith)).trans_le hx
  have hdiam n : 0 < (mesh n).maxDiameter :=
    (mesh n).maxDiameter_pos (Nat.zero_lt_succ d) (hne.mono hωS)
  have hevent := physical_conditions_eventually (M := M) hκ hh0 hΔ0 hqb hTpos
    (fun n => (mesh n).maxDiameter) (fun n => (g n).dt) hdiam (fun n => (g n).dt_pos) hlim htlim
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hevent
  have hgood n := hJ (n+J) (Nat.le_add_left J n)
  have hex n := (hdata (ι (n+J)) (mesh (n+J)) (hmesh (n+J)) (hboundary (n+J))
    (centers (n+J)) (r (n+J)) (ℓ (n+J)) (hr (n+J)) (hball (n+J)) (hsh (n+J))
    (hℓ (n+J)) (hlow (n+J)) (hupp (n+J)) (hg (n+J)) (hgood n).1
    (g (n+J)) (hT (n+J)) (hgood n).2.1 (hgood n).2.2.1 (hgood n).2.2.2.1
    (hgood n).2.2.2.2.1 (hgood n).2.2.2.2.2 (bg (n+J))
    (fun i => by simpa only [bg,fixedTimeCellPotential_bound] using hb)).2
    ((X (n+J)).orthogonalProjectionOnto y0)
  choose u y hy0 hy hu hyT using hex
  have havg n : ‖(X (n+J)).orthogonalProjectionOnto y0‖ ≤ ‖y0‖ :=
    (X (n+J)).norm_orthogonalProjectionOnto_apply_le y0
  have hterminal : Tendsto (fun n => ‖y n (Fin.last (g (n+J)).steps)‖) atTop (𝓝 0) := by
    apply physical_terminal_norm_tendsto_zero hκ hd0
      (fun n => (mesh (n+J)).maxDiameter) (fun n => (g (n+J)).dt)
      (fun n => hdiam (n+J)) (fun n => (g (n+J)).dt_pos)
      (hlim.comp (tendsto_add_atTop_nat J)) (htlim.comp (tendsto_add_atTop_nat J))
      (fun n => y n (Fin.last (g (n+J)).steps))
    intro n
    exact (hyT n).trans (mul_le_mul_of_nonneg_left (havg n) (by positivity))
  refine ⟨J,u,y,(fun n => (hgood n).2.2.2.2.1),?_,?_,hterminal,?_⟩
  · intro n
    refine ⟨hy0 n,hy n,hu n,hyT n,?_,?_⟩
    · rw [regional_time_control_norm T (g (n+J)) (hT (n+J)) ω hω.measurableSet]
      exact (hu n).trans (mul_le_mul_of_nonneg_left (havg n) (Real.sqrt_nonneg C))
    · exact regional_time_control_supported T (g (n+J)) (hT (n+J)) ω hω.measurableSet (u n)
  · simp only [hy0]
    exact (full_p1_initial_projection_strong_convergence (finite_halfspace_isOpen L offset)
      (finite_halfspace_convex L offset) mesh hmesh hboundary hlim y0).comp (tendsto_add_atTop_nat J)
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr hterminal


end Carleman.Physical
